section \<open> Design Parallel-by-Merge \<close>

theory utp_des_parallel
  imports utp_des_healths
begin

text \<open> A design merge relates the initial state and the two branch results to a final state.
  The laws below give conditions under which parallel composition preserves design healthiness. \<close>

type_synonym 's des_merge = "'s des_vars_ext merge"

subsection \<open> Merge Healthiness Conditions \<close>

text \<open> The merge conditions below are sufficient to preserve $H1$ and $H2$ under parallel-by-merge.\<close>

definition H1m :: "'s des_merge \<Rightarrow> 's des_merge" where
[pred]: "H1m M = (M \<or> (\<not> $<:ok\<^sup><)\<^sub>e)"

text \<open> $H2m$ applies $H2$ to the merge result by composing the merge with @{const J}. \<close>

definition H2m :: "'s des_merge \<Rightarrow> 's des_merge" where
[pred]: "H2m M = M ;; J"

(* Design merge healthiness: H1m and H2m. *)
definition HDM :: "'s des_merge \<Rightarrow> 's des_merge" where
[pred]: "HDM = H1m \<circ> H2m"

subsection \<open> Healthiness Algebra \<close>

lemma H1m_idem: "H1m(H1m M) = H1m M"
  by pred_auto

lemma H2m_idem: "H2m(H2m M) = H2m M"
  by (simp add: H2m_def seqr_assoc J_idem)

lemma H1m_H2m_commute:
  "(H1m \<circ> H2m) M = (H2m \<circ> H1m) M"
  by (simp add: comp_def; pred_auto)

lemmas H1m_H2m_commute' = H1m_H2m_commute[simplified comp_apply]

lemma HDM_idem: "HDM(HDM M) = HDM M"
  by (simp add: HDM_def H1m_H2m_commute' H1m_idem H2m_idem)

lemma H1m_Idempotent [closure]: "Idempotent H1m"
  by (simp add: Idempotent_def H1m_idem)

lemma H2m_Idempotent [closure]: "Idempotent H2m"
  by (simp add: Idempotent_def H2m_idem)

lemma HDM_Idempotent [closure]: "Idempotent HDM"
  by (simp add: Idempotent_def HDM_idem)

lemma H1m_mono: "M \<sqsubseteq> N \<Longrightarrow> H1m M \<sqsubseteq> H1m N"
  by pred_auto

lemma H2m_mono: "M \<sqsubseteq> N \<Longrightarrow> H2m M \<sqsubseteq> H2m N"
  by (simp add: H2m_def seqr_mono)

lemma HDM_mono: "M \<sqsubseteq> N \<Longrightarrow> HDM M \<sqsubseteq> HDM N"
  by (simp add: HDM_def H1m_mono H2m_mono)

lemma H1m_Monotonic [closure]: "Monotonic H1m"
  by (rule MonotonicI, rule H1m_mono)

lemma H2m_Monotonic [closure]: "Monotonic H2m"
  by (rule MonotonicI, rule H2m_mono)

lemma HDM_Monotonic [closure]: "Monotonic HDM"
  by (rule MonotonicI, rule HDM_mono)

lemma HDM_fixed_iff:
  "M is HDM \<longleftrightarrow> (M is H1m) \<and> (M is H2m)"
  using H1m_idem[of "H2m M"] H1m_H2m_commute'[of "H2m M"]
  by (auto simp add: Healthy_def' HDM_def H2m_idem)

lemma HDM_healths [closure]:
  assumes "M is HDM"
  shows "M is H1m" "M is H2m"
  using assms by (simp_all add: HDM_fixed_iff)

lemma HDM_intro:
  assumes "M is H1m" "M is H2m"
  shows "M is HDM"
  by (simp add: HDM_fixed_iff assms)

subsection \<open> Sequential Composition Closure \<close>

lemma H1m_seq [closure]:
  assumes "M is H1m" "P is H1"
  shows "M ;; P is H1m"
  using assms by (pred_simp; blast)

text \<open> For $H2m$, only the continuation needs to be $H2$-healthy. \<close>

lemma H2m_seq [closure]:
  assumes "P is H2"
  shows "M ;; P is H2m"
  using assms by (simp add: Healthy_def' H2m_def H2_def seqr_assoc)

lemma HDM_seq [closure]:
  assumes "M is HDM" "P is \<^bold>H"
  shows "M ;; P is HDM"
  by (rule HDM_intro;
      simp add: assms closure H_implies_H1 H_implies_H2)

subsection \<open> Parallel Composition Closure \<close>

lemma des_par_by_merge_unfold:
  fixes P Q :: "'s des_hrel" and M :: "'s des_merge"
  shows "(P \<parallel>\<^bsub>M\<^esub> Q) (s0, out) \<longleftrightarrow>
    (\<exists>p q. P (s0, p) \<and> Q (s0, q) \<and> merge_eval M s0 p q out)"
  by (cases s0; cases out;
      simp add: par_by_merge_def par_sep_def; pred_auto; blast)

lemma H1_par_by_merge [closure]:
  fixes P Q :: "'s des_hrel" and M :: "'s des_merge"
  assumes "P is H1" "Q is H1" "M is H1m"
  shows "(P \<parallel>\<^bsub>M\<^esub> Q) is H1"
  using assms by (pred_simp; auto simp add: all_bool_eq ex_bool_eq)

lemma H2_par_by_merge [closure]:
  fixes P Q :: "'s des_hrel" and M :: "'s des_merge"
  assumes "M is H2m"
  shows "(P \<parallel>\<^bsub>M\<^esub> Q) is H2"
  using assms
  by (simp add: Healthy_def' H2_def H2m_def par_by_merge_def seqr_assoc)

lemma H_par_by_merge [closure]:
  fixes P Q :: "'s des_hrel" and M :: "'s des_merge"
  assumes "P is \<^bold>H" "Q is \<^bold>H" "M is HDM"
  shows "(P \<parallel>\<^bsub>M\<^esub> Q) is \<^bold>H"
  by (rule Healthy_intro;
      simp add: Healthy_if H1_par_by_merge H2_par_by_merge
        H_implies_H1 HDM_healths assms)

subsection \<open> Disjunction and Conjunction \<close>

lemma H1m_disj: "H1m(M \<or> N) = (H1m M \<or> H1m N)"
  by pred_auto

lemma H1m_conj: "H1m(M \<and> N) = (H1m M \<and> H1m N)"
  by pred_auto

lemma H2m_disj: "H2m(M \<or> N) = (H2m M \<or> H2m N)"
  by (simp add: H2m_def seqr_or_distl)

lemma HDM_disj: "HDM(M \<or> N) = (HDM M \<or> HDM N)"
  by (simp add: HDM_def H1m_disj H2m_disj)

text \<open> $H2m$ and $HDM$ do not distribute over arbitrary conjunctions. Closing each conjunct
  separately can use a different intermediate value of $ok'$. The conjunction of two healthy
  merges is still healthy. \<close>

lemma H2m_conj:
  assumes "M is H2m" "N is H2m"
  shows "H2m(M \<and> N) = (H2m M \<and> H2m N)"
proof -
  have "H2m(H2m M \<and> H2m N) = (H2m M \<and> H2m N)"
    by (simp add: H2m_def J_split usubst; pred_auto)
  then show ?thesis
    by (simp only: Healthy_if[OF assms(1)] Healthy_if[OF assms(2)])
qed

lemma HDM_conj:
  assumes "M is H2m" "N is H2m"
  shows "HDM(M \<and> N) = (HDM M \<and> HDM N)"
  by (simp add: HDM_def H2m_conj assms H1m_conj)

lemma H2m_not_conj_distrib:
  "\<not> (\<forall> M N :: 's des_merge. H2m(M \<and> N) = (H2m M \<and> H2m N))"
proof -
  have "H2m(ok\<^sup>> \<and> \<not> ok\<^sup>>) \<noteq>
    (H2m(ok\<^sup>>) \<and> H2m(\<not> ok\<^sup>>) :: 's des_merge)"
    by pred_auto
  then show ?thesis by blast
qed

lemma HDM_not_conj_distrib:
  "\<not> (\<forall> M N :: 's des_merge. HDM(M \<and> N) = (HDM M \<and> HDM N))"
proof -
  have "HDM(ok\<^sup>> \<and> \<not> ok\<^sup>>) \<noteq>
    (HDM(ok\<^sup>>) \<and> HDM(\<not> ok\<^sup>>) :: 's des_merge)"
    by pred_auto
  then show ?thesis by blast
qed

lemma H1m_disj_closed [closure]:
  assumes "M is H1m" "N is H1m"
  shows "(M \<or> N) is H1m"
  by (rule Healthy_intro; simp add: H1m_disj Healthy_if assms)

lemma H1m_conj_closed [closure]:
  assumes "M is H1m" "N is H1m"
  shows "(M \<and> N) is H1m"
  by (rule Healthy_intro; simp add: H1m_conj Healthy_if assms)

lemma H2m_disj_closed [closure]:
  assumes "M is H2m" "N is H2m"
  shows "(M \<or> N) is H2m"
  by (rule Healthy_intro; simp add: H2m_disj Healthy_if assms)

lemma H2m_conj_closed [closure]:
  assumes "M is H2m" "N is H2m"
  shows "(M \<and> N) is H2m"
  by (rule Healthy_intro; simp add: H2m_conj Healthy_if assms)

lemma HDM_disj_closed [closure]:
  assumes "M is HDM" "N is HDM"
  shows "(M \<or> N) is HDM"
  by (rule Healthy_intro; simp add: HDM_disj Healthy_if assms)

lemma HDM_conj_closed [closure]:
  assumes "M is HDM" "N is HDM"
  shows "(M \<and> N) is HDM"
  by (rule HDM_intro; simp add: assms closure)

subsection \<open> Symmetry \<close>

lemma SymMerge_H1m [closure]:
  assumes "M is SymMerge"
  shows "H1m M is SymMerge"
  using assms by (pred_simp; blast)

lemma SymMerge_H2m [closure]:
  assumes "M is SymMerge"
  shows "H2m M is SymMerge"
  using assms by (simp add: Healthy_def' H2m_def seqr_assoc[symmetric])

lemma SymMerge_HDM [closure]:
  assumes "M is SymMerge"
  shows "HDM M is SymMerge"
  by (simp add: HDM_def assms closure)

subsection \<open> State-Merge Lifting \<close>

text \<open> The raw lift applies $j$ to the ordinary state parts of the initial state, both branch
  results, and the final state. It sets $ok' = ok_0 \wedge ok_1$. \<close>

definition merge_des_raw :: "'s merge \<Rightarrow> 's des_merge" ("M\<^sub>D\<^sup>0'(_')") where
"merge_des_raw j = (\<lambda>(m, out).
  des_vars.ok\<^sub>v out =
    (des_vars.ok\<^sub>v (mrg_left\<^sub>v m) \<and> des_vars.ok\<^sub>v (mrg_right\<^sub>v m)) \<and>
  j (\<lparr>mrg_prior\<^sub>v = des_vars.more (mrg_prior\<^sub>v m),
       mrg_left\<^sub>v = des_vars.more (mrg_left\<^sub>v m),
       mrg_right\<^sub>v = des_vars.more (mrg_right\<^sub>v m), \<dots> = ()\<rparr>,
     des_vars.more out))"

text \<open> Applying $HDM$ to the raw lift gives a healthy design merge. \<close>

definition merge_des :: "'s merge \<Rightarrow> 's des_merge" ("M\<^sub>D'(_')") where
"merge_des j = HDM (merge_des_raw j)"

lemma ordinary_merge_obs:
  "merge_eval (merge_des j) \<lparr>ok\<^sub>v = started, \<dots> = s0\<rparr>
    \<lparr>ok\<^sub>v = a, \<dots> = u\<rparr> \<lparr>ok\<^sub>v = b, \<dots> = v\<rparr>
    \<lparr>ok\<^sub>v = c, \<dots> = z\<rparr> \<longleftrightarrow>
    (\<not> started \<or> ((a \<and> b \<longrightarrow> c) \<and> merge_eval j s0 u v z))"
  by (simp add: merge_des_def HDM_def H1m_def H2m_def merge_des_raw_def; pred_auto)

lemma merge_des_is_HDM [closure]: "M\<^sub>D(j) is HDM"
  by (simp add: merge_des_def Healthy_def' HDM_idem)

definition des_par ::
  "'s des_hrel \<Rightarrow> 's merge \<Rightarrow> 's des_hrel \<Rightarrow> 's des_hrel"
  ("_ \<parallel>\<^sub>D\<^bsub>_\<^esub> _" [85,0,86] 85)
where "P \<parallel>\<^sub>D\<^bsub>j\<^esub> Q = P \<parallel>\<^bsub>M\<^sub>D(j)\<^esub> Q"

lemma ordinary_parallel_obs:
  fixes P Q :: "'s des_hrel"
  shows "des_par P j Q (\<lparr>ok\<^sub>v = started, \<dots> = s0\<rparr>, \<lparr>ok\<^sub>v = c, \<dots> = z\<rparr>) \<longleftrightarrow>
   (\<exists>a u b v. P (\<lparr>ok\<^sub>v = started, \<dots> = s0\<rparr>, \<lparr>ok\<^sub>v = a, \<dots> = u\<rparr>) \<and> Q (\<lparr>ok\<^sub>v = started, \<dots> = s0\<rparr>, \<lparr>ok\<^sub>v = b, \<dots> = v\<rparr>) \<and>
    (\<not> started \<or> ((a \<and> b \<longrightarrow> c) \<and> merge_eval j s0 u v z)))"
proof -
  have expand_result:
    "(\<exists>p :: 's des_vars_ext. F p) \<longleftrightarrow>
      (\<exists>b x. F \<lparr>ok\<^sub>v = b, \<dots> = x\<rparr>)" for F
    by pred_auto
  show ?thesis
    by (simp only: des_par_def des_par_by_merge_unfold expand_result ordinary_merge_obs)
qed

lemma des_par_H_closure [closure]:
  assumes "P is \<^bold>H" "Q is \<^bold>H"
  shows "(P \<parallel>\<^sub>D\<^bsub>j\<^esub> Q) is \<^bold>H"
  unfolding des_par_def
  by (rule H_par_by_merge[OF assms merge_des_is_HDM])

lemma des_par_assoc_state:
  fixes P Q R :: "'s des_hrel" and j :: "'s merge"
  assumes assoc: "\<And>s0 a b c z.
    (\<exists>v. merge_eval j s0 a b v \<and> merge_eval j s0 v c z) =
    (\<exists>v. merge_eval j s0 b c v \<and> merge_eval j s0 a v z)"
  shows "des_par (des_par P j Q) j R = des_par P j (des_par Q j R)"
proof -
  have merge_assoc:
    "(\<exists>i y. (\<not>b \<or> ((a \<and> d \<longrightarrow> i) \<and> merge_eval j s0 u v y)) \<and>
       (\<not>b \<or> ((i \<and> e \<longrightarrow> c) \<and> merge_eval j s0 y w z))) =
     (\<exists>i y. (\<not>b \<or> ((d \<and> e \<longrightarrow> i) \<and> merge_eval j s0 v w y)) \<and>
       (\<not>b \<or> ((a \<and> i \<longrightarrow> c) \<and> merge_eval j s0 u y z)))"
    for b a d e c s0 u v w z
    using assoc[of s0 u v w z]
    by (cases b; cases a; cases d; cases e; cases c; simp add: ex_bool_eq)
  show ?thesis
  proof (rule ext)
    fix obs :: "'s des_vars_ext \<times> 's des_vars_ext"
    obtain b s0 c z where obs: "obs = (\<lparr>ok\<^sub>v = b, \<dots> = s0\<rparr>, \<lparr>ok\<^sub>v = c, \<dots> = z\<rparr>)"
      by (cases obs; pred_auto)
    have left:
      "des_par (des_par P j Q) j R (\<lparr>ok\<^sub>v = b, \<dots> = s0\<rparr>, \<lparr>ok\<^sub>v = c, \<dots> = z\<rparr>) =
        (\<exists>a u d v e w. P (\<lparr>ok\<^sub>v = b, \<dots> = s0\<rparr>, \<lparr>ok\<^sub>v = a, \<dots> = u\<rparr>) \<and> Q (\<lparr>ok\<^sub>v = b, \<dots> = s0\<rparr>, \<lparr>ok\<^sub>v = d, \<dots> = v\<rparr>) \<and>
          R (\<lparr>ok\<^sub>v = b, \<dots> = s0\<rparr>, \<lparr>ok\<^sub>v = e, \<dots> = w\<rparr>) \<and> (\<exists>i y.
            (\<not>b \<or> ((a \<and> d \<longrightarrow> i) \<and> merge_eval j s0 u v y)) \<and>
            (\<not>b \<or> ((i \<and> e \<longrightarrow> c) \<and> merge_eval j s0 y w z))))"
      unfolding ordinary_parallel_obs by blast
    have right:
      "des_par P j (des_par Q j R) (\<lparr>ok\<^sub>v = b, \<dots> = s0\<rparr>, \<lparr>ok\<^sub>v = c, \<dots> = z\<rparr>) =
        (\<exists>a u d v e w. P (\<lparr>ok\<^sub>v = b, \<dots> = s0\<rparr>, \<lparr>ok\<^sub>v = a, \<dots> = u\<rparr>) \<and> Q (\<lparr>ok\<^sub>v = b, \<dots> = s0\<rparr>, \<lparr>ok\<^sub>v = d, \<dots> = v\<rparr>) \<and>
          R (\<lparr>ok\<^sub>v = b, \<dots> = s0\<rparr>, \<lparr>ok\<^sub>v = e, \<dots> = w\<rparr>) \<and> (\<exists>i y.
            (\<not>b \<or> ((d \<and> e \<longrightarrow> i) \<and> merge_eval j s0 v w y)) \<and>
            (\<not>b \<or> ((a \<and> i \<longrightarrow> c) \<and> merge_eval j s0 u y z))))"
      unfolding ordinary_parallel_obs by blast
    show "des_par (des_par P j Q) j R obs = des_par P j (des_par Q j R) obs"
      by (simp only: obs left right merge_assoc)
  qed
qed

end
