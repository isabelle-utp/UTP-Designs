section \<open> Design Healthiness Conditions \<close> 

theory utp_des_healths
  imports utp_des_core
          utp_des_laws
begin

subsection \<open> H1: No observation is allowed before initiation \<close>

definition H1 :: "('\<alpha>, '\<beta>) des_rel \<Rightarrow> ('\<alpha>, '\<beta>) des_rel" where
[pred, rel]: "H1(P) = (ok\<^sup>< \<longrightarrow> P)"

expr_constructor H1

lemma H1_idem:
  "H1 (H1 P) = H1(P)"
  by (pred_auto)

lemma H1_monotone:
  "P \<sqsubseteq> Q \<Longrightarrow> H1(P) \<sqsubseteq> H1(Q)"
  by (pred_auto)

lemma H1_Continuous: "Continuous H1"
  by (pred_auto)

lemma H1_below_top:
  "H1(P) \<sqsubseteq> \<top>\<^sub>D"
  by (pred_auto)

lemma H1_design_skip:
  "H1(II) = II\<^sub>D"
  by (pred_auto)

lemma H1_cond: "H1(P \<lhd> b \<rhd> Q) = H1(P) \<lhd> b \<rhd> H1(Q)"
  by (pred_auto)

lemma H1_conj: "H1(P \<and> Q) = (H1(P) \<and> H1(Q))"
  by (pred_auto)

lemma H1_disj: "H1(P \<or> Q) = (H1(P) \<or> H1(Q))"
  by (pred_auto)

lemma design_export_H1: "(P \<turnstile> Q) = (P \<turnstile> H1(Q))"
  by (pred_auto)

text \<open> The H1 algebraic laws are valid only when $\alpha(R)$ is homogeneous. This should maybe be
        generalised. \<close>

theorem H1_algebraic_intro:
  assumes
    "(true\<^sub>h ;; R) = true\<^sub>h"
    "(II\<^sub>D ;; R) = R"
  shows "R is H1"
proof -
  have "R = (II\<^sub>D ;; R)" by (simp add: assms(2))
  also have "... = (H1(II) ;; R)"
    by (simp add: H1_design_skip)
  also have "... = ((ok\<^sup>< \<longrightarrow> II) ;; R)"
    by (simp add: H1_def)
  also have "... = (((\<not> ok\<^sup><) ;; R) \<or> R)"
    by (pred_auto)
  also have "... = ((((\<not> ok\<^sup><) ;; true\<^sub>h) ;; R) \<or> R)"
    by (pred_auto)
  also have "... = (((\<not> (ok\<^sup><)) ;; true\<^sub>h) \<or> R)"
    by (metis assms(1) seqr_assoc)
  also have "... = (ok\<^sup>< \<longrightarrow> R)"
    by (pred_auto)
  finally show ?thesis by (metis H1_def Healthy_def')
qed

lemma nok_not_false:
  "(\<not> ok\<^sup><) \<noteq> false"
  by (pred_auto)

theorem H1_left_zero:
  assumes "P is H1"
  shows "(true ;; P) = true"
proof -
  from assms have "(true ;; P) = true ;; (ok\<^sup>< \<longrightarrow> P)"
    by (simp add: H1_def Healthy_def')
  (* The next step ensures we get the right alphabet for true by copying it *)
  also from assms have "... = (true ;; ((\<not> ok\<^sup><) \<or> P))" (is "_ = (?true ;; _)")
    by (pred_auto; blast)
  also from assms have "... = ((?true ;; (\<not> ok\<^sup><)) \<or> (?true ;; P))"
    by pred_auto
  also from assms have "... = (true \<or> (true ;; P))"
    by pred_auto
  finally show ?thesis
    by pred_auto
qed

theorem H1_left_unit:
  fixes P :: "('\<alpha>, '\<beta>) des_rel"
  assumes "P is H1"
  shows "(II\<^sub>D ;; P) = P"
proof -
  have "(II\<^sub>D ;; P) = ((ok\<^sup>< \<longrightarrow> II) ;; P)"
    by (metis H1_def H1_design_skip)
  also have "... = (((\<not> ok\<^sup><) ;; P) \<or> P)"
    by (pred_auto)
  also from assms have "... = ((((\<not> ok\<^sup><) ;; true\<^sub>h) ;; P) \<or> P)"
    by (pred_auto)
  also have "... = (((\<not> ok\<^sup><) ;; (true\<^sub>h ;; P)) \<or> P)"
    by (simp add: seqr_assoc)
  also from assms have "... = ((ok\<^sup><) \<longrightarrow> P)"
  proof -
    have "((\<not> (ok\<^sup><)) ;; (true\<^sub>h ;; P)) = ((\<not> (ok\<^sup><)) ;; true\<^sub>h)"
      using assms
      by (simp add: H1_left_zero, pred_auto)
    also have "... = (\<not> (ok\<^sup><))"
      by pred_auto
    finally show ?thesis
      by pred_auto
  qed
  finally show ?thesis using assms
    by (simp add: H1_def Healthy_def')
qed

theorem H1_algebraic:
  "P is H1 \<longleftrightarrow> (true\<^sub>h ;; P) = true\<^sub>h \<and> (II\<^sub>D ;; P) = P"
  using H1_algebraic_intro H1_left_unit H1_left_zero by metis

theorem H1_nok_left_zero:
  fixes P :: "'\<alpha> des_hrel"
  assumes "P is H1"
  shows "((\<not> ok\<^sup><) ;; P) = (\<not> ok\<^sup><)"
proof -
  have "((\<not> ok\<^sup><) ;; P) = (((\<not> ok\<^sup><) ;; true\<^sub>h) ;; P)"
    by pred_auto
  also have "... = ((\<not> ok\<^sup><) ;; true\<^sub>h)"
    by (metis H1_left_zero assms seqr_assoc)
  also have "... = (\<not> (ok\<^sup><))"
    by pred_auto
  finally show ?thesis .
qed

lemma H1_design:
  "H1(P \<turnstile> Q) = (P \<turnstile> Q)"
  by (pred_auto)

lemma H1_rdesign:
  "H1(P \<turnstile>\<^sub>r Q) = (P \<turnstile>\<^sub>r Q)"
  by (pred_auto)

lemma H1_choice_closed [closure]:
  "\<lbrakk> P is H1; Q is H1 \<rbrakk> \<Longrightarrow> P \<sqinter> Q is H1"
  by (metis H1_disj Healthy_if Healthy_intro disj_pred_def)

lemma H1_inf_closed [closure]:
  "\<lbrakk> P is H1; Q is H1 \<rbrakk> \<Longrightarrow> P \<squnion> Q is H1"
  by (metis H1_conj Healthy_def' conj_pred_def)

lemma H1_UINF:
  assumes "A \<noteq> {}"
  shows "H1(\<Sqinter> i \<in> A. P(i)) = (\<Sqinter> i \<in> A. H1(P(i)))"
  using assms by (pred_auto)

lemma H1_Sup:
  assumes "A \<noteq> {}" "\<forall> P \<in> A. P is H1"
  shows "(\<Sqinter> A) is H1"
proof -
  from assms(2) have "H1 ` A = A"
    by (auto simp add: Healthy_def rev_image_eqI)
  with H1_UINF[of A id, OF assms(1)] show ?thesis
    by (simp add: Healthy_def)
qed

lemma H1_USUP:
  shows "H1(\<Squnion> i \<in> A. P(i)) = (\<Squnion> i \<in> A. H1(P(i)))"
  by (pred_auto)

lemma H1_Inf [closure]:
  assumes "\<forall> P \<in> A. P is H1"
  shows "(\<Squnion> A) is H1"
proof -
  from assms have "H1 ` A = A"
    by (auto simp add: Healthy_def rev_image_eqI)
  then show ?thesis
    apply (simp add: Healthy_def)
    by (metis H1_USUP image_image)
qed

(*
lemma msubst_H1: "(\<And>x. P x is H1) \<Longrightarrow> P x\<lbrakk>x\<rightarrow>v\<rbrakk> is H1"
  by (rel_auto)
*)

subsection \<open> H2: A specification cannot require non-termination \<close>

definition J :: "'\<alpha> des_hrel" where 
[pred]: "J = ((ok\<^sup>< \<longrightarrow> ok\<^sup>>) \<and> II \<up> more\<^sub>L\<^sup>2)\<^sub>e"

definition H2 where
[pred]: "H2 (P) \<equiv> P ;; J"

expr_constructor H2

lemma J_split:
  shows "(P ;; J) = (P\<^sup>f \<or> (P\<^sup>t \<and> ok\<^sup>>))"
proof -
  have "(P ;; J) = (P ;; ((ok\<^sup>< \<longrightarrow> ok\<^sup>>) \<and> II \<up> more\<^sub>L\<^sup>2))\<^sub>e"
    by (simp add: H2_def J_def design_def, pred_auto)
  also have "... = (P ;; ((ok\<^sup>< \<longrightarrow> (ok\<^sup>< \<and> ok\<^sup>>)) \<and> II \<up> more\<^sub>L\<^sup>2))\<^sub>e"
    by (pred_auto)
  also have "... = ((P ;; (\<not> ok\<^sup>< \<and> II \<up> more\<^sub>L\<^sup>2)) \<or> (P ;; (ok\<^sup>< \<and> (II \<up> more\<^sub>L\<^sup>2 \<and> ok\<^sup>>))))"
    by (pred_auto)
  also have "... = (P\<^sup>f \<or> (P\<^sup>t \<and> ok\<^sup>>))"
  proof -
    have "(P ;; (\<not> ok\<^sup>< \<and> II \<up> more\<^sub>L\<^sup>2)) = P\<^sup>f"
    proof -
      have "(P ;; (\<not> ok\<^sup>< \<and> II \<up> more\<^sub>L\<^sup>2)) = ((P \<and> \<not> ok\<^sup>>) ;; II \<up> more\<^sub>L\<^sup>2)"
        by (pred_auto)
      also have "... = (\<exists>ok\<^sup>> \<Zspot> (P \<and> ok\<^sup>> = False)\<^sub>e)"
        by pred_auto
      also have "... = P\<^sup>f"
        by pred_auto
      finally show ?thesis .
    qed
    moreover have "(P ;; (ok\<^sup>< \<and> (II \<up> more\<^sub>L\<^sup>2 \<and> ok\<^sup>>))) = (P\<^sup>t \<and> ok\<^sup>>)"
    proof -
      have "(P ;; (ok\<^sup>< \<and> (II \<up> more\<^sub>L\<^sup>2 \<and> ok\<^sup>>))) = (P ;; (ok\<^sup>< \<and> II))"
        by (pred_auto)
      also have "... = (P\<^sup>t \<and> ok\<^sup>>)"
        by (pred_auto)
      finally show ?thesis .
    qed
    ultimately show ?thesis
      by simp
  qed
  finally show ?thesis .
qed

lemma H2_split:
  shows "H2(P) = (P\<^sup>f \<or> (P\<^sup>t \<and> ok\<^sup>>))"
  by (simp add: H2_def J_split)

theorem H2_equivalence:
  "P is H2 \<longleftrightarrow> `(P\<^sup>f \<longrightarrow> P\<^sup>t)`"
  by (pred_auto, (metis (full_types))+)

(*
proof -
  have "(P = (P ;; J)) \<longleftrightarrow> (P = (P\<^sup>f \<or> (P\<^sup>t \<and> ok\<^sup>>)))"
    by (simp add: J_split)
  also have "... \<longleftrightarrow> `\<lbrakk>(P \<longleftrightarrow> P\<^sup>f \<or> P\<^sup>t \<and> (ok\<^sup>>)\<^sub>e)\<^sup>f \<and> (P \<longleftrightarrow> P\<^sup>f \<or> P\<^sup>t \<and> (ok\<^sup>>)\<^sub>e)\<rbrakk>\<^sub>P`"
    by rel_auto
  also have "... = `\<lbrakk>(P\<^sup>f \<longleftrightarrow> P\<^sup>f) \<and> (P\<^sup>t \<longleftrightarrow> P\<^sup>f \<or> P\<^sup>t)\<rbrakk>\<^sub>P`"
    apply pred_auto
    by metis+
  also have "... = `\<lbrakk>P\<^sup>t \<longleftrightarrow> (P\<^sup>f \<or> P\<^sup>t)\<rbrakk>\<^sub>P`"
    by (pred_auto)
  also have "... = `P\<^sup>f \<longrightarrow> P\<^sup>t`"
    by (pred_auto)
  finally show ?thesis
    using H2_def Healthy_def'
    by (metis (no_types, lifting) SEXP_def conj_refine_left iff_pred_def pred_ba.boolean_algebra.conj_one_right pred_ba.inf_le2 pred_ba.sup.absorb2 pred_ba.sup.orderE pred_impl_laws(5) pred_set rel_eq_iff taut_def true_false_pred_expr(1))
qed
*)

lemma H2_equiv:
  "P is H2 \<longleftrightarrow> P\<^sup>t \<sqsubseteq> P\<^sup>f"
  by (simp add: H2_equivalence pred_refine_iff, expr_simp)

lemma H2_design:
  assumes "$ok\<^sup>> \<sharp> P" "$ok\<^sup>> \<sharp> Q"
  shows "H2(P \<turnstile> Q) = P \<turnstile> Q"
  using assms
  by (simp add: H2_split design_def usubst unrest, pred_auto)

lemma H2_rdesign:
  "H2(P \<turnstile>\<^sub>r Q) = P \<turnstile>\<^sub>r Q"
  by (simp add: H2_design unrest rdesign_def)

theorem J_idem:
  "(J ;; J) = J"
  by (pred_auto)

theorem H2_idem:
  "H2(H2(P)) = H2(P)"
  by (metis H2_def J_idem seqr_assoc)

(*
theorem H2_Continuous: "Continuous H2"
  by (rel_auto)
*)

theorem H2_not_okay: "H2 (\<not>ok\<^sup><) = (\<not>ok\<^sup><)"
proof -
  have "H2 (\<not>ok\<^sup><) = ((\<not>ok\<^sup><)\<^sup>f \<or> ((\<not>ok\<^sup><)\<^sup>t \<and> ok\<^sup>>))"
    by (simp add: H2_split)
  also have "... = (\<not> ok\<^sup>< \<or> (\<not>ok\<^sup><) \<and> ok\<^sup>>)"
    by (pred_auto)
  also have "... = (\<not> ok\<^sup><)"
    by (pred_auto)
  finally show ?thesis .
qed

lemma H2_true: "H2(true) = true"
  by (pred_auto)

lemma H2_choice_closed [closure]:
  "\<lbrakk> P is H2; Q is H2 \<rbrakk> \<Longrightarrow> P \<sqinter> Q is H2"
  by (metis H2_def Healthy_def' disj_pred_def seqr_or_distl)

lemma H2_inf_closed [closure]:
  assumes "P is H2" "Q is H2"
  shows "P \<squnion> Q is H2"
proof -
  have "P \<squnion> Q = (P\<^sup>f \<or> P\<^sup>t \<and> ok\<^sup>>) \<squnion> (Q\<^sup>f \<or> Q\<^sup>t \<and> ok\<^sup>>)"
    by (metis H2_def Healthy_def J_split assms(1) assms(2))
  moreover have "H2(...) = ..."
    by (simp add: H2_split usubst, pred_auto)
  ultimately show ?thesis
    by (simp add: Healthy_def)
qed

lemma H2_USUP:
  shows "H2(\<Sqinter> i \<in> A. P(i)) = (\<Sqinter> i \<in> A. H2(P(i)))"
  by (pred_auto)

theorem H1_H2_commute:
  "H1 (H2 P) = H2 (H1 P)"
proof -
  have "H2 (H1 P) = ((ok\<^sup>< \<longrightarrow> P) ;; J)"
    by (simp add: H1_def H2_def)
  also have "... = ((\<not> ok\<^sup>< \<or> P) ;; J)"
    by (pred_auto)
  also have "... = (((\<not> ok\<^sup><) ;; J) \<or> (P ;; J))"
    by (pred_auto)
  also have "... =  ((H2 (\<not> ok\<^sup><)) \<or> H2(P))"
    by (simp add: H2_def)
  also have "... =  ((\<not> ok\<^sup><) \<or> H2(P))"
    by (pred_auto)
  also have "... = H1(H2(P))"
    by (pred_auto)
  finally show ?thesis by simp
qed

subsection \<open> Designs as $H1$-$H2$ predicates \<close>


abbreviation H1_H2 :: "('\<alpha>, '\<beta>) des_rel \<Rightarrow> ('\<alpha>, '\<beta>) des_rel" ("\<^bold>H") where
"H1_H2 P \<equiv> H1 (H2 P)"

lemma H1_H2_comp: "\<^bold>H = H1 \<circ> H2"
  by (auto)

theorem H1_H2_eq_design:
  "\<^bold>H(P) = (\<not> P\<^sup>f) \<turnstile> P\<^sup>t"
proof -
  have "\<^bold>H(P) = (ok\<^sup>< \<longrightarrow> H2(P))"
    by (simp add: H1_def)
  also have "... = (ok\<^sup>< \<longrightarrow> (P\<^sup>f \<or> (P\<^sup>t \<and> ok\<^sup>>)))\<^sub>e"
    by (simp add:H2_split, pred_auto)
  also have "... = (ok\<^sup>< \<and> (\<not> P\<^sup>f) \<longrightarrow> ok\<^sup>> \<and> ok\<^sup>< \<and> P\<^sup>t)\<^sub>e"
    by (pred_auto)
  also have "... = (\<not> P\<^sup>f) \<turnstile> P\<^sup>t"
    by (pred_auto)
  finally show ?thesis .
qed

theorem H1_H2_is_design:
  assumes "P is H1" "P is H2"
  shows "P = (\<not> P\<^sup>f) \<turnstile> P\<^sup>t"
  using assms by (metis H1_H2_eq_design Healthy_def)

(*
lemma aext_arestr' [alpha]:
  fixes P :: "'a \<leftrightarrow> 'b"
  assumes "$a \<sharp> P"
  shows "(P \<down> a) \<up> a = P"
  apply rel_auto  
  by (rel_simp, metis assms lens_override_def)
*)

theorem H1_H2_eq_rdesign:
  "\<^bold>H(P) = pre\<^sub>D(P) \<turnstile>\<^sub>r post\<^sub>D(P)"
proof -
  have "\<^bold>H(P) = (ok\<^sup>< \<longrightarrow> H2(P))"
    by (simp add: H1_def Healthy_def')
  also have "... = (ok\<^sup>< \<longrightarrow> (P\<^sup>f \<or> (P\<^sup>t \<and> ok\<^sup>>)))"
    by (simp add: H2_split)
  also have "... = (ok\<^sup>< \<and> (\<not> P\<^sup>f) \<longrightarrow> ok\<^sup>> \<and> P\<^sup>t)"
    by (pred_auto)
  also have "... = (ok\<^sup>< \<and> (\<not> P\<^sup>f) \<longrightarrow> ok\<^sup>> \<and> ok\<^sup>< \<and> P\<^sup>t)"
    by (pred_auto)
  also have "... = ((ok\<^sup>< \<and> (pre\<^sub>D(P) \<up> more\<^sub>L\<^sup>2)) \<longrightarrow> ok\<^sup>> \<and> ok\<^sup>< \<and> (post\<^sub>D(P) \<up> more\<^sub>L\<^sup>2))"
    by (simp add: ok_post ok_pre )
  also have "... = (ok\<^sup>< \<and> (pre\<^sub>D(P) \<up> more\<^sub>L\<^sup>2) \<longrightarrow> ok\<^sup>> \<and> (post\<^sub>D(P)\<up> more\<^sub>L\<^sup>2))\<^sub>e"
    by (pred_auto)
  also have "... = pre\<^sub>D(P) \<turnstile>\<^sub>r post\<^sub>D(P)"
    by (simp add: rdesign_def design_def)
  finally show ?thesis .
qed

theorem H1_H2_is_rdesign:
  assumes "P is H1" "P is H2"
  shows "P = pre\<^sub>D(P) \<turnstile>\<^sub>r post\<^sub>D(P)"
  by (metis H1_H2_eq_rdesign Healthy_def assms(1) assms(2))

thm H1_H2_eq_rdesign
thm rdesign_refinement

lemma H1_H2_refinement:
  assumes "P is \<^bold>H" "Q is \<^bold>H"
  shows "P \<sqsubseteq> Q \<longleftrightarrow> (`pre\<^sub>D(P) \<longrightarrow> pre\<^sub>D(Q)` \<and> `pre\<^sub>D(P) \<and> post\<^sub>D(Q) \<longrightarrow> post\<^sub>D(P)`)"
  using assms
  apply (simp only:rdesign_refinement[symmetric])
  by (metis H1_H2_eq_rdesign Healthy_if)

lemma H1_H2_refines:
  assumes "P is \<^bold>H" "Q is \<^bold>H" "P \<sqsubseteq> Q"
  shows "pre\<^sub>D(Q) \<sqsubseteq> pre\<^sub>D(P)" "post\<^sub>D(P) \<sqsubseteq> (pre\<^sub>D(P) \<and> post\<^sub>D(Q))"
  apply (metis assms(3) conj_pred_def design_pre_choice ref_lattice.inf.absorb_iff2 ref_lattice.le_iff_sup)
  apply (metis assms(3) design_post_choice pred_ba.inf_le2 pred_ba.le_supI1 ref_lattice.inf.absorb_iff2)
  done
  
lemma H1_H2_idempotent: "\<^bold>H (\<^bold>H P) = \<^bold>H P"
  by (simp add: H1_H2_commute H1_idem H2_idem)

lemma H1_H2_Idempotent [closure]: "Idempotent \<^bold>H"
  by (simp add: Idempotent_def H1_H2_idempotent)

(*
lemma H1_H2_monotonic [closure]: "Monotone \<^bold>H"
  by (simp add: H1_monotone H2_def mono_def seqr_mono)

lemma H1_H2_Continuous [closure]: "Continuous \<^bold>H"
  by (simp add: Continuous_comp H1_Continuous H1_H2_comp H2_Continuous)
*)

lemma H1_H2_false: "\<^bold>H false = \<top>\<^sub>D"
  by (pred_auto)

lemma H1_H2_true: "\<^bold>H true = \<bottom>\<^sub>D"
  by (pred_auto)

lemma design_is_H1_H2 [closure]:
  "\<lbrakk> $ok\<^sup>> \<sharp> P; $ok\<^sup>> \<sharp> Q \<rbrakk> \<Longrightarrow> (P \<turnstile> Q) is \<^bold>H"
  by (simp add: H1_design H2_design Healthy_def')

lemma rdesign_is_H1_H2 [closure]:
  "(P \<turnstile>\<^sub>r Q) is \<^bold>H"
  by (simp add: Healthy_def H1_rdesign H2_rdesign)

lemma top_d_is_H1_H2 [closure]: "\<top>\<^sub>D is \<^bold>H"
  by (simp add: rdesign_is_H1_H2 top_d_ndes_def)

lemma bot_d_is_H1_H2 [closure]: "\<bottom>\<^sub>D is \<^bold>H"
  by (metis bot_d_true rdesign_is_H1_H2 true_is_rdesign)

lemma seq_r_H1_H2_closed [closure]:
  assumes "P is \<^bold>H" "Q is \<^bold>H"
  shows "(P ;; Q) is \<^bold>H"
proof -
  obtain P\<^sub>1 P\<^sub>2 where "P = P\<^sub>1 \<turnstile>\<^sub>r P\<^sub>2"
    by (metis H1_H2_commute H1_H2_is_rdesign H2_idem Healthy_def assms(1))
  moreover obtain Q\<^sub>1 Q\<^sub>2 where "Q = Q\<^sub>1 \<turnstile>\<^sub>r Q\<^sub>2"
   by (metis H1_H2_commute H1_H2_is_rdesign H2_idem Healthy_def assms(2))
  moreover have "((P\<^sub>1 \<turnstile>\<^sub>r P\<^sub>2) ;; (Q\<^sub>1 \<turnstile>\<^sub>r Q\<^sub>2)) is \<^bold>H"
    by (simp add: rdesign_composition rdesign_is_H1_H2)
  ultimately show ?thesis by simp
qed

lemma H1_H2_left_unit: "P is \<^bold>H \<Longrightarrow> II\<^sub>D ;; P = P"
  by (metis H1_H2_eq_rdesign Healthy_def' rdesign_left_unit)

thm design_is_H1_H2

lemma UINF_H1_H2_closed [closure]:
  assumes "A \<noteq> {}" "\<forall> P \<in> A. P is \<^bold>H"
  shows "(\<Sqinter> A) is H1_H2"
proof -
  from assms have A: "A = H1_H2 ` A"
    by (auto simp add: Healthy_def rev_image_eqI)
  then have "\<Sqinter> (...) = (\<Sqinter> P \<in> A. (\<not> P\<^sup>f) \<turnstile> P\<^sup>t)"
    by (simp add:H1_H2_eq_design)
  also have "... = (\<Squnion> P \<in> A. \<not> P\<^sup>f) \<turnstile> (\<Sqinter> P \<in> A. P\<^sup>t)"
    by (simp add: design_UINF_mem assms)
  also have "... is H1_H2"
  proof -
    have "$ok\<^sup>> \<sharp> (\<Squnion>P\<in>A. \<not> P\<lbrakk>False/ok\<^sup>>\<rbrakk>)"
         "$ok\<^sup>> \<sharp> (\<Sqinter>P \<in> A. P\<^sup>t)"
      by (pred_auto)+
    then show ?thesis 
      by (simp add: design_is_H1_H2)
  qed
  ultimately show ?thesis using A by auto
qed

definition design_inf :: "('\<alpha>, '\<beta>) des_rel set \<Rightarrow> ('\<alpha>, '\<beta>) des_rel" ("\<Sqinter>\<^sub>D_" [900] 900) where
"\<Sqinter>\<^sub>D A = (if (A = {}) then \<top>\<^sub>D else \<Sqinter> A)"

abbreviation design_sup :: "('\<alpha>, '\<beta>) des_rel set \<Rightarrow> ('\<alpha>, '\<beta>) des_rel" ("\<Squnion>\<^sub>D_" [900] 900) where
"\<Squnion>\<^sub>D A \<equiv> \<Squnion> A"

lemma design_inf_H1_H2_closed:
  assumes "\<forall> P \<in> A. P is \<^bold>H"
  shows "(\<Sqinter>\<^sub>D A) is \<^bold>H"
  using assms
  by (auto simp add: design_inf_def closure)
 
lemma design_sup_empty [simp]: "\<Sqinter>\<^sub>D {} = \<top>\<^sub>D"
  by (simp add: design_inf_def)

lemma design_sup_non_empty [simp]: "A \<noteq> {} \<Longrightarrow> \<Sqinter>\<^sub>D A = \<Sqinter> A"
  by (simp add: design_inf_def)

thm design_is_H1_H2

lemma USUP_mem_H1_H2_closed:
  assumes "\<And> i. i \<in> A \<Longrightarrow> P i is \<^bold>H"
  shows "(\<Squnion> i\<in>A. P i) is \<^bold>H"
proof -
  from assms have "(\<Squnion> i\<in>A. P i) = (\<Squnion> i\<in>A. \<^bold>H(P i))"
    by (simp add:Healthy_def)
  also have "... = (\<Squnion> i\<in>A. (\<not> (P i)\<^sup>f) \<turnstile> (P i)\<^sup>t)"
    by (simp add:H1_H2_eq_design)
  also have "... = (\<Sqinter> i\<in>A. \<not> (P i)\<^sup>f) \<turnstile> (\<Squnion> i\<in>A. (\<not> (@(P i))\<^sup>f \<longrightarrow> (@(P i))\<^sup>t)\<^sub>e)"    
    by (simp add: design_USUP_mem, pred_auto)
  also have "... is \<^bold>H"
  proof -
    have "$ok\<^sup>> \<sharp> (\<Sqinter> i\<in>A. \<not> (P i)\<^sup>f)"
         "$ok\<^sup>> \<sharp> (\<Squnion> i\<in>A. (\<not> (@(P i))\<^sup>f \<longrightarrow> (@(P i))\<^sup>t)\<^sub>e)"
      by pred_auto+
    then show ?thesis
      using design_is_H1_H2 by blast
  qed
  ultimately show ?thesis by auto
qed

lemma USUP_ind_H1_H2_closed:
  assumes "\<And> i. P i is \<^bold>H"
  shows "(\<Squnion> i. P i) is \<^bold>H"
  using assms USUP_mem_H1_H2_closed[of UNIV P] by simp
  
lemma Inf_H1_H2_closed:
  assumes "\<forall> P \<in> A. P is \<^bold>H"
  shows "(\<Squnion> A) is \<^bold>H"
proof -
  from assms have A: "A = \<^bold>H ` A"
    by (auto simp add: Healthy_def rev_image_eqI)
  also have "(\<Squnion> ...) = (\<Squnion> P \<in> A. \<^bold>H(P))"
    by auto
  also have B: "... = (\<Squnion> P \<in> A. (\<not> P\<^sup>f) \<turnstile> P\<^sup>t)"
    by (simp add:H1_H2_eq_design)
  then have C: "... = (\<Sqinter> P \<in> A. \<not> P\<^sup>f) \<turnstile> (\<Squnion> P \<in> A. (\<not> P\<^sup>f \<longrightarrow> P\<^sup>t)\<^sub>e)"
    by (simp add: design_USUP_mem, pred_auto)
  then have "... is \<^bold>H"
  proof -
    have "$ok\<^sup>> \<sharp> (\<Sqinter>P\<in>A. \<not> P\<lbrakk>False/ok\<^sup>>\<rbrakk>)"
         "$ok\<^sup>> \<sharp> \<Squnion>\<^sub>D((\<lambda>P. (\<not> P\<lbrakk>False/ok\<^sup>>\<rbrakk> \<longrightarrow> P\<lbrakk>True/ok\<^sup>>\<rbrakk>)\<^sub>e) ` A)"
      by (pred_auto)+
    then show ?thesis 
      using design_is_H1_H2 by auto
  qed
  ultimately show ?thesis using A B C by auto
qed

lemma rdesign_ref_monos:
  assumes "P is \<^bold>H" "Q is \<^bold>H" "P \<sqsubseteq> Q"
  shows "pre\<^sub>D(Q) \<sqsubseteq> pre\<^sub>D(P)" "post\<^sub>D(P) \<sqsubseteq> (pre\<^sub>D(P) \<and> post\<^sub>D(Q))"
proof -
  have r: "P \<sqsubseteq> Q \<longleftrightarrow> (`pre\<^sub>D(P) \<longrightarrow> pre\<^sub>D(Q)` \<and> `pre\<^sub>D(P) \<and> post\<^sub>D(Q) \<longrightarrow> post\<^sub>D(P)`)"
    using assms(3) design_refine_thms(1) design_refine_thms(2) by blast
  from r assms show "pre\<^sub>D(Q) \<sqsubseteq> pre\<^sub>D(P)"
    using H1_H2_refines(1) by blast
  from r assms show "post\<^sub>D(P) \<sqsubseteq> (pre\<^sub>D(P) \<and> post\<^sub>D(Q))"
    using H1_H2_refines(2) by blast
qed

subsection \<open> H3: The design assumption is a precondition \<close>

definition H3 :: "('\<alpha>, '\<beta>) des_rel \<Rightarrow> ('\<alpha>, '\<beta>) des_rel" where
[pred]: "H3 (P) \<equiv> P ;; II\<^sub>D"

theorem H3_idem:
  "H3(H3(P)) = H3(P)"
  by (metis H3_def design_skip_idem seqr_assoc)

theorem H3_mono:
  "P \<sqsubseteq> Q \<Longrightarrow> H3(P) \<sqsubseteq> H3(Q)"
  by (simp add: H3_def seqr_mono)

(*
theorem H3_Monotonic:
  "Monotonic H3"
  by (simp add: H3_mono mono_def)

theorem H3_Continuous: "Continuous H3"
  by (rel_auto)
*)

theorem design_condition_is_H3:
  assumes "out\<alpha> \<sharp> p"
  shows "(p \<turnstile> Q) is H3"
proof -
  have "((p \<turnstile> Q) ;; II\<^sub>D) = (\<not> ((\<not> p) ;; true)) \<turnstile> (Q\<^sup>t ;; II\<lbrakk>True/ok\<^sup><\<rbrakk>)"
    by (simp add: skip_d_alt_def design_composition_subst unrest assms)    
  also have "... = p \<turnstile> (Q\<^sup>t ;; II\<lbrakk>True/ok\<^sup><\<rbrakk>)"
    using assms precond_equiv seqr_true_lemma
    by metis
  also have "... = p \<turnstile> Q"
    by (pred_auto)
  finally show ?thesis
    by (simp add: H3_def Healthy_def')
qed

theorem rdesign_H3_iff_pre:
  "P \<turnstile>\<^sub>r Q is H3 \<longleftrightarrow> P = (P ;; true)"
proof -
  have "(P \<turnstile>\<^sub>r Q) ;; II\<^sub>D = (P \<turnstile>\<^sub>r Q) ;; (true \<turnstile>\<^sub>r II)"
    by (simp add: skip_d_def)
  also have "... = (\<not> ((\<not> P) ;; true) \<and> \<not> (Q ;; (\<not> true))) \<turnstile>\<^sub>r (Q ;; II)"
    by (simp add: rdesign_composition)
  also have "... = (\<not> ((\<not> P) ;; true) \<and> \<not> (Q ;; (\<not> true))) \<turnstile>\<^sub>r Q"
    by (pred_auto)
  also have "... = (\<not> ((\<not> P) ;; true)) \<turnstile>\<^sub>r Q"
    by (pred_auto)
  finally have "P \<turnstile>\<^sub>r Q is H3 \<longleftrightarrow> P \<turnstile>\<^sub>r Q = (\<not> ((\<not> P) ;; true)) \<turnstile>\<^sub>r Q"
    by (metis H3_def Healthy_def')
  also have "... \<longleftrightarrow> P = (\<not> ((\<not> P) ;; true))"
    by (metis rdesign_pre)
  also have "... \<longleftrightarrow> P = (P ;; true)"
    by (simp add: seqr_true_lemma)
  finally show ?thesis .
qed

theorem design_H3_iff_pre:
  assumes "$ok\<^sup>< \<sharp> P" "$ok\<^sup>> \<sharp> P" "$ok\<^sup>< \<sharp> Q" "$ok\<^sup>> \<sharp> Q"
  shows "P \<turnstile> Q is H3 \<longleftrightarrow> P = (P ;; true)"
proof -
  have "P \<turnstile> Q = (P \<down> more\<^sub>L\<^sup>2) \<turnstile>\<^sub>r (Q \<down> more\<^sub>L\<^sup>2)"
    by (simp add: assms rdesign_def lift_desr_inv)
  moreover hence "(P \<down> more\<^sub>L\<^sup>2) \<turnstile>\<^sub>r (Q \<down> more\<^sub>L\<^sup>2) is H3 \<longleftrightarrow> (P \<down> more\<^sub>L\<^sup>2) = ((P \<down> more\<^sub>L\<^sup>2) ;; true)"
    using rdesign_H3_iff_pre by blast
  ultimately show ?thesis
    by (metis assms(1,2) design_condition_is_H3 lift_desr_inv unrest_out_des_lift utp_rel_laws.precond_equiv)
qed

theorem H1_H3_commute:
  "H1 (H3 P) = H3 (H1 P)"
  by (pred_auto)

lemma skip_d_absorb_J_1:
  "(II\<^sub>D ;; J) = II\<^sub>D"
  by (metis H2_def H2_rdesign skip_d_def)

lemma skip_d_absorb_J_2:
  "(J ;; II\<^sub>D) = II\<^sub>D"
proof -
  have "(J ;; II\<^sub>D) = ((ok\<^sup>< \<longrightarrow> ok\<^sup>>) \<and> II \<up> more\<^sub>L\<^sup>2)\<^sub>e ;; (true \<turnstile> II)"
    by (simp add: J_def skip_d_alt_def)
  also have "... = ((((ok\<^sup>< \<longrightarrow> ok\<^sup>>)\<^sub>e \<and> II \<up> more\<^sub>L\<^sup>2)\<lbrakk>False/ok\<^sup>>\<rbrakk> ;; (true \<turnstile> II)\<lbrakk>False/ok\<^sup><\<rbrakk>)
                  \<or> (((ok\<^sup>< \<longrightarrow> ok\<^sup>>)\<^sub>e \<and> II \<up> more\<^sub>L\<^sup>2)\<lbrakk>True/ok\<^sup>>\<rbrakk> ;; (true \<turnstile> II)\<lbrakk>True/ok\<^sup><\<rbrakk>))"
    by (pred_auto)
  also have "... = ((\<not>ok\<^sup>< \<and> II \<up> more\<^sub>L\<^sup>2 ;; true) \<or> (II \<up> more\<^sub>L\<^sup>2 ;; ok\<^sup>> \<and> II \<up> more\<^sub>L\<^sup>2))"
    by (pred_auto)
  also have "... = II\<^sub>D"
    by (pred_auto)
  finally show ?thesis .
qed

lemma H2_H3_absorb:
  "H2 (H3 P) = H3 P"
  by (metis H2_def H3_def seqr_assoc skip_d_absorb_J_1)

lemma H3_H2_absorb:
  "H3 (H2 P) = H3 P"
  by (metis H2_def H3_def seqr_assoc skip_d_absorb_J_2)

theorem H2_H3_commute:
  "H2 (H3 P) = H3 (H2 P)"
  by (simp add: H2_H3_absorb H3_H2_absorb)

theorem H3_design_pre:
  assumes "$ok\<^sup>< \<sharp> p" "out\<alpha> \<sharp> p" "$ok\<^sup>< \<sharp> Q" "$ok\<^sup>> \<sharp> Q"
  shows "H3(p \<turnstile> Q) = p \<turnstile> Q"
  using assms
  using Healthy_def design_condition_is_H3 by auto

theorem H3_rdesign_pre:
  assumes "out\<alpha> \<sharp> p"
  shows "H3(p \<turnstile>\<^sub>r Q) = p \<turnstile>\<^sub>r Q"
  using assms
  by (simp add: H3_def)

theorem H3_ndesign: "H3(p \<turnstile>\<^sub>n Q) = (p \<turnstile>\<^sub>n Q)"
  by pred_auto

theorem ndesign_is_H3 [closure]: "p \<turnstile>\<^sub>n Q is H3"
  by (simp add: H3_ndesign Healthy_def)

(*
lemma msubst_pre_H3: "(\<And>x. P x is H3) \<Longrightarrow> P x\<lbrakk>x\<rightarrow>\<lceil>v\<rceil>\<^sub><\<rbrakk> is H3"
  by (rel_auto)
*)

subsection \<open> Normal Designs as $H1$-$H3$ predicates \<close>

text \<open> A normal design~\cite{Guttman2010} refers only to initial state variables in the precondition. \<close>

abbreviation H1_H3 :: "('\<alpha>, '\<beta>) des_rel \<Rightarrow> ('\<alpha>, '\<beta>) des_rel" ("\<^bold>N") where
"H1_H3 p \<equiv> H1 (H3 p)"

lemma H1_H3_comp: "H1_H3 = H1 \<circ> H3"
  by (auto)

theorem H1_H3_is_design:
  assumes "P is H1" "P is H3"
  shows "P = (\<not> P\<^sup>f) \<turnstile> P\<^sup>t"
  by (metis H1_H2_eq_design H2_H3_absorb Healthy_def' assms(1) assms(2))

theorem H1_H3_is_rdesign:
  assumes "P is H1" "P is H3"
  shows "P = pre\<^sub>D(P) \<turnstile>\<^sub>r post\<^sub>D(P)"
  by (metis H1_H2_is_rdesign H2_H3_absorb Healthy_def' assms)

theorem H1_H3_is_normal_design:
  assumes "P is H1" "P is H3"
  shows "P = (pre\<^sub>D(P))\<^sub>< \<turnstile>\<^sub>n post\<^sub>D(P)"
  by (metis H1_H3_is_rdesign SEXP_def assms drop_pre_inv rdesign_H3_iff_pre utp_rel.postcond_equiv)

lemma H1_H3_idempotent: "\<^bold>N (\<^bold>N P) = \<^bold>N P"
  by (simp add: H1_H3_commute H1_idem H3_idem)

lemma H1_H3_Idempotent [closure]: "Idempotent \<^bold>N"
  by (simp add: Idempotent_def H1_H3_idempotent)

(*
lemma H1_H3_monotonic [closure]: "Monotonic \<^bold>N"
  by (simp add: H1_monotone H3_mono mono_def)

lemma H1_H3_Continuous [closure]: "Continuous \<^bold>N"
  by (simp add: Continuous_comp H1_Continuous H1_H3_comp H3_Continuous)
*)
lemma H1_H3_false: "\<^bold>N false = \<top>\<^sub>D"
  by (pred_auto)

lemma H1_H3_true: "\<^bold>N true = \<bottom>\<^sub>D"
  by (pred_auto)

lemma H1_H3_intro:
  assumes "P is \<^bold>H" "out\<alpha> \<sharp> pre\<^sub>D(P)"
  shows "P is \<^bold>N"
  by (metis H1_H2_eq_rdesign H1_rdesign H3_rdesign_pre Healthy_def' assms)

lemma H1_H3_left_unit: "P is \<^bold>N \<Longrightarrow> II\<^sub>D ;; P = P"
  by (metis H1_H2_left_unit H1_H3_commute H2_H3_absorb H3_idem Healthy_def)
  
lemma H1_H3_right_unit: "P is \<^bold>N \<Longrightarrow> P ;; II\<^sub>D = P"
  by (metis H1_H3_commute H3_def H3_idem Healthy_def)

lemma H1_H3_top_left: "P is \<^bold>N \<Longrightarrow> \<top>\<^sub>D ;; P = \<top>\<^sub>D"
  by (metis H1_H2_eq_design H2_H3_absorb Healthy_if design_top_left_zero)
  
lemma H1_H3_bot_left: "P is \<^bold>N \<Longrightarrow> \<bottom>\<^sub>D ;; P = \<bottom>\<^sub>D"
  by (metis H1_idem H1_left_zero Healthy_def bot_d_true)

lemma H1_H3_impl_H2 [closure]: "P is \<^bold>N \<Longrightarrow> P is \<^bold>H"
  by (metis H1_H2_commute H1_idem H2_H3_absorb Healthy_def')

lemma H1_H3_eq_design_d_comp: "\<^bold>N(P) = ((\<not> P\<^sup>f) \<turnstile> P\<^sup>t) ;; II\<^sub>D"
  by (metis H1_H2_eq_design H1_H3_commute H3_H2_absorb H3_def)

lemma H1_H3_eq_design: "\<^bold>N(P) = (\<not> (P\<^sup>f ;; true)) \<turnstile> P\<^sup>t"
  apply (simp add: H1_H3_eq_design_d_comp skip_d_alt_def)
  apply (subst design_composition_subst)
  by pred_auto+

lemma H3_unrest_out_alpha_nok [unrest]:
  assumes "P is \<^bold>N"
  shows "out\<alpha> \<sharp> P\<^sup>f"
proof -
  have "P = (\<not> (P\<^sup>f ;; true)) \<turnstile> P\<^sup>t"
    by (metis H1_H3_eq_design Healthy_def assms)
  also have "out\<alpha> \<sharp> (...\<^sup>f)"
    by (simp add: design_def usubst unrest, pred_auto)
  ultimately show ?thesis by auto
qed

lemma H3_unrest_out_alpha [unrest]: "P is \<^bold>N \<Longrightarrow> out\<alpha> \<sharp> pre\<^sub>D(P)"
  by (metis H1_H3_commute H1_H3_is_rdesign H1_idem Healthy_def' precond_equiv rdesign_H3_iff_pre)

lemma ndesign_H1_H3 [closure]: "p \<turnstile>\<^sub>n Q is \<^bold>N"
  by (simp add: H1_rdesign H3_def Healthy_def', pred_auto)

lemma ndesign_form: "P is \<^bold>N \<Longrightarrow> ((pre\<^sub>D(P))\<^sub>< \<turnstile>\<^sub>n post\<^sub>D(P)) = P"
  by (metis H1_H3_is_normal_design H1_H3_right_unit H3_def Healthy_def)

lemma des_bot_H1_H3 [closure]: "\<bottom>\<^sub>D is \<^bold>N"
  by (metis H1_design H3_def Healthy_def' design_false_pre design_true_left_zero skip_d_alt_def bot_d_def)

lemma des_top_is_H1_H3 [closure]: "\<top>\<^sub>D is \<^bold>N"
  by (metis ndesign_H1_H3 ndesign_miracle) 
    
lemma skip_d_is_H1_H3 [closure]: "II\<^sub>D is \<^bold>N"
  by (simp add: ndesign_H1_H3 skip_d_ndes_def)
    
lemma seq_r_H1_H3_closed [closure]:
  assumes "P is \<^bold>N" "Q is \<^bold>N"
  shows "(P ;; Q) is \<^bold>N"
  by (metis (no_types) H1_H2_eq_design H1_H3_eq_design_d_comp H1_H3_impl_H2 Healthy_def assms(1) assms(2) seq_r_H1_H2_closed seqr_assoc)
  
lemma dcond_H1_H2_closed [closure]:
  assumes "P is \<^bold>N" "Q is \<^bold>N"
  shows "(P \<triangleleft> b \<triangleright>\<^sub>D Q) is \<^bold>N"
  by (metis assms ndesign_H1_H3 ndesign_dcond ndesign_form)

lemma inf_H1_H2_closed [closure]:
  assumes "P is \<^bold>N" "Q is \<^bold>N"
  shows "(P \<sqinter> Q) is \<^bold>N"
proof -
  obtain P\<^sub>1 P\<^sub>2 Q\<^sub>1 Q\<^sub>2 where P:"P = (P\<^sub>1 \<turnstile>\<^sub>n P\<^sub>2)" and Q:"Q = (Q\<^sub>1 \<turnstile>\<^sub>n Q\<^sub>2)"
    by (metis assms ndesign_form)
  have "(P\<^sub>1 \<turnstile>\<^sub>n P\<^sub>2) \<sqinter> (Q\<^sub>1 \<turnstile>\<^sub>n Q\<^sub>2) = (P\<^sub>1 \<and> Q\<^sub>1) \<turnstile>\<^sub>n (P\<^sub>2 \<or> Q\<^sub>2)"
    by (simp add: ndesign_choice)
  moreover have "... is \<^bold>N"
    by (simp add: ndesign_H1_H3)
  ultimately show ?thesis by (simp add: P Q)
qed

lemma sup_H1_H2_closed [closure]:
  assumes "P is \<^bold>N" "Q is \<^bold>N"
  shows "(P \<squnion> Q) is \<^bold>N"
proof -
  obtain P\<^sub>1 P\<^sub>2 Q\<^sub>1 Q\<^sub>2 where P:"P = (P\<^sub>1 \<turnstile>\<^sub>n P\<^sub>2)" and Q:"Q = (Q\<^sub>1 \<turnstile>\<^sub>n Q\<^sub>2)"
    by (metis assms ndesign_form)
  have "(P\<^sub>1 \<turnstile>\<^sub>n P\<^sub>2) \<squnion> (Q\<^sub>1 \<turnstile>\<^sub>n Q\<^sub>2) = (P\<^sub>1 \<or> Q\<^sub>1) \<turnstile>\<^sub>n ((P\<^sub>1\<^sup>< \<longrightarrow> P\<^sub>2) \<and> (Q\<^sub>1\<^sup>< \<longrightarrow> Q\<^sub>2))"
    by (simp add: ndesign_inf)
  moreover have "... is \<^bold>N"
    by (simp add: ndesign_H1_H3)
  ultimately show ?thesis by (simp add: P Q)
qed
    
lemma ndes_seqr_miracle:
  assumes "P is \<^bold>N"
  shows "P ;; \<top>\<^sub>D = (pre\<^sub>D P)\<^sub>< \<turnstile>\<^sub>n false"
proof -
  have "P ;; \<top>\<^sub>D = ((pre\<^sub>D(P))\<^sub>< \<turnstile>\<^sub>n post\<^sub>D(P)) ;; (True \<turnstile>\<^sub>n false)"
    by (simp add: assms ndesign_form ndesign_miracle)
  also have "... = (pre\<^sub>D P)\<^sub>< \<turnstile>\<^sub>n false"
    by (simp add: ndesign_composition_wlp wp)
  finally show ?thesis .
qed
    
lemma ndes_seqr_abort: 
  assumes "P is \<^bold>N"
  shows "P ;; \<bottom>\<^sub>D = ((pre\<^sub>D P)\<^sub>< \<and> post\<^sub>D P wlp False) \<turnstile>\<^sub>n false"
proof -
  have "P ;; \<bottom>\<^sub>D = ((pre\<^sub>D(P))\<^sub>< \<turnstile>\<^sub>n post\<^sub>D(P)) ;; (False \<turnstile>\<^sub>n false)"
    by (simp add: assms bot_d_true ndesign_false_pre ndesign_form)
  also have "... = ((pre\<^sub>D P)\<^sub>< \<and> post\<^sub>D P wlp False) \<turnstile>\<^sub>n false"
    by (simp add: ndesign_composition_wlp)
  finally show ?thesis .
qed

lemma USUP_ind_H1_H3_closed [closure]:
  "\<lbrakk> \<And> i. P i is \<^bold>N \<rbrakk> \<Longrightarrow> (\<Squnion> i. P i) is \<^bold>N"
  by (rule H1_H3_intro, simp_all add: H1_H3_impl_H2 USUP_ind_H1_H2_closed preD_USUP_ind unrest)

(*
lemma msubst_pre_H1_H3 [closure]: "(\<And>x. P x is \<^bold>N) \<Longrightarrow> P x\<lbrakk>x\<rightarrow>\<lceil>v\<rceil>\<^sub><\<rbrakk> is \<^bold>N"
  by (metis H1_H3_right_unit H3_def Healthy_if Healthy_intro msubst_H1 msubst_pre_H3)
*)

subsection \<open> H4: Feasibility \<close>

definition H4 :: "('\<alpha>, '\<beta>) des_rel \<Rightarrow> ('\<alpha>, '\<beta>) des_rel" where
[pred]: "H4(P) = ((P;;true) \<longrightarrow> P)"

theorem H4_idem:
  "H4(H4(P)) = H4(P)"
  by (pred_auto)

lemma is_H4_alt_def:
  "P is H4 \<longleftrightarrow> (P ;; true) = true"
  by (pred_auto, blast)

end