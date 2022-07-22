theory utp_des_laws
  imports utp_des_core
begin 

named_theorems ndes and ndes_simp

subsection \<open> Basic Design Laws \<close>

lemma design_export_ok: "(P \<turnstile> Q) = (P \<turnstile> (ok\<^sup>< \<and> Q))"
  by (pred_auto)

lemma design_export_ok': "P \<turnstile> Q = (P \<turnstile> (ok\<^sup>> \<and> Q))"
  by (pred_auto)

lemma design_export_pre: "P \<turnstile> (P \<and> Q) = P \<turnstile> Q"
  by (pred_auto)

lemma design_export_spec: "P \<turnstile> (P \<longrightarrow> Q)\<^sub>e = P \<turnstile> Q"
  by (pred_auto)

lemma design_ok_pre_conj: "(ok\<^sup>< \<and> P) \<turnstile> Q = P \<turnstile> Q"
  by (pred_auto)

lemma true_is_design: "(false \<turnstile> true) = true"
  by (pred_auto)

lemma true_is_rdesign: "(false \<turnstile>\<^sub>r true) = true"
  by (pred_auto)
    
lemma bot_d_true: "\<bottom>\<^sub>D = true"
  by (pred_auto)  
  
lemma bot_d_ndes_def [ndes_simp]: "\<bottom>\<^sub>D = (false \<turnstile>\<^sub>n true)"
  by (pred_auto)

lemma design_false_pre: "(false \<turnstile> P) = true"
  by (pred_auto)

lemma rdesign_false_pre: "(false \<turnstile>\<^sub>r P) = true"
  by (pred_auto)

lemma ndesign_false_pre: "(False \<turnstile>\<^sub>n P) = true"
  by (pred_auto)

lemma ndesign_miracle: "(true \<turnstile>\<^sub>n false) = \<top>\<^sub>D"
  by (pred_auto)

lemma top_d_ndes_def [ndes_simp]: "\<top>\<^sub>D = (true \<turnstile>\<^sub>n false)"
  by (pred_auto)

lemma skip_d_alt_def: "II\<^sub>D = true \<turnstile> II"
  by (pred_auto)

lemma skip_d_ndes_def [ndes_simp]: "II\<^sub>D = true \<turnstile>\<^sub>n II"
  by (pred_auto)

lemma design_subst_ok:
  "(P\<lbrakk>true/ok\<^sup><\<rbrakk> \<turnstile> Q\<lbrakk>true/ok\<^sup><\<rbrakk>) = (P \<turnstile> Q)"
  by (pred_auto)

lemma design_subst_ok_ok':
  "(P\<lbrakk>true/ok\<^sup><\<rbrakk> \<turnstile> Q\<lbrakk>true,true/ok\<^sup><,ok\<^sup>>\<rbrakk>) = (P \<turnstile> Q)"
  by pred_auto

lemma design_subst_ok':
  "(P \<turnstile> Q\<lbrakk>true/ok\<^sup>>\<rbrakk>) = (P \<turnstile> Q)"
  by pred_auto

subsection \<open> Sequential Composition Laws \<close>

theorem design_skip_idem [simp]:
  "(II\<^sub>D ;; II\<^sub>D) = II\<^sub>D"
  by (pred_auto)

(*
theorem design_composition_cond:
  assumes
    "out\<alpha> \<sharp> p1" "$ok\<^sup>< \<sharp> P2" "$ok\<^sup>> \<sharp> Q1" "$ok\<^sup>< \<sharp> Q2"
  shows "((p1 \<turnstile> Q1) ;; (P2 \<turnstile> Q2)) = ((p1 \<and> \<not> (Q1 ;; (\<not> P2))) \<turnstile> (Q1 ;; Q2))"
  using assms
  apply (simp add: design_composition unrest precond_right_unit)
*)

(*
theorem rdesign_composition_cond:
  assumes "out\<alpha> \<sharp> p1"
  shows "((p1 \<turnstile>\<^sub>r Q1) ;; (P2 \<turnstile>\<^sub>r Q2)) = ((p1 \<and> \<not> (Q1 ;; (\<not> P2))) \<turnstile>\<^sub>r (Q1 ;; Q2))"
  using assms
  by (simp add: rdesign_def design_composition_cond unrest alpha)
*)

(*
theorem design_composition_wp:
  fixes p1 p2 :: "'a des_vars_scheme \<Rightarrow> bool"
  assumes
    "$ok \<sharp> p1" "$ok \<sharp> p2"
    "$ok\<^sup>< \<sharp> Q1" "$ok\<^sup>> \<sharp> Q1" "$ok\<^sup>< \<sharp> Q2" "$ok\<^sup>> \<sharp> Q2"
  shows "(((p1\<^sup><)\<^sub>u \<turnstile> Q1) ;; ((p2\<^sup><)\<^sub>u \<turnstile> Q2)) = (((p1 \<and> Q1 wlp p2)\<^sup><)\<^sub>u \<turnstile> (Q1 ;; Q2))"
  using assms unfolding design_def
*)

(*
theorem rdesign_composition_wp:
  "((\<lceil>p1\<rceil>\<^sub>< \<turnstile>\<^sub>r Q1) ;; (\<lceil>p2\<rceil>\<^sub>< \<turnstile>\<^sub>r Q2)) = ((\<lceil>p1 \<and> Q1 wlp p2\<rceil>\<^sub><) \<turnstile>\<^sub>r (Q1 ;; Q2))"
  by (rel_blast)
*)
  
theorem design_true_left_zero: "(true ;; (P \<turnstile> Q)) = true"
  by pred_auto

theorem design_left_unit_hom:
  fixes P Q :: "('\<alpha>, '\<alpha>) des_rel"
  shows "(II\<^sub>D ;; (P \<turnstile>\<^sub>r Q)) = (P \<turnstile>\<^sub>r Q)"
  by pred_auto

theorem rdesign_left_unit [simp]:
  "II\<^sub>D ;; (P \<turnstile>\<^sub>r Q) = (P \<turnstile>\<^sub>r Q)"
  by (pred_auto)

theorem design_right_semi_unit:
  "(P \<turnstile>\<^sub>r Q) ;; II\<^sub>D = ((\<not> (\<not> P) ;; true) \<turnstile>\<^sub>r Q)"
  by pred_auto

theorem design_right_cond_unit [simp]:
  assumes "out\<alpha> \<sharp> p"
  shows "(p \<turnstile>\<^sub>r Q) ;; II\<^sub>D = (p \<turnstile>\<^sub>r Q)"
  using assms
  by (metis design_right_semi_unit postcond_simp seqr_true_lemma)

theorem ndesign_left_unit [simp]:
  "II\<^sub>D ;; (p \<turnstile>\<^sub>n Q) = (p \<turnstile>\<^sub>n Q)"
  by (pred_auto)

theorem design_bot_left_zero: "(\<bottom>\<^sub>D ;; (P \<turnstile> Q)) = \<bottom>\<^sub>D"
  by (pred_auto)

theorem design_top_left_zero: "(\<top>\<^sub>D ;; (P \<turnstile> Q)) = \<top>\<^sub>D"
  by (pred_auto)

subsection \<open> Preconditions and Postconditions \<close>

theorem design_npre:
  "(P \<turnstile> Q)\<^sup>f = (\<not> ok\<^sup>< \<or> \<not> P\<^sup>f)"
  by (pred_auto)

theorem design_pre:
  "\<not> (P \<turnstile> Q)\<^sup>f = (ok\<^sup>< \<and> P\<^sup>f)"
  by pred_auto

theorem design_post:
  "(P \<turnstile> Q)\<^sup>t = ((ok\<^sup>< \<and> P\<^sup>t) \<longrightarrow> Q\<^sup>t)\<^sub>e"
  by (pred_auto)

theorem rdesign_pre [simp]: "pre\<^sub>D(P \<turnstile>\<^sub>r Q) = P"
  by (pred_auto)

theorem rdesign_post [simp]: "post\<^sub>D(P \<turnstile>\<^sub>r Q) = (P \<longrightarrow> Q)\<^sub>e"
  by (pred_auto)

theorem ndesign_pre [simp]: "pre\<^sub>D(p \<turnstile>\<^sub>n Q) = p\<^sup><"
  by (pred_auto)

theorem ndesign_post [simp]: "post\<^sub>D(p \<turnstile>\<^sub>n Q) = (p\<^sup>< \<longrightarrow> Q)\<^sub>e"
  by (pred_auto)

lemma design_pre_choice [simp]:
  "pre\<^sub>D(P \<sqinter> Q) = (pre\<^sub>D(P) \<and> pre\<^sub>D(Q))"
  by (pred_auto)

lemma design_post_choice [simp]:
  "post\<^sub>D(P \<sqinter> Q) = (post\<^sub>D(P) \<or> post\<^sub>D(Q))"
  by (pred_auto)

lemma design_pre_condr [simp]:
  "pre\<^sub>D(P \<lhd> b \<up> des_vars.more\<^sub>L\<^sup>2 \<rhd> Q) = (pre\<^sub>D(P) \<lhd> b \<rhd> pre\<^sub>D(Q))"
  by (pred_auto)

lemma design_post_condr [simp]:
  shows "post\<^sub>D(P \<lhd> b \<up> des_vars.more\<^sub>L\<^sup>2 \<rhd> Q) = (post\<^sub>D(P) \<lhd> b \<rhd> post\<^sub>D(Q))"
  by (pred_auto)

lemma preD_USUP_mem: "pre\<^sub>D (\<Squnion> i\<in>A.  P i) = (\<Sqinter> i\<in>A. pre\<^sub>D(P i))"
  by (pred_auto)
  
lemma preD_USUP_ind: "pre\<^sub>D (\<Squnion> i. P i) = (\<Sqinter> i. pre\<^sub>D(P i))"
  by (pred_auto)

subsection \<open> Distribution Laws \<close>

theorem design_choice:
  "(P\<^sub>1 \<turnstile> P\<^sub>2) \<sqinter> (Q\<^sub>1 \<turnstile> Q\<^sub>2) = ((P\<^sub>1 \<and> Q\<^sub>1) \<turnstile> (P\<^sub>2 \<or> Q\<^sub>2))"
  by (pred_auto)

theorem rdesign_choice:
  "(P\<^sub>1 \<turnstile>\<^sub>r P\<^sub>2) \<sqinter> (Q\<^sub>1 \<turnstile>\<^sub>r Q\<^sub>2) = ((P\<^sub>1 \<and> Q\<^sub>1) \<turnstile>\<^sub>r (P\<^sub>2 \<or> Q\<^sub>2))"
  by (pred_auto)

theorem ndesign_choice [ndes_simp]:
  "(p\<^sub>1 \<turnstile>\<^sub>n P\<^sub>2) \<sqinter> (q\<^sub>1 \<turnstile>\<^sub>n Q\<^sub>2) = ((p\<^sub>1 \<and> q\<^sub>1) \<turnstile>\<^sub>n (P\<^sub>2 \<or> Q\<^sub>2))"
  by (pred_auto)

theorem ndesign_choice' [ndes_simp]:
  "((p\<^sub>1 \<turnstile>\<^sub>n P\<^sub>2) \<or> (q\<^sub>1 \<turnstile>\<^sub>n Q\<^sub>2)) = ((p\<^sub>1 \<and> q\<^sub>1) \<turnstile>\<^sub>n (P\<^sub>2 \<or> Q\<^sub>2))"
  by (pred_auto)

theorem design_inf:
  "(P\<^sub>1 \<turnstile> P\<^sub>2) \<squnion> (Q\<^sub>1 \<turnstile> Q\<^sub>2) = ((P\<^sub>1 \<or> Q\<^sub>1) \<turnstile> ((P\<^sub>1 \<longrightarrow> P\<^sub>2) \<and> (Q\<^sub>1 \<longrightarrow> Q\<^sub>2))\<^sub>e)"
  by (pred_auto)

theorem rdesign_inf:
  "(P\<^sub>1 \<turnstile>\<^sub>r P\<^sub>2) \<squnion> (Q\<^sub>1 \<turnstile>\<^sub>r Q\<^sub>2) = ((P\<^sub>1 \<or> Q\<^sub>1) \<turnstile>\<^sub>r ((P\<^sub>1 \<longrightarrow> P\<^sub>2) \<and> (Q\<^sub>1 \<longrightarrow> Q\<^sub>2))\<^sub>e)"
  by (pred_auto)

theorem ndesign_inf [ndes_simp]:
  "(p\<^sub>1 \<turnstile>\<^sub>n P\<^sub>2) \<squnion> (q\<^sub>1 \<turnstile>\<^sub>n Q\<^sub>2) = ((p\<^sub>1 \<or> q\<^sub>1) \<turnstile>\<^sub>n ((p\<^sub>1\<^sup>< \<longrightarrow> P\<^sub>2) \<and> (q\<^sub>1\<^sup>< \<longrightarrow> Q\<^sub>2))\<^sub>e)"
  by (pred_auto)
    
theorem design_condr:
  "((P\<^sub>1 \<turnstile> P\<^sub>2) \<lhd> b \<rhd> (Q\<^sub>1 \<turnstile> Q\<^sub>2)) = ((P\<^sub>1 \<lhd> b \<rhd> Q\<^sub>1) \<turnstile> (P\<^sub>2 \<lhd> b \<rhd> Q\<^sub>2))"
  by (pred_auto)

theorem ndesign_dcond [ndes_simp]:
  shows "((p\<^sub>1 \<turnstile>\<^sub>n P\<^sub>2) \<lhd> b\<^sup>< \<up> more\<^sub>L\<^sup>2 \<rhd> (q\<^sub>1 \<turnstile>\<^sub>n Q\<^sub>2)) = ((p\<^sub>1 \<triangleleft> b \<triangleright> q\<^sub>1) \<turnstile>\<^sub>n (P\<^sub>2 \<lhd> b\<^sup>< \<rhd> Q\<^sub>2))"
  by (pred_auto)

lemma design_UINF_mem:
  assumes "A \<noteq> {}"
  shows "(\<Sqinter> i \<in> A. P(i) \<turnstile> Q(i)) = (\<Squnion> i \<in> A. P(i)) \<turnstile> (\<Sqinter> i \<in> A. Q(i))"
  using assms by (pred_auto)

lemma ndesign_UINF_mem [ndes_simp]:
  fixes A :: "'i set"
  assumes "A \<noteq> {}"
  shows "(\<Sqinter> i \<in> A. (@(p i) \<turnstile>\<^sub>n Q(i))) = (\<Squnion> i \<in> \<guillemotleft>A\<guillemotright>. @(p i)) \<turnstile>\<^sub>n (\<Sqinter> i \<in> A. Q(i))"
  using assms by (pred_auto)

lemma ndesign_UINF_ind [ndes_simp]:
  "(\<Sqinter> i. p(i) \<turnstile>\<^sub>n Q(i)) = (\<Squnion> i. p(i)) \<turnstile>\<^sub>n (\<Sqinter> i. Q(i))"
  by (pred_auto)
    
lemma design_USUP_mem:
  "(\<Squnion> i \<in> A. P(i) \<turnstile> Q(i)) = (\<Sqinter> i \<in> A. P(i)) \<turnstile> (\<Squnion> i \<in> A. (@(P i) \<longrightarrow> @(Q i))\<^sub>e)"
  by (pred_auto)

lemma ndesign_USUP_mem [ndes_simp]:
  fixes A :: "'i set"
  shows "(\<Squnion> i \<in> A. @(p i) \<turnstile>\<^sub>n Q(i)) = (\<Sqinter> i \<in> \<guillemotleft>A\<guillemotright>. @(p i)) \<turnstile>\<^sub>n (\<Squnion> i \<in> A. (@(p i)\<^sup>< \<longrightarrow> @(Q i))\<^sub>e)"
  by (pred_auto)

lemma ndesign_USUP_ind [ndes_simp]:
  "(\<Squnion> i. @(p i) \<turnstile>\<^sub>n Q(i)) = (\<Sqinter> i. @(p i)) \<turnstile>\<^sub>n (\<Squnion> i. (@(p i)\<^sup>< \<longrightarrow> @(Q i))\<^sub>e)"
  by (pred_auto)

subsection \<open> Refinement Introduction \<close>

lemma ndesign_eq_intro:
  assumes "p\<^sub>1 = q\<^sub>1" "P\<^sub>2 = Q\<^sub>2"
  shows "p\<^sub>1 \<turnstile>\<^sub>n P\<^sub>2 = q\<^sub>1 \<turnstile>\<^sub>n Q\<^sub>2"
  by (simp add: assms)

(*
theorem design_refinement:
  assumes
    "$ok\<^sup>< \<sharp> P1" "$ok\<^sup>> \<sharp> P1" "$ok\<^sup>< \<sharp> P2" "$ok\<^sup>> \<sharp> P2"
    "$ok\<^sup>< \<sharp> Q1" "$ok\<^sup>> \<sharp> Q1" "$ok\<^sup>< \<sharp> Q2" "$ok\<^sup>> \<sharp> Q2"
  shows "((P1 \<turnstile> Q1) \<sqsubseteq> (P2 \<turnstile> Q2)) \<longleftrightarrow> (((P1 \<Rightarrow> P2) \<and> (P1 \<and> Q2 \<Rightarrow> Q1)) = UNIV)"
proof -
  have "(P1 \<turnstile> Q1) \<sqsubseteq> (P2 \<turnstile> Q2) \<longleftrightarrow> ((((ok\<^sup><)\<^sub>u \<and> P2 \<Rightarrow> (ok\<^sup>>)\<^sub>u \<and> Q2) \<Rightarrow> ((ok\<^sup><)\<^sub>u \<and> P1 \<Rightarrow> (ok\<^sup>>)\<^sub>u \<and> Q1)) = UNIV) "
    apply (pred_auto)
  also with assms have "... = `(P2 \<Rightarrow> ok\<^sup>> \<and> Q2) \<Rightarrow> (P1 \<Rightarrow> ok\<^sup>> \<and> Q1)`"
    by (subst subst_bool_split[of "in_var ok"], simp_all, subst_tac)
  also with assms have "... = `(\<not> P2 \<Rightarrow> \<not> P1) \<and> ((P2 \<Rightarrow> Q2) \<Rightarrow> P1 \<Rightarrow> Q1)`"
    by (subst subst_bool_split[of "out_var ok"], simp_all, subst_tac)
  also have "... \<longleftrightarrow> `(P1 \<Rightarrow> P2)` \<and> `P1 \<and> Q2 \<Rightarrow> Q1`"
    by (pred_auto)
  finally show ?thesis .
qed
*)

(*
theorem rdesign_refinement:
  "(P1 \<turnstile>\<^sub>r Q1 \<sqsubseteq> P2 \<turnstile>\<^sub>r Q2) \<longleftrightarrow> ((P1 \<Rightarrow> P2) = UNIV) \<and> ((P1 \<and> Q2 \<Rightarrow> Q1) = UNIV)"
  apply (pred_auto)
*)

lemma design_refine_intro:
  assumes "`P1 \<longrightarrow> P2`" "`P1 \<and> Q2 \<longrightarrow> Q1`"
  shows "P1 \<turnstile> Q1 \<sqsubseteq> P2 \<turnstile> Q2"
  using assms by (pred_auto)

lemma design_refine_intro':
  assumes "P\<^sub>2 \<sqsubseteq> P\<^sub>1" "Q\<^sub>1 \<sqsubseteq> (P\<^sub>1 \<and> Q\<^sub>2)"
  shows "P\<^sub>1 \<turnstile> Q\<^sub>1 \<sqsubseteq> P\<^sub>2 \<turnstile> Q\<^sub>2"
  using assms design_refine_intro[of P\<^sub>1 P\<^sub>2 Q\<^sub>2 Q\<^sub>1] by pred_auto

lemma rdesign_refine_intro:
  assumes "`P1 \<longrightarrow> P2`" "`P1 \<and> Q2 \<longrightarrow> Q1`"
  shows "P1 \<turnstile>\<^sub>r Q1 \<sqsubseteq> P2 \<turnstile>\<^sub>r Q2"
  using assms by (pred_auto)

lemma rdesign_refine_intro':
  assumes "P2 \<sqsubseteq> P1" "Q1 \<sqsubseteq> (P1 \<and> Q2)"
  shows "P1 \<turnstile>\<^sub>r Q1 \<sqsubseteq> P2 \<turnstile>\<^sub>r Q2"
  using assms by (pred_auto)

(*
lemma ndesign_refinement: 
  "p1 \<turnstile>\<^sub>n Q1 \<sqsubseteq> p2 \<turnstile>\<^sub>n Q2 \<longleftrightarrow> (((p1 \<Rightarrow> p2) = UNIV) \<and> (((p1\<^sup><)\<^sub>u \<and> Q2 \<Rightarrow> Q1) = UNIV))"
  by (simp add: ndesign_def rdesign_def design_refinement unrest, pred_auto)
*)

(*
lemma ndesign_refinement': 
  "p1 \<turnstile>\<^sub>n Q1 \<sqsubseteq> p2 \<turnstile>\<^sub>n Q2 \<longleftrightarrow> (`p1 \<Rightarrow> p2` \<and> Q1 \<sqsubseteq> ?[p1] ;; Q2)"
  by (simp add: ndesign_refinement, pred_auto)
*)

(*
lemma ndesign_refine_intro:
  assumes "(p1 \<Rightarrow> p2) = UNIV" "Q1 \<sqsubseteq> ?[p1] ;; Q2"
  shows "p1 \<turnstile>\<^sub>n Q1 \<sqsubseteq> p2 \<turnstile>\<^sub>n Q2"
  by (simp add: ndesign_refinement' assms)
*)

lemma design_top:
  "(P \<turnstile> Q) \<sqsubseteq> \<top>\<^sub>D"
  by (pred_auto)

lemma design_bottom:
  "\<bottom>\<^sub>D \<sqsubseteq> (P \<turnstile> Q)"
  by (pred_auto)

lemma design_refine_thms:
  assumes "P \<sqsubseteq> Q"
  shows "`pre\<^sub>D(P) \<longrightarrow> pre\<^sub>D(Q)`" "`pre\<^sub>D(P) \<and> post\<^sub>D(Q) \<longrightarrow> post\<^sub>D(P)`"
  using assms unfolding pred_refine_iff by (pred_auto, blast, pred_auto)

end