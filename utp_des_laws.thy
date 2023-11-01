theory utp_des_laws
  imports utp_des_core
begin 

named_theorems ndes and ndes_simp

subsection \<open> Lifting, Unrestriction, and Substitution \<close>

lemma drop_desr_inv [simp]: "((P \<up> more\<^sub>L\<^sup>2) \<down> more\<^sub>L\<^sup>2) = P"
  by (simp add: ares_aext prod_vwb_lens)

lemma lift_desr_inv:
  fixes P :: "('\<alpha>, '\<beta>) des_rel"
  assumes "$ok\<^sup>< \<sharp> P" "$ok\<^sup>> \<sharp> P"
  shows "((P \<down> more\<^sub>L\<^sup>2) \<up> more\<^sub>L\<^sup>2) = P"
  by (pred_auto assms: assms, (metis (no_types, lifting) des_vars.simps(4) des_vars.surjective)+)

lemma unrest_out_des_lift [unrest]: "out\<alpha> \<sharp> p \<Longrightarrow> out\<alpha> \<sharp> (p \<up> more\<^sub>L\<^sup>2)"
  by (pred_simp)

lemma lift_dist_seq [simp]:
  "(P ;; Q) \<up> more\<^sub>L\<^sup>2 = (P \<up> more\<^sub>L\<^sup>2 ;; Q \<up> more\<^sub>L\<^sup>2)"
  by (pred_auto)

lemma lift_des_skip_dr_unit [simp]:
  "(P \<up> more\<^sub>L\<^sup>2 ;; II \<up> more\<^sub>L\<^sup>2) = P \<up> more\<^sub>L\<^sup>2"
  "(II \<up> more\<^sub>L\<^sup>2 ;; P \<up> more\<^sub>L\<^sup>2) = P \<up> more\<^sub>L\<^sup>2"
  by (pred_auto)+

lemma lift_des_skip_dr_unit_unrest: "$ok\<^sup>> \<sharp> P \<Longrightarrow> (P ;; II \<up> more\<^sub>L\<^sup>2) = P"
  by (pred_auto)

(*
lemma state_subst_design [usubst]:
  "\<lceil>\<sigma> \<oplus>\<^sub>s \<Sigma>\<^sub>D\<rceil>\<^sub>s \<dagger> (P \<turnstile>\<^sub>r Q) = (\<lceil>\<sigma>\<rceil>\<^sub>s \<dagger> P) \<turnstile>\<^sub>r (\<lceil>\<sigma>\<rceil>\<^sub>s \<dagger> Q)"
  by (rel_auto)
*)

lemma get_unrest_subst [usubst_eval]: "\<lbrakk> vwb_lens x; $x \<sharp>\<^sub>s \<sigma> \<rbrakk> \<Longrightarrow> get\<^bsub>x\<^esub> (\<sigma> s) = get\<^bsub>x\<^esub> s"
  by (expr_simp, metis vwb_lens_wb wb_lens.get_put wb_lens_weak weak_lens.view_determination)

lemma design_subst [usubst]:
  "\<lbrakk> $ok\<^sup>< \<sharp>\<^sub>s \<sigma>; $ok\<^sup>> \<sharp>\<^sub>s \<sigma> \<rbrakk> \<Longrightarrow> \<sigma> \<dagger> (P \<turnstile> Q) = (\<sigma> \<dagger> P) \<turnstile> (\<sigma> \<dagger> Q)"
  by (simp add: pred, subst_eval, simp add: subst_app_def)

(*
lemma design_msubst [usubst]:
  "(P(x) \<turnstile> Q(x))\<lbrakk>x\<rightarrow>v\<rbrakk> = (P(x)\<lbrakk>x\<rightarrow>v\<rbrakk> \<turnstile> Q(x)\<lbrakk>x\<rightarrow>v\<rbrakk>)"
  by (rel_auto)
*)
    
lemma design_ok_false [usubst]: "(P \<turnstile> Q)\<lbrakk>False/ok\<^sup><\<rbrakk> = true"
  by pred_auto


lemma ok_pre: "(ok\<^sup>< \<and> pre\<^sub>D(P) \<up> more\<^sub>L\<^sup>2) = (ok\<^sup>< \<and> (\<not> P\<^sup>f))"
  by (pred_auto, (metis (no_types, lifting) des_vars.surjective des_vars.update_convs(1) des_vars.update_convs(2))+)

lemma ok_post: "(ok\<^sup>< \<and> post\<^sub>D(P) \<up> more\<^sub>L\<^sup>2) = (ok\<^sup>< \<and> (P\<^sup>t))"
  by (pred_auto, (smt (z3) des_vars.surjective des_vars.update_convs(1) des_vars.update_convs(2))+)
  
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
  
lemma bot_d_ndes_def [ndes_simp]: "\<bottom>\<^sub>D = (False \<turnstile>\<^sub>n true)"
  by (pred_auto)

lemma design_false_pre: "(false \<turnstile> P) = true"
  by (pred_auto)

lemma rdesign_false_pre: "(false \<turnstile>\<^sub>r P) = true"
  by (pred_auto)

lemma ndesign_false_pre: "(False \<turnstile>\<^sub>n P) = true"
  by (pred_auto)

lemma ndesign_miracle: "(True \<turnstile>\<^sub>n false) = \<top>\<^sub>D"
  by (pred_auto)

lemma top_d_ndes_def [ndes_simp]: "\<top>\<^sub>D = (True \<turnstile>\<^sub>n false)"
  by (pred_auto)

lemma skip_d_alt_def: "II\<^sub>D = true \<turnstile> II"
  by (pred_auto)

lemma skip_d_ndes_def [ndes_simp]: "II\<^sub>D = True \<turnstile>\<^sub>n II"
  by (pred_auto)

lemma design_subst_ok:
  "(P\<lbrakk>True/ok\<^sup><\<rbrakk> \<turnstile> Q\<lbrakk>True/ok\<^sup><\<rbrakk>) = (P \<turnstile> Q)"
  by (pred_auto)

lemma design_subst_ok_ok':
  "(P\<lbrakk>True/ok\<^sup><\<rbrakk> \<turnstile> Q\<lbrakk>True,True/ok\<^sup><,ok\<^sup>>\<rbrakk>) = (P \<turnstile> Q)"
  by pred_auto

lemma design_subst_ok':
  "(P \<turnstile> Q\<lbrakk>True/ok\<^sup>>\<rbrakk>) = (P \<turnstile> Q)"
  by pred_auto

subsection \<open> Sequential Composition Laws \<close>

theorem design_skip_idem [simp]:
  "(II\<^sub>D ;; II\<^sub>D) = II\<^sub>D"
  by (pred_auto)

theorem design_composition_cond:
  assumes
    "out\<alpha> \<sharp> p1" "$ok\<^sup>< \<sharp> P2" "$ok\<^sup>> \<sharp> Q1" "$ok\<^sup>< \<sharp> Q2"
  shows "((p1 \<turnstile> Q1) ;; (P2 \<turnstile> Q2)) = ((p1 \<and> \<not> (Q1 ;; (\<not> P2))) \<turnstile> (Q1 ;; Q2))"
  using assms by (pred_simp, smt)

theorem rdesign_composition_cond:
  assumes "out\<alpha> \<sharp> p1"
  shows "((p1 \<turnstile>\<^sub>r Q1) ;; (P2 \<turnstile>\<^sub>r Q2)) = ((p1 \<and> \<not> (Q1 ;; (\<not> P2))) \<turnstile>\<^sub>r (Q1 ;; Q2))"
  using assms by pred_auto

theorem design_composition_wp:
  fixes p1 p2 :: "'a des_vars_scheme \<Rightarrow> bool"
  assumes
    "$ok \<sharp> p1" "$ok \<sharp> p2"
    "$ok\<^sup>< \<sharp> Q1" "$ok\<^sup>> \<sharp> Q1" "$ok\<^sup>< \<sharp> Q2" "$ok\<^sup>> \<sharp> Q2"
  shows "((p1\<^sup>< \<turnstile> Q1) ;; (p2\<^sup>< \<turnstile> Q2)) = ((p1 \<and> Q1 wlp p2)\<^sup>< \<turnstile> (Q1 ;; Q2))"
  unfolding design_def by (pred_auto assms: assms, metis+)

theorem rdesign_composition_wp:
  "((p1\<^sup>< \<turnstile>\<^sub>r Q1) ;; (p2\<^sup>< \<turnstile>\<^sub>r Q2)) = ((p1 \<and> Q1 wlp p2)\<^sup>< \<turnstile>\<^sub>r (Q1 ;; Q2))"
  by (pred_auto)

theorem design_composition_subst:
  assumes
    "$ok\<^sup>> \<sharp> P1" "$ok\<^sup>< \<sharp> P2"
  shows "((P1 \<turnstile> Q1) ;; (P2 \<turnstile> Q2)) =
         (((\<not> ((\<not> P1) ;; true)) \<and> \<not> (Q1\<lbrakk>True/ok\<^sup>>\<rbrakk> ;; (\<not> P2))) \<turnstile> (Q1\<lbrakk>True/ok\<^sup>>\<rbrakk> ;; Q2\<lbrakk>True/ok\<^sup><\<rbrakk>))"
proof -
  have "((P1 \<turnstile> Q1) ;; (P2 \<turnstile> Q2)) = (\<Sqinter> ok\<^sub>0. ((P1 \<turnstile> Q1)\<lbrakk>\<guillemotleft>ok\<^sub>0\<guillemotright>/ok\<^sup>>\<rbrakk> ;; (P2 \<turnstile> Q2)\<lbrakk>\<guillemotleft>ok\<^sub>0\<guillemotright>/ok\<^sup><\<rbrakk>))"
    by (rule seqr_middle, simp)
  also have " ...
        = (((P1 \<turnstile> Q1)\<lbrakk>False/ok\<^sup>>\<rbrakk> ;; (P2 \<turnstile> Q2)\<lbrakk>False/ok\<^sup><\<rbrakk>)
            \<or> ((P1 \<turnstile> Q1)\<lbrakk>True/ok\<^sup>>\<rbrakk> ;; (P2 \<turnstile> Q2)\<lbrakk>True/ok\<^sup><\<rbrakk>))"
    by (pred_auto; (metis (full_types)))
  also from assms
  have "... = (((ok\<^sup>< \<and> P1 \<longrightarrow> Q1\<lbrakk>True/ok\<^sup>>\<rbrakk>) ;; (P2 \<longrightarrow> ok\<^sup>> \<and> Q2\<lbrakk>True/ok\<^sup><\<rbrakk>)) \<or> ((\<not> (ok\<^sup>< \<and> P1)) ;; true))"
    by (simp add: design_def usubst usubst_eval)
       (pred_auto; blast)
  also have "... = (((\<not>ok\<^sup><)\<^sub>e ;; true\<^sub>h) \<or> ((\<not>P1) ;; true) \<or> (Q1\<lbrakk>True/ok\<^sup>>\<rbrakk> ;; (\<not>P2)) \<or> ((ok\<^sup>>)\<^sub>e \<and> (Q1\<lbrakk>True/ok\<^sup>>\<rbrakk> ;; Q2\<lbrakk>True/ok\<^sup><\<rbrakk>)))"
    by (pred_auto)
  also have "... = (((\<not> ((\<not> P1) ;; true)) \<and> \<not> (Q1\<lbrakk>True/ok\<^sup>>\<rbrakk> ;; (\<not> P2))) \<turnstile> (Q1\<lbrakk>True/ok\<^sup>>\<rbrakk> ;; Q2\<lbrakk>True/ok\<^sup><\<rbrakk>))"
    unfolding design_def by (pred_auto)
  finally show ?thesis .
qed

lemma design_composition:
  assumes "$ok\<^sup>> \<sharp> P1" "$ok\<^sup>< \<sharp> P2" "$ok\<^sup>> \<sharp> Q1" "$ok\<^sup>< \<sharp> Q2"
  shows "((P1 \<turnstile> Q1) ;; (P2 \<turnstile> Q2)) = (((\<not> ((\<not> P1) ;; true)) \<and> \<not> (Q1 ;; (\<not> P2))) \<turnstile> (Q1 ;; Q2))"
  using assms
  by (simp add: design_composition_subst, subst_eval)

theorem rdesign_composition:
  "((P1 \<turnstile>\<^sub>r Q1) ;; (P2 \<turnstile>\<^sub>r Q2)) = (((\<not> ((\<not> P1) ;; true)) \<and> \<not> (Q1 ;; (\<not> P2))) \<turnstile>\<^sub>r (Q1 ;; Q2))"
  by (simp add: rdesign_def design_composition unrest usubst)

theorem ndesign_composition_wlp:
  "(p\<^sub>1 \<turnstile>\<^sub>n Q\<^sub>1) ;; (p\<^sub>2 \<turnstile>\<^sub>n Q\<^sub>2) = (p\<^sub>1 \<and> Q\<^sub>1 wlp p\<^sub>2) \<turnstile>\<^sub>n (Q\<^sub>1 ;; Q\<^sub>2)"
  by (simp add: rdesign_composition unrest, pred_auto)

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

lemma ndesign_Suc_power: "(p \<turnstile>\<^sub>n Q)\<^bold>^ Suc n = ((\<forall> i\<in>{0..\<guillemotleft>n\<guillemotright>}. (Q \<^bold>^ i) wlp p) \<turnstile>\<^sub>n (Q \<^bold>^ Suc n))" 
proof (induct n)
  case 0
  then show ?case 
    by (simp del: SEXP_apply add: wp)
next
  case (Suc n)
  then show ?case
  proof -
    have "p \<turnstile>\<^sub>n Q \<^bold>^ Suc (Suc n) = p \<turnstile>\<^sub>n Q ;; p \<turnstile>\<^sub>n Q \<^bold>^ Suc n"
      by (simp del: SEXP_apply add: upred_semiring.power.power_Suc Suc)
    also have "... = p \<turnstile>\<^sub>n Q ;; (\<forall>i\<in>{0..\<guillemotleft>n\<guillemotright>}. Q \<^bold>^ i wlp p) \<turnstile>\<^sub>n (Q \<^bold>^ Suc n)"
      by (simp only: Suc)
    also have "... = (p \<and> Q wlp (\<forall>i\<in>{0..\<guillemotleft>n\<guillemotright>}. Q \<^bold>^ i wlp p)) \<turnstile>\<^sub>n (Q ;; Q \<^bold>^ Suc n)"
      by (simp add: ndesign_composition_wlp)
    also have "... = (\<forall>i\<in>{0..\<guillemotleft>Suc n\<guillemotright>}. Q \<^bold>^ i wlp p) \<turnstile>\<^sub>n (Q ;; Q \<^bold>^ Suc n)"
    proof -
      have "(p \<and> Q wlp (\<forall>i\<in>{0..\<guillemotleft>n\<guillemotright>}. Q \<^bold>^ i wlp p))\<^sub>e = (p \<and> (\<forall>i\<in>{0..\<guillemotleft>n\<guillemotright>}. Q \<^bold>^ Suc i wlp p))\<^sub>e"
        by (simp add: upred_semiring.power_Suc wp, pred_auto)
      also have "... = (p \<and> (\<forall>i\<in>{1..\<guillemotleft>Suc n\<guillemotright>}. Q \<^bold>^ i wlp p))\<^sub>e"
        by (pred_auto, metis Suc_le_D Suc_le_mono atLeastAtMost_iff least_zero)
      also have "... = (\<forall>i\<in>{0..\<guillemotleft>Suc n\<guillemotright>}. Q \<^bold>^ i wlp p)\<^sub>e"
        by (pred_simp, simp add: atLeast0_atMost_Suc_eq_insert_0 power.power_eq_if)
      finally show ?thesis by simp
    qed
    finally show ?case
      by (metis upred_semiring.power_Suc)
  qed
qed


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
  "pre\<^sub>D(P \<triangleleft> b \<up> des_vars.more\<^sub>L\<^sup>2 \<triangleright> Q) = (pre\<^sub>D(P) \<triangleleft> b \<triangleright> pre\<^sub>D(Q))"
  by (pred_auto)

lemma design_post_condr [simp]:
  shows "post\<^sub>D(P \<triangleleft> b \<up> des_vars.more\<^sub>L\<^sup>2 \<triangleright> Q) = (post\<^sub>D(P) \<triangleleft> b \<triangleright> post\<^sub>D(Q))"
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
  "(p\<^sub>1 \<turnstile>\<^sub>n P\<^sub>2) \<squnion> (q\<^sub>1 \<turnstile>\<^sub>n Q\<^sub>2) = ((p\<^sub>1 \<or> q\<^sub>1) \<turnstile>\<^sub>n ((p\<^sub>1\<^sup>< \<longrightarrow> P\<^sub>2) \<and> (q\<^sub>1\<^sup>< \<longrightarrow> Q\<^sub>2)))"
  by (pred_auto)
    
theorem design_condr:
  "((P\<^sub>1 \<turnstile> P\<^sub>2) \<lhd> b \<rhd> (Q\<^sub>1 \<turnstile> Q\<^sub>2)) = ((P\<^sub>1 \<lhd> b \<rhd> Q\<^sub>1) \<turnstile> (P\<^sub>2 \<lhd> b \<rhd> Q\<^sub>2))"
  by (pred_auto)

theorem ndesign_dcond [ndes_simp]:
  shows "(dcond (p\<^sub>1 \<turnstile>\<^sub>n P\<^sub>2) b (q\<^sub>1 \<turnstile>\<^sub>n Q\<^sub>2)) = ((p\<^sub>1 \<triangleleft> b \<triangleright> q\<^sub>1) \<turnstile>\<^sub>n (P\<^sub>2 \<triangleleft> b\<^sup>< \<triangleright> Q\<^sub>2))"
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

theorem design_refinement:
  assumes
    "$ok\<^sup>< \<sharp> P1" "$ok\<^sup>> \<sharp> P1" "$ok\<^sup>< \<sharp> P2" "$ok\<^sup>> \<sharp> P2"
    "$ok\<^sup>< \<sharp> Q1" "$ok\<^sup>> \<sharp> Q1" "$ok\<^sup>< \<sharp> Q2" "$ok\<^sup>> \<sharp> Q2"
  shows "((P1 \<turnstile> Q1) \<sqsubseteq> (P2 \<turnstile> Q2)) \<longleftrightarrow> `(P1 \<longrightarrow> P2) \<and> (P1 \<and> Q2 \<longrightarrow> Q1)`"
  by (pred_auto assms: assms; metis)

theorem rdesign_refinement:
  "(P1 \<turnstile>\<^sub>r Q1 \<sqsubseteq> P2 \<turnstile>\<^sub>r Q2) \<longleftrightarrow> `P1 \<longrightarrow> P2` \<and> `P1 \<and> Q2 \<longrightarrow> Q1`"
  by (pred_auto)

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


lemma ndesign_refinement: 
  "p1 \<turnstile>\<^sub>n Q1 \<sqsubseteq> p2 \<turnstile>\<^sub>n Q2 \<longleftrightarrow> (`p1 \<longrightarrow> p2` \<and> `p1\<^sup>< \<and> Q2 \<longrightarrow> Q1`)"
  by pred_auto


lemma ndesign_refinement': 
  "p1 \<turnstile>\<^sub>n Q1 \<sqsubseteq> p2 \<turnstile>\<^sub>n Q2 \<longleftrightarrow> (`p1 \<longrightarrow> p2` \<and> Q1 \<sqsubseteq> \<questiondown>p1? ;; Q2)"
  by (simp add: ndesign_refinement, pred_auto)

lemma ndesign_refine_intro:
  assumes "`p1 \<longrightarrow> p2`" "Q1 \<sqsubseteq> \<questiondown>p1? ;; Q2"
  shows "p1 \<turnstile>\<^sub>n Q1 \<sqsubseteq> p2 \<turnstile>\<^sub>n Q2"
  by (simp add: ndesign_refinement' assms)

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