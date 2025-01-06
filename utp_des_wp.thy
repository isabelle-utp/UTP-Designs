section \<open> Design Weakest Preconditions \<close>

theory utp_des_wp
  imports utp_des_prog utp_des_hoare
begin

term "pre\<^sub>D(Q) ;; true"

term "ares ((pre\<^sub>D(Q) ;; true) :: ('\<alpha>, '\<beta>) urel) fst\<^sub>L"

definition wp_design :: "('\<alpha>, '\<beta>) des_rel \<Rightarrow> '\<beta> pred \<Rightarrow> '\<alpha> pred" (infix "wp\<^sub>D" 60) where
[pred]: "Q wp\<^sub>D r = ((pre\<^sub>D(Q) ;; true :: ('\<alpha>, '\<beta>) urel) \<down> \<^bold>v\<^sup>< \<and> (post\<^sub>D(Q) wlp r))"

text \<open> If two normal designs have the same weakest precondition for any given postcondition, then
  the two designs are equivalent. \<close>

theorem wpd_eq_intro: "\<lbrakk> \<And> r. (p\<^sub>1 \<turnstile>\<^sub>n Q\<^sub>1) wp\<^sub>D r = (p\<^sub>2 \<turnstile>\<^sub>n Q\<^sub>2) wp\<^sub>D r \<rbrakk> \<Longrightarrow> (p\<^sub>1 \<turnstile>\<^sub>n Q\<^sub>1) = (p\<^sub>2 \<turnstile>\<^sub>n Q\<^sub>2)"
  by (pred_simp, metis curry_conv)

theorem wpd_H3_eq_intro: "\<lbrakk> P is H1_H3; Q is H1_H3; \<And> r. P wp\<^sub>D r = Q wp\<^sub>D r \<rbrakk> \<Longrightarrow> P = Q"
  by (metis H1_H3_commute H1_H3_is_normal_design H3_idem Healthy_def' wpd_eq_intro)

lemma wp_d_abort [wp]: "true wp\<^sub>D p = false"
  by (pred_auto)

lemma wp_assigns_d [wp]: "\<langle>\<sigma>\<rangle>\<^sub>D wp\<^sub>D r = \<sigma> \<dagger> r"
  by (pred_auto)

theorem rdesign_wp [wp]:
  "(p\<^sup>< \<turnstile>\<^sub>r Q) wp\<^sub>D r = (p \<and> Q wlp r)"
  by pred_auto

theorem ndesign_wp [wp]:
  "(p \<turnstile>\<^sub>n Q) wp\<^sub>D r = (p \<and> Q wlp r)"
  by (metis ndesign_pre rdesign_pre rdesign_wp)

theorem wpd_seq_r:
  fixes Q1 Q2 :: "'\<alpha> hrel"
  shows "((p1\<^sup>< \<turnstile>\<^sub>r Q1) ;; (p2\<^sup>< \<turnstile>\<^sub>r Q2)) wp\<^sub>D r = (p1\<^sup>< \<turnstile>\<^sub>r Q1) wp\<^sub>D ((p2\<^sup>< \<turnstile>\<^sub>r Q2) wp\<^sub>D r)"
  by (pred_auto)

theorem wpnd_seq_r [wp]:
  fixes Q1 Q2 :: "'\<alpha> hrel"
  shows "((p1 \<turnstile>\<^sub>n Q1) ;; (p2 \<turnstile>\<^sub>n Q2)) wp\<^sub>D r = (p1 \<turnstile>\<^sub>n Q1) wp\<^sub>D ((p2 \<turnstile>\<^sub>n Q2) wp\<^sub>D r)"
  by (metis ndesign_pre rdesign_pre wpd_seq_r)

theorem wpd_seq_r_H1_H3 [wp]:
  fixes P Q :: "'\<alpha> des_hrel"
  assumes "P is \<^bold>N" "Q is \<^bold>N"
  shows "(P ;; Q) wp\<^sub>D r = P wp\<^sub>D (Q wp\<^sub>D r)"
  by (metis H1_H3_commute H1_H3_is_normal_design H1_idem Healthy_def' assms(1) assms(2) wpnd_seq_r)

theorem wp_hoare_d_link:
  assumes "Q is \<^bold>N"
  shows "{p}Q{r}\<^sub>D \<longleftrightarrow> (Q wp\<^sub>D r \<sqsubseteq> p)"
  by (ndes_simp cls: assms, pred_auto)

end