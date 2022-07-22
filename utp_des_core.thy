theory utp_des_core
  imports UTP2.utp_wlp
begin 

alphabet des_vars = 
  ok :: bool

type_synonym ('s\<^sub>1, 's\<^sub>2) des_rel = "('s\<^sub>1 des_vars_scheme, 's\<^sub>2 des_vars_scheme) urel"

definition design where
[pred]: "design P Q = ((ok\<^sup>< \<and> P) \<longrightarrow> (ok\<^sup>> \<and> Q))\<^sub>e"

definition rdesign :: "('s\<^sub>1, 's\<^sub>2) urel \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) urel \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) des_rel" where
[pred]: "rdesign P Q = design (P \<up> more\<^sub>L\<^sup>2) (Q \<up> more\<^sub>L\<^sup>2)"

syntax 
  "_design"  :: "logic \<Rightarrow> logic \<Rightarrow> logic" (infix "\<turnstile>" 85)
  "_rdesign" :: "logic \<Rightarrow> logic \<Rightarrow> logic" (infix "\<turnstile>\<^sub>r" 85)
  "_ndesign" :: "logic \<Rightarrow> logic \<Rightarrow> logic" (infix "\<turnstile>\<^sub>n" 85)

translations 
  "P \<turnstile> Q" == "CONST design P Q"
  "P \<turnstile>\<^sub>r Q" == "CONST rdesign P Q"
  "p \<turnstile>\<^sub>n Q" == "(p\<^sup><)\<^sub>e \<turnstile>\<^sub>r Q"

syntax
  "_svid_des_alpha"  :: "svid" ("\<^bold>v\<^sub>D")

translations
  "_svid_des_alpha" => "CONST des_vars.more\<^sub>L"

lemma "false \<turnstile> true = true"
  by pred_auto

lemma "true \<turnstile> false = (\<not> $ok\<^sup><)\<^sub>e"
  by pred_auto

lemma design_union: "((P\<^sub>1 \<turnstile> Q\<^sub>1) \<or> (P\<^sub>2 \<turnstile> Q\<^sub>2)) = ((P\<^sub>1 \<and> P\<^sub>2) \<turnstile> (Q\<^sub>1 \<or> Q\<^sub>2))"
  by pred_auto

lemma design_cond: "(P\<^sub>1 \<turnstile> Q\<^sub>1) \<lhd> b \<rhd> (P\<^sub>2 \<turnstile> Q\<^sub>2) = (P\<^sub>1 \<lhd> b \<rhd> P\<^sub>2) \<turnstile> (Q\<^sub>1 \<lhd> b \<rhd> Q\<^sub>2)"
  by pred_auto

expr_ctr utrue

definition skip_d :: "('\<alpha>,'\<alpha>) des_rel" ("II\<^sub>D") where 
  [pred]: "II\<^sub>D \<equiv> (true \<turnstile>\<^sub>r II)"

expr_ctr skip_d

definition bot_d :: "('\<alpha>, '\<beta>) des_rel" ("\<bottom>\<^sub>D") where
  [pred]: "\<bottom>\<^sub>D = (false \<turnstile> false)"

expr_ctr bot_d

definition top_d :: "('\<alpha>, '\<beta>) des_rel" ("\<top>\<^sub>D") where
  [pred]: "\<top>\<^sub>D = (true \<turnstile> false)"

expr_ctr top_d

lemma top_d_not_ok:
  "\<top>\<^sub>D = (\<not> ok\<^sup><)\<^sub>e"
  unfolding top_d_def design_def 
  by (expr_simp, simp add: false_pred_def true_pred_def)

definition pre_design :: "('\<alpha>, '\<beta>) des_rel \<Rightarrow> ('\<alpha>, '\<beta>) urel" ("pre\<^sub>D") where
  [pred]: "pre\<^sub>D(P) =  (\<not>P\<lbrakk>True,False/ok\<^sup><,ok\<^sup>>\<rbrakk>) \<down> more\<^sub>L\<^sup>2"

expr_ctr pre_design

definition post_design :: "('\<alpha>, '\<beta>) des_rel \<Rightarrow> ('\<alpha>, '\<beta>) urel" ("post\<^sub>D") where
  [pred]: "post\<^sub>D(P) = P\<lbrakk>True,True/ok\<^sup><,ok\<^sup>>\<rbrakk> \<down> more\<^sub>L\<^sup>2"

expr_ctr post_design

syntax
  "_ok_f"  :: "logic \<Rightarrow> logic" ("_\<^sup>f" [1000] 1000)
  "_ok_t"  :: "logic \<Rightarrow> logic" ("_\<^sup>t" [1000] 1000)

translations
  "P\<^sup>f" \<rightharpoonup> "_subst P (CONST False) (_svid_post (CONST ok))"
  "P\<^sup>t" \<rightharpoonup> "_subst P (CONST True) (_svid_post (CONST ok))"

end