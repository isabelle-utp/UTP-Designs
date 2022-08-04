theory utp_des_core
  imports UTP2.utp_wlp
begin 

alphabet des_vars = 
  ok :: bool

type_synonym ('s\<^sub>1, 's\<^sub>2) des_rel = "('s\<^sub>1 des_vars_scheme, 's\<^sub>2 des_vars_scheme) urel"
type_synonym ('s\<^sub>1) des_hrel = "('s\<^sub>1, 's\<^sub>1) des_rel"

syntax
  "_svid_des_alpha"  :: "svid" ("\<^bold>v\<^sub>D")

translations
  "_svid_des_alpha" => "CONST des_vars.more\<^sub>L"

text \<open> The following notations define liftings from non-design predicates into design
  predicates using alphabet extensions. \<close>

abbreviation lift_desr ("\<lceil>_\<rceil>\<^sub>D")
where "\<lceil>P\<rceil>\<^sub>D \<equiv> P \<up> (\<^bold>v\<^sub>D \<times> \<^bold>v\<^sub>D)"

expr_ctr lift_desr

abbreviation lift_pre_desr ("\<lceil>_\<rceil>\<^sub>D\<^sub><")
where "\<lceil>p\<rceil>\<^sub>D\<^sub>< \<equiv> \<lceil>p\<^sup><\<rceil>\<^sub>D"

expr_ctr lift_pre_desr

abbreviation lift_post_desr ("\<lceil>_\<rceil>\<^sub>D\<^sub>>")
where "\<lceil>p\<rceil>\<^sub>D\<^sub>> \<equiv> \<lceil>p\<^sup>>\<rceil>\<^sub>D"

abbreviation drop_desr ("\<lfloor>_\<rfloor>\<^sub>D")
where "\<lfloor>P\<rfloor>\<^sub>D \<equiv> P \<down> (\<^bold>v\<^sub>D \<times> \<^bold>v\<^sub>D)"

abbreviation dcond :: "('\<alpha>, '\<beta>) des_rel \<Rightarrow> '\<alpha> pred \<Rightarrow> ('\<alpha>, '\<beta>) des_rel \<Rightarrow> ('\<alpha>, '\<beta>) des_rel" 
where "dcond P b Q \<equiv> P \<triangleleft> \<lceil>b\<rceil>\<^sub>D\<^sub>< \<triangleright> Q"

syntax "_dcond" :: "logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("(3_ \<triangleleft> _ \<triangleright>\<^sub>D/ _)" [52,0,53] 52)
translations "_dcond P b Q" == "CONST dcond P (b)\<^sub>e Q"

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