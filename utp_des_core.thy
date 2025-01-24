section \<open> Design Signature and Core Laws \<close>

theory utp_des_core
  imports UTP2.utp
begin 

text \<open> UTP designs~\cite{Cavalcanti04,Hoare&98} are a subset of the alphabetised relations that
  use a boolean observational variable $ok$ to record the start and termination of a program. For 
  more information on designs please see Chapter 3 of the UTP book~\cite{Hoare&98}, or
  the more accessible designs tutorial~\cite{Cavalcanti04}. \<close>

alphabet des_vars = 
  ok :: bool

type_synonym ('s\<^sub>1, 's\<^sub>2) des_rel = "('s\<^sub>1 des_vars_scheme, 's\<^sub>2 des_vars_scheme) urel"
type_synonym 's des_hrel = "('s, 's) des_rel"

notation des_vars.more\<^sub>L ("\<^bold>v\<^sub>D")

syntax
  "_svid_des_alpha"  :: "svid" ("\<^bold>v\<^sub>D")

translations
  "_svid_des_alpha" => "CONST des_vars.more\<^sub>L"

text \<open> Define the lens functor for designs \<close>
  
definition lmap_des_vars :: "('\<alpha> \<Longrightarrow> '\<beta>) \<Rightarrow> ('\<alpha> des_vars_scheme \<Longrightarrow> '\<beta> des_vars_scheme)" ("lmap\<^sub>D")
where [lens_defs]: "lmap_des_vars = lmap[des_vars]"

syntax "_lmap_des_vars" :: "svid \<Rightarrow> svid" ("lmap\<^sub>D[_]")
translations "_lmap_des_vars a" => "CONST lmap_des_vars a"

lemma lmap_des_vars: "vwb_lens f \<Longrightarrow> vwb_lens (lmap_des_vars f)"
  by (unfold_locales, auto simp add: lens_defs alpha_defs)

lemma lmap_id: "lmap\<^sub>D 1\<^sub>L = 1\<^sub>L"
  by (simp add: lens_defs alpha_defs fun_eq_iff)

lemma lmap_comp: "lmap\<^sub>D (f ;\<^sub>L g) = lmap\<^sub>D f ;\<^sub>L lmap\<^sub>D g"
  by (simp add: lens_defs alpha_defs fun_eq_iff)

text \<open> The following notations define liftings from non-design predicates into design
  predicates using alphabet extensions. \<close>

abbreviation lift_desr ("\<lceil>_\<rceil>\<^sub>D")
where "\<lceil>P\<rceil>\<^sub>D \<equiv> P \<up> (\<^bold>v\<^sub>D \<times> \<^bold>v\<^sub>D)"

expr_constructor lift_desr

abbreviation lift_pre_desr ("\<lceil>_\<rceil>\<^sub>D\<^sub><")
where "\<lceil>p\<rceil>\<^sub>D\<^sub>< \<equiv> \<lceil>p\<^sup><\<rceil>\<^sub>D"

expr_constructor lift_pre_desr

abbreviation lift_post_desr ("\<lceil>_\<rceil>\<^sub>D\<^sub>>")
where "\<lceil>p\<rceil>\<^sub>D\<^sub>> \<equiv> \<lceil>p\<^sup>>\<rceil>\<^sub>D"

abbreviation drop_desr ("\<lfloor>_\<rfloor>\<^sub>D")
where "\<lfloor>P\<rfloor>\<^sub>D \<equiv> P \<down> (\<^bold>v\<^sub>D \<times> \<^bold>v\<^sub>D)"

abbreviation dcond :: "('\<alpha>, '\<beta>) des_rel \<Rightarrow> '\<alpha> pred \<Rightarrow> ('\<alpha>, '\<beta>) des_rel \<Rightarrow> ('\<alpha>, '\<beta>) des_rel" 
where "dcond P b Q \<equiv> P \<lhd> (b \<up> \<^bold>v\<^sub>D) \<rhd> Q"

syntax "_dcond" :: "logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("(3_ \<triangleleft> _ \<triangleright>\<^sub>D/ _)" [52,0,53] 52)
translations "_dcond P b Q" == "CONST dcond P (b)\<^sub>e Q"

definition design where
[pred]: "design P Q = ((ok\<^sup>< \<and> P) \<longrightarrow> (ok\<^sup>> \<and> Q))"

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

expr_constructor skip_d

definition bot_d :: "('\<alpha>, '\<beta>) des_rel" ("\<bottom>\<^sub>D") where
  [pred]: "\<bottom>\<^sub>D = (false \<turnstile> false)"

expr_constructor bot_d

definition top_d :: "('\<alpha>, '\<beta>) des_rel" ("\<top>\<^sub>D") where
  [pred]: "\<top>\<^sub>D = (true \<turnstile> false)"

expr_constructor top_d

lemma top_d_not_ok:
  "\<top>\<^sub>D = (\<not> ok\<^sup><)\<^sub>e"
  unfolding top_d_def design_def 
  by (pred_simp)

definition pre_design :: "('\<alpha>, '\<beta>) des_rel \<Rightarrow> ('\<alpha>, '\<beta>) urel" ("pre\<^sub>D") where
  [pred]: "pre\<^sub>D(P) =  (\<not>P\<lbrakk>True,False/ok\<^sup><,ok\<^sup>>\<rbrakk>) \<down> more\<^sub>L\<^sup>2"

expr_constructor pre_design

definition post_design :: "('\<alpha>, '\<beta>) des_rel \<Rightarrow> ('\<alpha>, '\<beta>) urel" ("post\<^sub>D") where
  [pred]: "post\<^sub>D(P) = P\<lbrakk>True,True/ok\<^sup><,ok\<^sup>>\<rbrakk> \<down> more\<^sub>L\<^sup>2"

expr_constructor post_design

syntax
  "_ok_f"  :: "logic \<Rightarrow> logic" ("_\<^sup>f" [1000] 1000)
  "_ok_t"  :: "logic \<Rightarrow> logic" ("_\<^sup>t" [1000] 1000)

translations
  "P\<^sup>f" \<rightharpoonup> "_subst P (CONST False) (_svid_post (CONST ok))"
  "P\<^sup>t" \<rightharpoonup> "_subst P (CONST True) (_svid_post (CONST ok))"

lemma state_subst_design [usubst]:
  "(\<sigma> \<up>\<^sub>s \<^bold>v\<^sub>D\<^sup><) \<dagger> (P \<turnstile>\<^sub>r Q) = ((\<sigma> \<up>\<^sub>s \<^bold>v\<^sup><) \<dagger> P) \<turnstile>\<^sub>r ((\<sigma> \<up>\<^sub>s \<^bold>v\<^sup><) \<dagger> Q)"
  by (pred_auto)

end