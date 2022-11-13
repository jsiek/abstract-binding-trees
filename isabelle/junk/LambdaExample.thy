theory LambdaExample
 imports Main AbstractBindingTrees
begin

section "Lambda Calculus"

datatype op_lam = LamOp | AppOp

type_synonym Term = "op_lam ABT"

abbreviation Lam :: "Term \<Rightarrow> Term" ("\<lambda>") where 
  "\<lambda> N \<equiv> App LamOp [Bnd (Trm N)]"

abbreviation Apply :: "Term \<Rightarrow> Term \<Rightarrow> Term" (infixl "\<cdot>" 60) where
  "L \<cdot> M \<equiv> App AppOp [Trm L, Trm M]"

inductive WF_op :: "op_lam \<Rightarrow> unit list list \<Rightarrow> unit list \<Rightarrow> unit \<Rightarrow> bool" where
  WFLamOp[intro!]: "WF_op LamOp [[()]] [()] ()" |
  WFAppOp[intro!]: "WF_op AppOp [[],[]] [(),()] ()"

context abt_predicate
begin

inductive_cases
  wf_var_elim[elim!]: "\<Gamma> \<turnstile> Var x : T" and
  wf_app_elim[elim!]: "\<Gamma> \<turnstile> App op args : T" and
  wf_trm_elim[elim!]: "\<Gamma>; Bs \<turnstile>\<^sub>a Trm M : T" and
  wf_bnd_elim[elim!]: "\<Gamma>; Bs \<turnstile>\<^sub>a Bnd A : T" and
  wf_cons_elim[elim!]: "\<Gamma>; Bss \<turnstile>\<^sub>+ As : Ts"

end

interpretation lam: abt_predicate WF_op .

abbreviation WF :: "unit list \<Rightarrow> Term \<Rightarrow> bool" ("_\<turnstile>_") where
  "\<Gamma> \<turnstile> M \<equiv> lam.wf_abt \<Gamma> M ()"

inductive wf :: "unit list \<Rightarrow> Term \<Rightarrow> bool" where
  wf_var[intro!]: "nth \<Gamma> x = () \<Longrightarrow> wf \<Gamma> (Var x)" |
  wf_app[intro!]: "\<lbrakk> wf \<Gamma> L; wf \<Gamma> M \<rbrakk> \<Longrightarrow> wf \<Gamma> (L \<cdot> M)" |
  wf_abs[intro!]: "wf (()#\<Gamma>) N \<Longrightarrow> wf \<Gamma> (\<lambda> N)"

lemma wf_implies_WF: "wf \<Gamma> M \<Longrightarrow> \<Gamma> \<turnstile> M"
  by (induction \<Gamma> M rule: wf.induct) auto

thm ABT.induct
thm wf.induct
thm lam.wf_abt_wf_args_wf_arg.induct

lemma WF_implies_wf: "\<Gamma> \<turnstile> M \<longrightarrow> wf \<Gamma> M"
  apply (induction \<Gamma> M rule: lam.wf_abt_wf_args_wf_arg.induct)
  sorry

inductive reduce :: "Term \<Rightarrow> Term \<Rightarrow> bool" (infix "\<longmapsto>" 50) where
  beta[intro!]: "(\<lambda> N) \<cdot> M \<longmapsto> N[M]" |
  appl[intro!]: "L \<longmapsto> L' \<Longrightarrow> L \<cdot> M \<longmapsto> L' \<cdot> M" |
  appr[intro!]: "M \<longmapsto> M' \<Longrightarrow> L \<cdot> M \<longmapsto> L \<cdot> M'" |
  abs[intro!]: "N \<longmapsto> N' \<Longrightarrow> \<lambda> N \<longmapsto> \<lambda> N'"

lemma reduce_WF: "\<lbrakk> M \<longmapsto> N; \<Gamma> \<turnstile> M \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> N"
proof (induction arbitrary: \<Gamma> rule: reduce.induct)
  case (beta N M)
  have 1: "\<Gamma> \<turnstile> M" using beta by auto
  have 2: "()#\<Gamma> \<turnstile> N" using beta by auto
  from 1 2 show ?case apply auto apply (rule lam.subst_pres) apply force 
    unfolding lam.sub_pres_def \<iota>_def apply auto apply (case_tac x) apply auto done 
next
  case (appl L L' M)
  then show ?case by auto
next
  case (appr M M' L)
  then show ?case by auto
next
  case (abs N N' \<Gamma>)
  have "()#\<Gamma> \<turnstile> N" using abs by auto
  then have "()#\<Gamma> \<turnstile> N'" using abs by blast
  then show ?case by auto
qed


section "Confluence"

inductive reduce_parallel :: "Term \<Rightarrow> Term \<Rightarrow> bool" (infix "\<Down>" 50) where
  pvar[intro!]: "Var x \<Down> Var x" |
  pabs[intro!]: "N \<Down> N' \<Longrightarrow> \<lambda> N \<Down> \<lambda> N'" |
  papp[intro!]: "\<lbrakk> L \<Down> L'; M \<Down> M' \<rbrakk> \<Longrightarrow> L \<cdot> M \<Down> L' \<cdot> M'" |
  pbeta[intro!]: "\<lbrakk> N \<Down> N'; M \<Down> M' \<rbrakk> \<Longrightarrow> (\<lambda> N) \<cdot> M \<Down> N'[M']"

(*
lemma parallel_refl: "\<Gamma> \<turnstile> M \<Longrightarrow> M \<Down> M"
  by (induction rule: WF.induct) auto
*)

lemma beta_parallel: "M \<longmapsto> N \<Longrightarrow> M \<Down> N"
  apply (induction rule: reduce.induct)
  sorry

end