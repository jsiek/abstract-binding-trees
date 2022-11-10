theory LambdaExample
 imports Main AbstractBindingTrees
begin

section "Lambda Calculus"

datatype op_lam =
  LamOp | AppOp

type_synonym Term = "op_lam ABT"

abbreviation Lam :: "Term \<Rightarrow> Term" ("\<lambda>") where 
  "\<lambda> N \<equiv> App LamOp [Bnd (Trm N)]"

abbreviation Apply :: "Term \<Rightarrow> Term \<Rightarrow> Term" (infixl "\<cdot>" 60) where
  "L \<cdot> M \<equiv> App AppOp [Trm L, Trm M]"

inductive reduce :: "Term \<Rightarrow> Term \<Rightarrow> bool" (infix "\<longmapsto>" 50) where
  beta: "(\<lambda> N) \<cdot> M \<longmapsto> N[M]"


end