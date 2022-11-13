theory Experiment3
  imports Main SubstHelper
begin

datatype Term =
    Var var
    | App Term Term (infixl "\<cdot>" 70)
    | Lam Term      ("\<lambda>")

abbreviation extr :: "Renaming \<Rightarrow> Renaming" where
  "extr \<rho> \<equiv> 0 \<bullet> \<Up>\<^sub>r \<rho>"

fun rename :: "Renaming \<Rightarrow> Term \<Rightarrow> Term" where
  "rename \<rho> (Var x) = Var (\<rho> x)" |
  "rename \<rho> (L \<cdot> M) = (rename \<rho> L) \<cdot> (rename \<rho> M)" |
  "rename \<rho> (\<lambda> N) = \<lambda> (rename (extr \<rho>) N)"

type_synonym Subst = "var \<Rightarrow> Term"

definition ids :: "Subst" where
  "ids x \<equiv> Var x"

definition lift_sub :: "Subst \<Rightarrow> Subst" ("\<Up>") where
  "\<Up> \<sigma> x \<equiv> rename Suc (\<sigma> x)"

abbreviation exts :: "Subst \<Rightarrow> Subst" where
  "exts \<sigma> \<equiv> Var 0 \<bullet> \<Up> \<sigma>"

fun sub :: "Subst \<Rightarrow> Term \<Rightarrow> Term" where
  "sub \<sigma> (Var x) = \<sigma> x" |
  "sub \<sigma> (L \<cdot> M) = (sub \<sigma> L) \<cdot> (sub \<sigma> M)" |
  "sub \<sigma> (\<lambda> N) = \<lambda> (sub (exts \<sigma>) N)"

definition ren :: "Renaming \<Rightarrow> Subst" where
  "ren \<rho> x \<equiv> Var (\<rho> x)"

definition seq :: "Subst \<Rightarrow> Subst \<Rightarrow> Subst" (infixr ";" 70) where
  "(\<sigma> ; \<tau>) x \<equiv> sub \<tau> (\<sigma> x)"

interpretation interp_sub: subst1 Var lift_sub sub ren seq
  apply unfold_locales
  apply (simp add: ren_def)
  apply (simp add: seq_def)
   apply (simp add: lift_sub_def ren_def)
  done

lemma rename_sub_ren: "rename \<rho> M = sub (ren \<rho>) M"
  by (induction M arbitrary: \<rho>) (auto simp add: ren_def)

lemma lift_def: "\<Up> \<sigma> x = sub (ren Suc) (\<sigma> x)"
  using rename_sub_ren ren_def lift_sub_def by simp

interpretation interp_sub: subst2 Var lift_sub sub ren seq
  apply unfold_locales
  using lift_def apply blast
  apply simp
  done

lemma ren_sub: "sub \<tau> (sub (ren \<rho>) M) = sub (ren \<rho> ; \<tau>) M"
proof (induction M arbitrary: \<tau> \<rho>)
  case (Var x)
  then show ?case by (simp add: seq_def)
next
  case (App L M)
  then show ?case by simp
next
  case (Lam N)
  from Lam have "sub (exts \<tau>) (sub (ren (extr \<rho>)) N) 
               = sub (ren (extr \<rho>) ; (exts \<tau>)) N" by blast
  then show ?case by simp
qed

interpretation interp_sub: subst3 Var lift_sub sub ren seq
  apply unfold_locales
  using ren_sub apply fast
  done

lemma sub_ren: "sub (ren \<rho>) (sub \<sigma> M) = sub (\<sigma> ; ren \<rho>) M"
proof (induction M arbitrary: \<sigma> \<rho>)
  case (Var x)
  then show ?case by (simp add: seq_def)
next
  case (App L M)
  then show ?case by simp
next
  case (Lam N)
  from Lam have "sub (ren (extr \<rho>)) (sub (exts \<sigma>) N) 
               = sub ((exts \<sigma>) ; ren (extr \<rho>)) N" by fast 
  then show ?case by simp
qed

interpretation interp_sub: subst4 Var lift_sub sub ren seq
  apply unfold_locales using sub_ren apply fast done

lemma sub_sub[simp]: "sub \<tau> (sub \<sigma> M) = sub (\<sigma> ; \<tau>) M"
proof (induction M arbitrary: \<sigma> \<tau>)
  case (Var x)
  then show ?case by (simp add: seq_def)
next
  case (Lam N)
  let ?S = "Var 0 \<bullet> \<Up> \<sigma>" and ?T = "Var 0 \<bullet> \<Up> \<tau>"
  from Lam have IH: "sub ?T (sub ?S N) = sub (?S ; ?T) N" by fast
  from IH show ?case using interp_sub.exts_seq by simp
next
  case (App L M)
  then show ?case by simp
qed

interpretation interp_sub: subst5 Var lift_sub sub ren seq ids 
  apply unfold_locales using sub_sub apply fast using ids_def apply fast
  done

abbreviation up :: Subst ("\<up>") where
  "\<up> \<equiv> ren Suc"

definition ext :: "Subst \<Rightarrow> Subst" where
  "ext \<sigma> \<equiv> Var 0 \<bullet> (\<sigma> ; \<up>)"
declare ext_def[simp]

lemma sub_id[simp]: "sub ids M = M"
  apply (induction M)
    apply (simp add: ids_def)
   apply simp
  apply simp
  done

interpretation interp_sub: subst6 Var lift_sub sub ren seq ids ext
  apply unfold_locales unfolding ext_def apply auto done

abbreviation subst_one :: "Term \<Rightarrow> Term \<Rightarrow> Term" ("_[_]" 70) where
  "subst_one N M \<equiv> sub (M \<bullet> ids) N"
abbreviation subst_two :: "Term \<Rightarrow> Term \<Rightarrow> Term" ("_\<lbrace>_\<rbrace>" 60) where
 "N \<lbrace> M \<rbrace> \<equiv> sub (ext (M \<bullet> ids)) N"


end