theory SystemF
imports Main SubstHelper
begin

section "Types"

datatype Type =
    TVar var
  | TBool
  | TFun Type Type (infixl "\<rightarrow>" 60)
  | TAll Type ("\<forall>")

abbreviation extr :: "Renaming \<Rightarrow> Renaming" where
  "extr \<rho> \<equiv> 0 \<bullet> \<Up>\<^sub>r \<rho>"

fun rename\<^sub>t :: "Renaming \<Rightarrow> Type \<Rightarrow> Type" where
  "rename\<^sub>t \<rho> (TVar x) = TVar (\<rho> x)" |
  "rename\<^sub>t \<rho> TBool = TBool" |
  "rename\<^sub>t \<rho> (A \<rightarrow> B) = (rename\<^sub>t \<rho> A) \<rightarrow> (rename\<^sub>t \<rho> B)" |
  "rename\<^sub>t \<rho> (\<forall> A) = \<forall> (rename\<^sub>t (extr \<rho>) A)"

type_synonym Subst\<^sub>t = "var \<Rightarrow> Type"

definition id\<^sub>t :: "Subst\<^sub>t" where
  "id\<^sub>t x \<equiv> TVar x"

definition lift_sub\<^sub>t :: "Subst\<^sub>t \<Rightarrow> Subst\<^sub>t" ("\<Up>\<^sub>t") where
  "\<Up>\<^sub>t \<sigma> x \<equiv> rename\<^sub>t Suc (\<sigma> x)"

abbreviation ext\<^sub>t :: "Subst\<^sub>t \<Rightarrow> Subst\<^sub>t" where
  "ext\<^sub>t \<sigma> \<equiv> TVar 0 \<bullet> \<Up>\<^sub>t \<sigma>"

fun sub\<^sub>t :: "Subst\<^sub>t \<Rightarrow> Type \<Rightarrow> Type" where
  "sub\<^sub>t \<sigma> (TVar x) = \<sigma> x" |
  "sub\<^sub>t \<sigma> TBool = TBool" |
  "sub\<^sub>t \<sigma> (A \<rightarrow> B) = (sub\<^sub>t \<sigma> A) \<rightarrow> (sub\<^sub>t \<sigma> B)" |
  "sub\<^sub>t \<sigma> (\<forall> A) = \<forall> (sub\<^sub>t (ext\<^sub>t \<sigma>) A)"

definition ren\<^sub>t :: "Renaming \<Rightarrow> Subst\<^sub>t" where
  "ren\<^sub>t \<rho> x \<equiv> TVar (\<rho> x)"

definition seq\<^sub>t :: "Subst\<^sub>t \<Rightarrow> Subst\<^sub>t \<Rightarrow> Subst\<^sub>t" (infixr ";\<^sub>t" 70) where
  "(\<sigma> ;\<^sub>t \<tau>) x \<equiv> sub\<^sub>t \<tau> (\<sigma> x)"

interpretation type_sub: subst1 TVar lift_sub\<^sub>t sub\<^sub>t ren\<^sub>t seq\<^sub>t
  apply unfold_locales
    apply (simp add: ren\<^sub>t_def)
   apply (simp add: seq\<^sub>t_def)
  apply (simp add: lift_sub\<^sub>t_def ren\<^sub>t_def)
  done

lemma rename_sub_ren: "rename\<^sub>t \<rho> A = sub\<^sub>t (ren\<^sub>t \<rho>) A"
  by (induction A arbitrary: \<rho>) (auto simp add: ren\<^sub>t_def)

lemma lift_def: "\<Up>\<^sub>t \<sigma> x = sub\<^sub>t (ren\<^sub>t Suc) (\<sigma> x)"
  using rename_sub_ren ren\<^sub>t_def lift_sub\<^sub>t_def by simp

interpretation type_sub: subst2 TVar lift_sub\<^sub>t sub\<^sub>t ren\<^sub>t seq\<^sub>t
  apply unfold_locales
  using lift_def apply blast
  apply simp
  done

lemma ren_sub\<^sub>t: "sub\<^sub>t \<tau> (sub\<^sub>t (ren\<^sub>t \<rho>) A) = sub\<^sub>t (ren\<^sub>t \<rho> ;\<^sub>t \<tau>) A"
proof (induction A arbitrary: \<tau> \<rho>)
case (TVar x)
then show ?case by (simp add: seq\<^sub>t_def)
next
case TBool
  then show ?case by simp
next
  case (TFun A B)
  then show ?case by simp
next
  case (TAll A)
  from TAll have "sub\<^sub>t (ext\<^sub>t \<tau>) (sub\<^sub>t (ren\<^sub>t (extr \<rho>)) A) 
               = sub\<^sub>t (ren\<^sub>t (extr \<rho>) ;\<^sub>t (ext\<^sub>t \<tau>)) A" by blast
  then show ?case by simp
qed

interpretation interp_sub: subst3 TVar lift_sub\<^sub>t sub\<^sub>t ren\<^sub>t seq\<^sub>t
  apply unfold_locales
  using ren_sub\<^sub>t apply fast
  done

lemma sub_ren\<^sub>t: "sub\<^sub>t (ren\<^sub>t \<rho>) (sub\<^sub>t \<sigma> A) = sub\<^sub>t (\<sigma> ;\<^sub>t ren\<^sub>t \<rho>) A"
proof (induction A arbitrary: \<sigma> \<rho>)
case (TVar x)
  then show ?case by (simp add: seq\<^sub>t_def)
next
  case TBool
  then show ?case by simp
next
  case (TFun A B)
  then show ?case by simp
next
  case (TAll A)
  from TAll have "sub\<^sub>t (ren\<^sub>t (extr \<rho>)) (sub\<^sub>t (ext\<^sub>t \<sigma>) A) 
                = sub\<^sub>t ((ext\<^sub>t \<sigma>) ;\<^sub>t ren\<^sub>t (extr \<rho>)) A" by fast 
  then show ?case by simp
qed

interpretation type_sub: subst4 TVar lift_sub\<^sub>t sub\<^sub>t ren\<^sub>t seq\<^sub>t
  apply unfold_locales using sub_ren\<^sub>t apply fast done

lemma sub_sub\<^sub>t[simp]: "sub\<^sub>t \<tau> (sub\<^sub>t \<sigma> A) = sub\<^sub>t (\<sigma> ;\<^sub>t \<tau>) A"
proof (induction A arbitrary: \<sigma> \<tau>)
case (TVar x)
then show ?case by (simp add: seq\<^sub>t_def)
next
case TBool
  then show ?case by simp
next
  case (TFun A B)
  then show ?case by simp
next
  case (TAll A)
  from TAll have IH: "sub\<^sub>t (ext\<^sub>t \<tau>) (sub\<^sub>t (ext\<^sub>t \<sigma>) A) = sub\<^sub>t ((ext\<^sub>t \<sigma>) ;\<^sub>t (ext\<^sub>t \<tau>)) A" by fast
  from IH show ?case using type_sub.exts_seq by simp
qed

interpretation type_sub: subst5 TVar lift_sub\<^sub>t sub\<^sub>t ren\<^sub>t seq\<^sub>t id\<^sub>t 
  apply unfold_locales using sub_sub\<^sub>t apply fast using id\<^sub>t_def apply fast
  done

abbreviation up :: Subst\<^sub>t ("\<up>\<^sub>t") where
  "\<up>\<^sub>t \<equiv> ren\<^sub>t Suc"

definition extt :: "Subst\<^sub>t \<Rightarrow> Subst\<^sub>t" where
  "extt \<sigma> \<equiv> TVar 0 \<bullet> (\<sigma> ;\<^sub>t \<up>\<^sub>t)"
declare extt_def[simp]

lemma sub\<^sub>t_id[simp]: "sub\<^sub>t id\<^sub>t A = A"
  apply (induction A) 
    apply (simp add: id\<^sub>t_def)
   apply simp
   apply simp
  apply simp
  done

interpretation interp_sub: subst6 TVar lift_sub\<^sub>t sub\<^sub>t ren\<^sub>t seq\<^sub>t id\<^sub>t extt
  apply unfold_locales unfolding extt_def apply auto done

abbreviation subst_one\<^sub>t :: "Type \<Rightarrow> Type \<Rightarrow> Type" ("_[_]\<^sub>t" 70) where
  "subst_one\<^sub>t A B \<equiv> sub\<^sub>t (B \<bullet> id\<^sub>t) A"


section "Terms"

datatype Term =
  Var var
  | App Term Term (infixl "\<cdot>" 70)
  | Lam Term      ("\<lambda>")
  | TLam Term     ("\<Lambda>")
  | TApp Term Type




end