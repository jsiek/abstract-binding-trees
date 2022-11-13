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

lemma rename_sub_ren\<^sub>t: "rename\<^sub>t \<rho> A = sub\<^sub>t (ren\<^sub>t \<rho>) A"
  by (induction A arbitrary: \<rho>) (auto simp add: ren\<^sub>t_def)

lemma lift_def\<^sub>t: "\<Up>\<^sub>t \<sigma> x = sub\<^sub>t (ren\<^sub>t Suc) (\<sigma> x)"
  using rename_sub_ren\<^sub>t ren\<^sub>t_def lift_sub\<^sub>t_def by simp

interpretation type_sub: subst2 TVar lift_sub\<^sub>t sub\<^sub>t ren\<^sub>t seq\<^sub>t
  apply unfold_locales
  using lift_def\<^sub>t apply blast
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

inductive wft :: "nat \<Rightarrow> Type \<Rightarrow> bool" where
  wft_var[intro!]: "x < n \<Longrightarrow> wft n (TVar x)" |
  wft_bool[intro!]: "wft n TBool" |
  wft_fun[intro!]: "\<lbrakk> wft n A; wft n B \<rbrakk> \<Longrightarrow> wft n (A \<rightarrow> B)" |
  wft_all[intro!]: "wft (Suc n) A \<Longrightarrow> wft n (\<forall> A)"

inductive_cases
  wftvar[elim!]: "wft n (TVar x)" and
  wftfun[elim!]: "wft n (A \<rightarrow> B)" and
  wftall[elim!]: "wft n (\<forall> A)" 

definition wf_ren\<^sub>t :: "Renaming \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "wf_ren\<^sub>t \<rho> \<Gamma> \<Gamma>' \<equiv> \<forall> x. x < \<Gamma> \<longrightarrow> \<rho> x < \<Gamma>'"
declare wf_ren\<^sub>t_def[simp]

(* Node: need equations about renaming! *)
lemma ext_wf_rent: assumes 1: "wf_ren\<^sub>t \<rho> \<Gamma> \<Gamma>'"
  shows "wf_ren\<^sub>t (extr \<rho>) (Suc \<Gamma>) (Suc \<Gamma>')"
  apply auto apply (case_tac x) apply force
  apply (simp add: lift_ren_def) using 1 apply auto done

lemma wft_rename_pres: "\<lbrakk> wft \<Gamma> A; wf_ren\<^sub>t \<rho> \<Gamma> \<Gamma>' \<rbrakk> \<Longrightarrow> wft \<Gamma>' (rename\<^sub>t \<rho> A)"
proof (induction A arbitrary: \<Gamma> \<Gamma>' \<rho>)
  case (TVar x)
  then show ?case by auto
next
  case TBool
  then show ?case by auto
next
  case (TFun A1 A2)
  then show ?case by auto
next
  case (TAll A)
  then show ?case using ext_wf_rent by auto
qed

definition wf_sub\<^sub>t :: "Subst\<^sub>t \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "wf_sub\<^sub>t \<sigma> \<Gamma> \<Gamma>' \<equiv> \<forall> x. x < \<Gamma> \<longrightarrow> wft \<Gamma>' (\<sigma> x)"
declare wf_sub\<^sub>t_def[simp]

lemma ext_wf_subt: assumes 1: "wf_sub\<^sub>t \<sigma> \<Gamma> \<Gamma>'"
  shows "wf_sub\<^sub>t (extt \<sigma>) (Suc \<Gamma>) (Suc \<Gamma>')"
  apply auto
proof -
  fix x assume xg: "x < Suc \<Gamma>" 
  show "wft (Suc \<Gamma>') ((TVar 0 \<bullet> (\<sigma> ;\<^sub>t \<up>\<^sub>t)) x)"
  proof (cases x)
    case 0
    then show ?thesis by auto
  next
    case (Suc y)
    from xg Suc 1 have 2: "wft \<Gamma>' (\<sigma> y)" by auto
    from 2 have "wft (Suc \<Gamma>') (rename\<^sub>t Suc (\<sigma> y))"
      by (rule wft_rename_pres) auto
    then have "wft (Suc \<Gamma>') (sub\<^sub>t \<up>\<^sub>t (\<sigma> y))" 
      using rename_sub_ren\<^sub>t[of Suc "\<sigma> y"] by simp
    with Suc show ?thesis by (simp add: seq\<^sub>t_def)
  qed
qed
  
lemma wft_sub_pres: "\<lbrakk> wft \<Gamma> A; wf_sub\<^sub>t \<sigma> \<Gamma> \<Gamma>' \<rbrakk> \<Longrightarrow> wft \<Gamma>' (sub\<^sub>t \<sigma> A)"
proof (induction A arbitrary: \<Gamma> \<Gamma>' \<sigma>)
  case (TVar x)
  then show ?case by auto
next
  case TBool
then show ?case by auto
next
case (TFun A B)
  then show ?case by auto
next
  case (TAll A)
  from TAll have 1: "wft (Suc \<Gamma>) A" by blast
  from TAll have 2: "wf_sub\<^sub>t (extt \<sigma>) (Suc \<Gamma>) (Suc \<Gamma>')"
    using ext_wf_subt by auto
  from TAll 1 2 have IH: "wft (Suc \<Gamma>') (sub\<^sub>t (extt \<sigma>) A)" by blast
  then show ?case by auto
qed

lemma wft_subst_pres: "\<lbrakk> wft \<Gamma> A; wft \<Gamma> B \<rbrakk> \<Longrightarrow> wft \<Gamma> (A[B]\<^sub>t)"
  apply (rule wft_sub_pres)
   apply assumption
  apply auto
  apply (case_tac x)
   apply (auto simp add: id\<^sub>t_def)
  done


section "Terms"

datatype Term =
  Var var
  | Bool bool
  | App Term Term (infixl "\<cdot>" 70)
  | Lam Term      ("\<lambda>")
  | TLam Term     ("\<Lambda>")
  | TApp Term  (* leave out the type to side-step type substitution *)

inductive wtt :: "Type list \<Rightarrow> nat \<Rightarrow> Term \<Rightarrow> Type \<Rightarrow> bool" ("_;_\<turnstile>_:_" 55) where
  wt_var[intro!]: "\<Gamma>; \<Sigma> \<turnstile> Var x : \<Gamma>!x" |
  wt_bool[intro!]: "\<Gamma>; \<Sigma> \<turnstile> Bool b : TBool" |
  wt_app[intro!]: "\<lbrakk> \<Gamma>; \<Sigma> \<turnstile> L : A \<rightarrow> B; \<Gamma>; \<Sigma> \<turnstile> M : A \<rbrakk> \<Longrightarrow> \<Gamma>; \<Sigma> \<turnstile> L \<cdot> M : B" |
  wt_lam[intro!]: "\<lbrakk> wft \<Sigma> A; A#\<Gamma>; \<Sigma> \<turnstile> N : B\<rbrakk> \<Longrightarrow> \<Gamma>; \<Sigma> \<turnstile> \<lambda> N : A \<rightarrow> B" |
  wt_tlam[intro!]: "\<lbrakk> \<Gamma>; Suc \<Sigma> \<turnstile> N : A\<rbrakk> \<Longrightarrow> \<Gamma>; \<Sigma> \<turnstile> \<Lambda> N : \<forall> A" |
  wt_tapp[intro!]: "\<lbrakk> wft \<Sigma> B; \<Gamma>; \<Sigma> \<turnstile> L : \<forall> A\<rbrakk> \<Longrightarrow> \<Gamma>; \<Sigma> \<turnstile> TApp L : A[B]\<^sub>t" 

fun rename :: "Renaming \<Rightarrow> Term \<Rightarrow> Term" where
  "rename \<rho> (Var x) = Var (\<rho> x)" |
  "rename \<rho> (Bool b) = Bool b" |
  "rename \<rho> (L \<cdot> M) = (rename \<rho> L) \<cdot> (rename \<rho> M)" |
  "rename \<rho> (\<lambda> N) = \<lambda> (rename (extr \<rho>) N)" |
  "rename \<rho> (\<Lambda> N) = \<Lambda> (rename \<rho> N)" |
  "rename \<rho> (TApp L) = TApp (rename \<rho> L)"

type_synonym Subst = "var \<Rightarrow> Term"

definition ids :: "Subst" where
  "ids x \<equiv> Var x"

definition lift_sub :: "Subst \<Rightarrow> Subst" ("\<Up>") where
  "\<Up> \<sigma> x \<equiv> rename Suc (\<sigma> x)"

abbreviation exts :: "Subst \<Rightarrow> Subst" where
  "exts \<sigma> \<equiv> Var 0 \<bullet> \<Up> \<sigma>"

fun sub :: "Subst \<Rightarrow> Term \<Rightarrow> Term" where
  "sub \<sigma> (Var x) = \<sigma> x" |
  "sub \<sigma> (Bool b) = Bool b" |
  "sub \<sigma> (L \<cdot> M) = (sub \<sigma> L) \<cdot> (sub \<sigma> M)" |
  "sub \<sigma> (\<lambda> N) = \<lambda> (sub (exts \<sigma>) N)" |
  "sub \<sigma> (\<Lambda> N) = \<Lambda> (sub \<sigma> N)" |
  "sub \<sigma> (TApp L) = TApp (sub \<sigma> L)"

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
  apply (induction M arbitrary: \<rho>)
  apply (auto simp add: ren_def)
  done

lemma lift_def: "\<Up> \<sigma> x = sub (ren Suc) (\<sigma> x)"
  using rename_sub_ren ren_def lift_sub_def apply simp
  done

interpretation interp_sub: subst2 Var lift_sub sub ren seq
  apply unfold_locales
  using lift_def apply blast
  apply simp
  done




end