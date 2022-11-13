(*
  I'm relatively happy with this experiment.
  The idea was to use a custom Term data type, but
  make many of the substitution lemmas generic,
  in a sequence of locale's that culminate in
  the substitution lemma.
 
*)

theory Lambda
  imports Main SubstHelper
begin

section "Syntax"

datatype Term =
  Var var
  | Bool bool
  | App Term Term (infixl "\<cdot>" 70)
  | Lam Term      ("\<lambda>")

section "Substitution"

abbreviation extr :: "Renaming \<Rightarrow> Renaming" where
  "extr \<rho> \<equiv> 0 \<bullet> \<Up>\<^sub>r \<rho>"

fun rename :: "Renaming \<Rightarrow> Term \<Rightarrow> Term" where
  "rename \<rho> (Var x) = Var (\<rho> x)" |
  "rename \<rho> (Bool b) = Bool b" |
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
  "sub \<sigma> (Bool b) = Bool b" |
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
  case (Bool b)
  then show ?case by simp
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
  case (Bool b)
  then show ?case by simp
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
  case (Bool b)
  then show ?case by simp
next
  case (Lam N)
  let ?S = "exts \<sigma>" and ?T = "exts \<tau>"
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
  apply simp
  done

interpretation interp_sub: subst6 Var lift_sub sub ren seq ids ext
  apply unfold_locales unfolding ext_def apply auto done

abbreviation subst_one :: "Term \<Rightarrow> Term \<Rightarrow> Term" ("_[_]" 70) where
  "subst_one N M \<equiv> sub (M \<bullet> ids) N"
abbreviation subst_two :: "Term \<Rightarrow> Term \<Rightarrow> Term" ("_\<lbrace>_\<rbrace>" 60) where
  "N \<lbrace> M \<rbrace> \<equiv> sub (ext (M \<bullet> ids)) N"


section "Type System"

datatype Type =
    TVar var
  | TBool
  | TFun Type Type (infixl "\<rightarrow>" 60)

type_synonym TEnv = "Type list" 

inductive wtt :: "TEnv \<Rightarrow> Term \<Rightarrow> Type \<Rightarrow> bool" ("_\<turnstile>_:_" 55) where
  wt_var[intro!]: "\<lbrakk> x < length \<Gamma>; \<Gamma>!x = A \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> Var x : A" |
  wt_bool[intro!]: "\<Gamma> \<turnstile> Bool b : TBool" |
  wt_app[intro!]: "\<lbrakk> \<Gamma> \<turnstile> L : A \<rightarrow> B; \<Gamma> \<turnstile> M : A \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> L \<cdot> M : B" |
  wt_lam[intro!]: "\<lbrakk> A#\<Gamma> \<turnstile> N : B\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> \<lambda> N : A \<rightarrow> B"

inductive_cases
  wt_var_elim[elim!]: "\<Gamma> \<turnstile> Var x : A" and
  wt_bool_elim[elim!]: "\<Gamma> \<turnstile> Bool b : A" and
  wt_app_elim[elim!]: "\<Gamma> \<turnstile> App L M : A" and
  wt_lam_elim[elim!]: "\<Gamma> \<turnstile> \<lambda> N : A" 

definition wt_ren :: "Renaming \<Rightarrow> TEnv \<Rightarrow> TEnv \<Rightarrow> bool" where
  "wt_ren \<rho> \<Gamma> \<Gamma>' \<equiv> \<forall> x. x < length \<Gamma> \<longrightarrow> \<rho> x < length \<Gamma>' \<and> \<Gamma>!x = \<Gamma>'!(\<rho> x)"
declare wt_ren_def[simp]

lemma ext_wt_ren: assumes 1: "wt_ren \<rho> \<Gamma> \<Gamma>'"
  shows "wt_ren (extr \<rho>) (A#\<Gamma>) (A#\<Gamma>')"
  apply auto 
   apply (case_tac x) apply force using 1 apply force
  apply (case_tac x) apply force using 1 apply force 
  done

lemma wt_rename_pres: "\<lbrakk> \<Gamma> \<turnstile> M : A; wt_ren \<rho> \<Gamma> \<Gamma>' \<rbrakk> \<Longrightarrow> \<Gamma>' \<turnstile> rename \<rho> M : A"
proof (induction M arbitrary: \<Gamma> \<Gamma>' \<rho> A)
  case (Var x)
  then show ?case by auto
next
  case (Bool b)
  then show ?case by auto
next
  case (App L M)
  then show ?case by auto
next
  case (Lam N)
  then show ?case using ext_wt_ren by auto
qed

definition wt_sub :: "Subst \<Rightarrow> TEnv \<Rightarrow> TEnv \<Rightarrow> bool" where
  "wt_sub \<sigma> \<Gamma> \<Gamma>' \<equiv> \<forall> x. x < length \<Gamma> \<longrightarrow> \<Gamma>' \<turnstile> \<sigma> x : \<Gamma>!x"
declare wt_sub_def[simp]

lemma ext_wt_sub: assumes 1: "wt_sub \<sigma> \<Gamma> \<Gamma>'"
  shows "wt_sub (ext \<sigma>) (A#\<Gamma>) (A#\<Gamma>')"
  apply auto
proof -
  fix x assume xg: "x < Suc (length \<Gamma>)"
  show "A # \<Gamma>'\<turnstile>(Var 0 \<bullet> (\<sigma> ; \<up>)) x:(A # \<Gamma>) ! x"
  proof (cases x)
    case 0
    then show ?thesis by auto 
  next
    case (Suc y)
    from 1 xg Suc have 2: "\<Gamma>' \<turnstile> \<sigma> y : \<Gamma>!y" by auto
    from 2 have "A#\<Gamma>' \<turnstile> rename Suc (\<sigma> y) : \<Gamma>!y" by (rule wt_rename_pres) auto
    then have "A#\<Gamma>' \<turnstile> sub \<up> (\<sigma> y) : \<Gamma>!y" using rename_sub_ren[of Suc "\<sigma> y"] by simp
    with Suc show ?thesis by (simp add: seq_def)
  qed
qed

lemma wt_sub_pres: "\<lbrakk> \<Gamma> \<turnstile> M : A; wt_sub \<sigma> \<Gamma> \<Gamma>' \<rbrakk> \<Longrightarrow> \<Gamma>' \<turnstile> sub \<sigma> M : A"
proof (induction M arbitrary: \<Gamma> \<Gamma>' \<sigma> A)
  case (Var x)
  then show ?case by auto
next
  case (Bool x)
  then show ?case by auto
next
  case (App L M)
  then show ?case by auto
next
  case (Lam N)
  from Lam obtain B C where 1: "B#\<Gamma> \<turnstile> N : C" and 2: "A = B \<rightarrow> C" by auto
  from Lam have 3: "wt_sub (ext \<sigma>) (B#\<Gamma>) (B#\<Gamma>')" using ext_wt_sub by auto
  from 1 3 Lam have "B#\<Gamma>' \<turnstile> sub (ext \<sigma>) N : C" by blast
  with 2 show ?case by auto
qed

lemma wft_subst_pres: "\<lbrakk> B#\<Gamma> \<turnstile> M : A; \<Gamma> \<turnstile> N : B \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> M[N] : A"
  apply (rule wt_sub_pres)
   apply assumption
  apply auto
  apply (case_tac x)
   apply (auto simp add: ids_def)
  done

section "Semantics"

inductive reduce :: "Term \<Rightarrow> Term \<Rightarrow> bool" (infix "\<longmapsto>" 50) where
  beta[intro!]: "(\<lambda> N) \<cdot> M \<longmapsto> N[M]" |
  appl[intro!]: "L \<longmapsto> L' \<Longrightarrow> L \<cdot> M \<longmapsto> L' \<cdot> M" |
  appr[intro!]: "M \<longmapsto> M' \<Longrightarrow> L \<cdot> M \<longmapsto> L \<cdot> M'" |
  abs[intro!]: "N \<longmapsto> N' \<Longrightarrow> \<lambda> N \<longmapsto> \<lambda> N'"

inductive val :: "Term \<Rightarrow> bool" where
  vlam[intro!]: "val (\<lambda> N)" |
  vbool[intro!]: "val (Bool b)"

lemma preservation: "\<lbrakk> M \<longmapsto> N; \<Gamma> \<turnstile> M : A \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> N : A"
proof (induction M N arbitrary: \<Gamma> A rule: reduce.induct)
case (beta N M)
  then show ?case using wft_subst_pres by auto
next
  case (appl L L' M)
  then show ?case by auto
next
  case (appr M M' L)
  then show ?case by auto
next
  case (abs N N')
  then show ?case by auto
qed

lemma progress: "\<Gamma> \<turnstile> M : A \<Longrightarrow> \<Gamma> = [] \<Longrightarrow> val M \<or> (\<exists> N. M \<longmapsto> N)"
proof (induction M A rule: wtt.induct)
case (wt_var \<Gamma> x A)
  then show ?case by auto
next
  case (wt_bool \<Gamma> b)
  then show ?case by auto
next
  case (wt_app \<Gamma> L A B M)
  from wt_app have " val L \<or> (\<exists>L'. L \<longmapsto> L')" by auto
  then show ?case
  proof
    assume "val L"
    show ?thesis sorry
  next
    assume "\<exists>L'. L \<longmapsto> L'"
    then show ?thesis by auto
  qed
next
  case (wt_lam A \<Gamma> N B)
  then show ?case by auto
qed

end