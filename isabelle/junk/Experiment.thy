theory Experiment
  imports Main
begin

type_synonym var = nat
type_synonym Renaming = "var \<Rightarrow> var"

fun cons :: "'v \<Rightarrow> (var \<Rightarrow> 'v) \<Rightarrow> (var \<Rightarrow> 'v)" (infixl "\<bullet>" 75) where
  "(cons v \<sigma>) 0 = v" |
  "(cons v \<sigma>) (Suc x) = \<sigma> x"

definition lift_ren :: "Renaming \<Rightarrow> Renaming" ("\<Up>") where
  "\<Up> \<rho> x \<equiv> Suc (\<rho> x)"

(********************************************************************)
locale substitution =
  fixes Var :: "var \<Rightarrow> 't"
    and lift_sub :: "(var \<Rightarrow> 't) \<Rightarrow> (var \<Rightarrow> 't)" ("\<Up>")
    and ren :: "Renaming \<Rightarrow> (var \<Rightarrow> 't)"
    and sub :: "(var \<Rightarrow> 't) \<Rightarrow> 't \<Rightarrow> 't"
    and ids :: "var \<Rightarrow> 't"
    and seq :: "(var \<Rightarrow> 't) \<Rightarrow> (var \<Rightarrow> 't) \<Rightarrow> (var \<Rightarrow> 't)" (infixr ";" 70)
  assumes ren_def: "ren \<rho> x = Var (\<rho> x)"
    and ren_shift[simp]: "ren (\<Up> \<rho>) = lift_sub (ren \<rho>)" (* was lift_sub (ren \<rho>)  *)
    and sub_var[simp]: "sub \<sigma> (Var x) = \<sigma> x"
    and shift_var[simp]: "\<Up> Var x = Var (Suc x)"
    and lift_ren_var[simp]: "lift_sub (ren \<rho>) x = Var (Suc (\<rho> x))"
    and lift_sub_var[simp]: "lift_sub \<sigma> x = sub (ren Suc) (\<sigma> x)"
    and ids_def: "ids x = Var x"
    and seq_def: "(\<sigma> ; \<tau>) x \<equiv> sub \<tau> (\<sigma> x)"
begin

lemma ren_cons[simp]: "ren (y \<bullet> \<rho>) = Var y \<bullet> ren \<rho>"
  apply (rule ext)
  apply (case_tac x)
   apply (simp add: ren_def)
  apply (simp add: ren_def)
  done

lemma id_sub[simp]: "sub \<sigma> (ids x) = \<sigma> x"
  unfolding ids_def by simp

lemma ext_id[simp]: "Var 0 \<bullet> \<Up> ids = ids"
  apply (rule ext) unfolding ids_def ren_def
  apply (case_tac x) apply force
  apply (simp add: ren_def)
  done

theorem shift_ren_seq[simp]: "\<Up> (ren \<rho> ; \<tau>) = (\<Up> (ren \<rho>) ; Var 0 \<bullet> \<Up> \<tau>)"
  apply (rule ext)
  apply (case_tac x)
   apply (simp add: seq_def ren_def)
   apply (simp add: seq_def ren_def)
  done

lemma ren_suc[simp]: fixes \<rho>::Renaming shows "(ren \<rho> ; ren Suc) = ren (\<Up> \<rho>)"
  apply (rule ext)
  apply (simp add: seq_def ren_def)
  done

lemma shift_seq_ren[simp]: "ren Suc ; Var 0 \<bullet> \<Up> (ren \<rho>) = ren (\<Up> \<rho>)"
  apply (rule ext)
  apply (case_tac x)
   apply (simp add: seq_def ren_def)
  apply (simp add: seq_def ren_def )
  done

theorem ConsSeq[simp]: "(M \<bullet> \<sigma>) ; \<tau> = sub \<tau> M \<bullet> (\<sigma> ; \<tau>)"
  apply (rule ext)
  apply (case_tac x)
   apply (simp add: seq_def)
   apply (simp add: seq_def)
  done

lemma shift_seq_sub[simp]: "ren Suc ; Var 0 \<bullet> \<Up> \<sigma> = \<Up> \<sigma>"
  apply (rule ext) apply (case_tac x) 
   apply (simp add: seq_def ren_def)
   apply (simp add: seq_def ren_def)
  done

end
(********************************************************************)

datatype Term =
    Var var
    | App Term Term (infixl "\<cdot>" 70)
    | Lam Term      ("\<lambda>")

fun rename :: "Renaming \<Rightarrow> Term \<Rightarrow> Term" where
  "rename \<rho> (Var x) = Var (\<rho> x)" |
  "rename \<rho> (L \<cdot> M) = (rename \<rho> L) \<cdot> (rename \<rho> M)" |
  "rename \<rho> (\<lambda> N) = \<lambda> (rename (0 \<bullet> \<Up> \<rho>) N)"

type_synonym Subst = "var \<Rightarrow> Term"

definition lift_sub :: "Subst \<Rightarrow> Subst" ("\<Up>") where
  "\<Up> \<sigma> x \<equiv> rename Suc (\<sigma> x)"

fun sub :: "Subst \<Rightarrow> Term \<Rightarrow> Term" where
  "sub \<sigma> (Var x) = \<sigma> x" |
  "sub \<sigma> (L \<cdot> M) = (sub \<sigma> L) \<cdot> (sub \<sigma> M)" |
  "sub \<sigma> (\<lambda> N) = \<lambda> (sub (Var 0 \<bullet> \<Up> \<sigma>) N)"

definition ren :: "Renaming \<Rightarrow> Subst" where
  "ren \<rho> x \<equiv> Var (\<rho> x)"

lemma rename_sub_ren: "rename \<rho> M = sub (ren \<rho>) M"
proof (induction M arbitrary: \<rho>)
  case (Var x)
then show ?case unfolding ren_def by simp
next
  case (App L M)
  then show ?case by simp
next
  case (Lam N)
  have "ren (0 \<bullet> \<Up> \<rho>) = (Var 0 \<bullet> \<Up> (ren \<rho>))" apply (rule ext)
    unfolding ren_def lift_ren_def lift_sub_def apply (case_tac x) apply auto done
  then have "sub (ren (0 \<bullet> \<Up> \<rho>)) N = sub (Var 0 \<bullet> \<Up> (ren \<rho>)) N" by simp
  with Lam show "rename \<rho> (\<lambda> N) = sub (ren \<rho>) (\<lambda> N)" by simp
qed

lemma lift_def[simp]: "\<Up> \<sigma> x = sub (ren Suc) (\<sigma> x)"
  using rename_sub_ren ren_def lift_sub_def by simp

definition ids :: "Subst" where
  "ids x \<equiv> Var x"

definition seq :: "Subst \<Rightarrow> Subst \<Rightarrow> Subst" (infixr ";" 70) where
  "(\<sigma> ; \<tau>) x \<equiv> sub \<tau> (\<sigma> x)"

lemma ren_shift[simp]: "ren (\<Up> \<rho>) = \<Up> (ren \<rho>)"
  apply (rule ext)
  apply (case_tac x)
  apply (simp add: lift_ren_def ren_def)
  apply (simp add: lift_ren_def ren_def)
  done

(***********************************************************)

interpretation subst: substitution Var lift_sub ren sub ids seq
  apply unfold_locales
  apply (simp add: ren_def)
  using ren_shift apply simp
   apply simp
   apply (simp add: ren_def)
   apply (simp add: lift_sub_def ren_def)
   apply simp
   apply (simp add: ids_def)
  apply (simp add: seq_def)
  done

(***********************************************************)

lemma sub_id[simp]: "sub ids M = M"
  apply (induction M)
  apply (simp add: ids_def)
  apply simp
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
  let ?T = "Var 0 \<bullet> \<Up> \<tau>" and ?R = "0 \<bullet> \<Up> \<rho>"
  from Lam have "sub ?T (sub (ren ?R) N) = sub (ren ?R ; ?T) N" by blast
  then show ?case by simp
qed

lemma shift_sub_ren[simp]: "\<Up> (\<sigma> ; ren \<rho>) = \<Up> \<sigma> ; Var 0 \<bullet> ren (\<Up> \<rho>)"
  apply (rule ext)
  apply (case_tac x)
   apply (simp add: seq_def ren_def ren_sub)
   apply (simp add: seq_def ren_def ren_sub)
  done

lemma sub_ren: "sub (ren \<rho>) (sub \<sigma> M) = sub (\<sigma> ; ren \<rho>) M"
  apply (induction M arbitrary: \<sigma> \<rho>)
    apply (simp add: seq_def)
   apply simp
  apply simp
proof -
  fix M \<sigma> \<rho> 
  assume IH: "\<And>\<sigma> \<rho>. sub (ren \<rho>) (sub \<sigma> M) = sub (\<sigma> ; ren \<rho>) M"
  have "sub (Var 0 \<bullet> \<Up> (ren \<rho>)) (sub (Var 0 \<bullet> \<Up> \<sigma>) M)
        = sub (ren (0 \<bullet> \<Up> \<rho>)) (sub (Var 0 \<bullet> \<Up> \<sigma>) M)" by simp
  also have "... = sub ((Var 0 \<bullet> \<Up> \<sigma>) ; ren (0 \<bullet> \<Up> \<rho>)) M" using IH by fast
  also have "... = sub (Var 0 \<bullet> (\<Up> \<sigma> ; Var 0 \<bullet> \<Up> (ren \<rho>))) M" by simp
  finally show "sub (Var 0 \<bullet> \<Up> (ren \<rho>)) (sub (Var 0 \<bullet> \<Up> \<sigma>) M) 
        = sub (Var 0 \<bullet> (\<Up> \<sigma> ; Var 0 \<bullet> \<Up> (ren \<rho>))) M" .
qed

lemma sub_suc[simp]: fixes \<rho>::Renaming shows "(\<sigma> ; ren Suc) = \<Up> \<sigma>"
  unfolding seq_def lift_sub_def apply (rule ext) using rename_sub_ren apply simp done

lemma sub_sub: "sub \<tau> (sub \<sigma> M) = sub (\<sigma> ; \<tau>) M"
proof (induction M arbitrary: \<sigma> \<tau>)
  case (Var x)
  then show ?case by (simp add: seq_def)
next
  case (Lam M)
  have "Var 0 \<bullet> \<Up> \<sigma> ; Var 0 \<bullet> \<Up> \<tau> = Var 0 \<bullet> \<Up> (\<sigma> ; \<tau>)"
    apply (rule ext) apply (case_tac x) 
     apply (simp add: seq_def lift_sub_def)
    apply simp apply (simp add: seq_def lift_sub_def ren_sub) using sub_ren apply auto done
  with Lam show ?case by simp
next
  case (App L M)
  then show ?case by simp
qed

end