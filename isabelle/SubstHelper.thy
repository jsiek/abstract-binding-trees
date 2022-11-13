theory SubstHelper
imports Main
begin


type_synonym var = nat
type_synonym Renaming = "var \<Rightarrow> var"

fun cons :: "'v \<Rightarrow> (var \<Rightarrow> 'v) \<Rightarrow> (var \<Rightarrow> 'v)" (infixl "\<bullet>" 75) where
  "(cons v \<sigma>) 0 = v" |
  "(cons v \<sigma>) (Suc x) = \<sigma> x"

definition lift_ren :: "Renaming \<Rightarrow> Renaming" ("\<Up>\<^sub>r") where
  "\<Up>\<^sub>r \<rho> x \<equiv> Suc (\<rho> x)"

locale subst1 =
  fixes Var :: "var \<Rightarrow> 'a"
    and lift_sub :: "(var \<Rightarrow> 'a) \<Rightarrow> (var \<Rightarrow> 'a)" ("\<Up>")
    and sub :: "(var \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a"
    and ren :: "(var \<Rightarrow> var) \<Rightarrow> (var \<Rightarrow> 'a)"
    and seq :: "(var \<Rightarrow> 'a) \<Rightarrow> (var \<Rightarrow> 'a) \<Rightarrow> (var \<Rightarrow> 'a)" (infixr ";" 70)
  assumes ren_def: "ren \<rho> x = Var (\<rho> x)"
    and seq_def: "(\<sigma> ; \<tau>) x = sub \<tau> (\<sigma> x)"
    and lift_sub_ren_var: "\<Up> (ren \<rho>) x = Var (Suc (\<rho> x))"
begin

lemma ren_cons[simp]: "ren (y \<bullet> \<rho>) = Var y \<bullet> ren \<rho>"
  apply (rule ext)
  apply (case_tac x)
   apply (simp add: ren_def)
  apply (simp add: ren_def)
  done

lemma ren_shift[simp]: "ren (\<Up>\<^sub>r \<rho>) = \<Up> (ren \<rho>)"
  apply (rule ext)
  apply (case_tac x)
  apply (simp add: lift_sub_ren_var ren_def lift_ren_def)
  apply (simp add: lift_ren_def ren_def lift_sub_ren_var)
  done

theorem ConsSeq[simp]: "(M \<bullet> \<sigma>) ; \<tau> = sub \<tau> M \<bullet> (\<sigma> ; \<tau>)"
  apply (rule ext)
  apply (case_tac x)
   apply (simp add: seq_def)
   apply (simp add: seq_def)
  done

end

locale subst2 = subst1 +
  assumes lift_def: "\<Up> \<sigma> x = sub (ren Suc) (\<sigma> x)"
    and sub_var: "sub \<sigma> (Var x) = \<sigma> x"
begin

theorem shift_ren_seq[simp]: "\<Up> (ren \<rho> ; \<tau>) = \<Up> (ren \<rho>) ; Var 0 \<bullet> \<Up> \<tau>"
  apply (rule ext)
  apply (case_tac x)
   apply (simp add: seq_def ren_def lift_def sub_var)
   apply (simp add: seq_def ren_def lift_def sub_var)
  done

lemma ren_suc: fixes \<rho>::Renaming shows "(ren \<rho> ; ren Suc) = \<Up> (ren \<rho>)"
  apply (rule ext)
  apply (simp add: seq_def ren_def lift_def)
  done

end

end