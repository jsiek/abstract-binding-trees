(*

This file contains a sequence of locale's that help
prove the usual substitution lemmas for a language.
The client has to prove ren_sub, sub_ren, sub_sub, and sub_id,
but the locale's in this file make that easier.

*)

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
declare lift_ren_def[simp]

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
    and sub_var[simp]: "sub \<sigma> (Var x) = \<sigma> x"
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

lemma shift_seq_ren[simp]: "ren Suc ; Var 0 \<bullet> \<Up> (ren \<rho>) = ren (\<Up>\<^sub>r \<rho>)"
  apply (rule ext)
  apply (case_tac x)
   apply (simp add: seq_def ren_def sub_var)
  apply (simp add: seq_def ren_def sub_var)
  done

lemma shift_seq_sub[simp]: "ren Suc ; M \<bullet> \<sigma> = \<sigma>"
  apply (rule ext) apply (case_tac x) 
   apply (simp add: seq_def ren_def sub_var)
   apply (simp add: seq_def ren_def sub_var)
  done

end

locale subst3 = subst2 + 
  assumes ren_sub: "sub \<tau> (sub (ren \<rho>) M) = sub (ren \<rho> ; \<tau>) M"
begin

lemma shift_sub_ren[simp]: "\<Up> (\<sigma> ; ren \<rho>) = \<Up> \<sigma> ; Var 0 \<bullet> ren (\<Up>\<^sub>r \<rho>)"
  apply (rule ext)
  apply (case_tac x)
   apply (simp add: seq_def ren_def ren_sub lift_def ren_suc)
   apply (simp add: seq_def ren_def ren_sub lift_def ren_suc)
  done

end

locale subst4 = subst3 + 
  assumes sub_ren: "sub (ren \<rho>) (sub \<sigma> M) = sub (\<sigma> ; ren \<rho>) M"
begin

lemma sub_suc: fixes \<rho>::Renaming shows "(\<sigma> ; ren Suc) = \<Up> \<sigma>"
  unfolding seq_def apply (rule ext)
  apply (simp add: lift_def)  
  done

abbreviation exts :: "(var \<Rightarrow> 'a) \<Rightarrow> (var \<Rightarrow> 'a)" where
  "exts \<sigma> \<equiv> Var 0 \<bullet> \<Up> \<sigma>"

lemma exts_seq: "exts \<sigma> ; exts \<tau> = exts (\<sigma> ; \<tau>)"
  apply (rule ext) apply (case_tac x) 
   apply (simp add: seq_def lift_def sub_var)
  apply (simp add: seq_def lift_def ren_sub)
  using sub_ren sub_suc apply auto done

end

locale subst5 = subst4 +
  fixes ids :: "var \<Rightarrow> 'a"
  assumes sub_sub[simp]: "sub \<tau> (sub \<sigma> M) = sub (\<sigma> ; \<tau>) M"
    and ids_def: "ids x = Var x"
begin

lemma id_sub[simp]: "sub \<sigma> (ids x) = \<sigma> x"
  unfolding ids_def sub_var by simp

lemma exts_id[simp]: "exts ids = ids"
  apply (rule ext) unfolding ids_def ren_def
  apply (case_tac x) apply force
  apply (simp add: ren_def lift_def sub_var)
  done

theorem seq_ids_left[simp]: "ids ; \<sigma> = \<sigma>" 
  unfolding seq_def ids_def sub_var by simp

theorem seq_assoc[simp]: "(\<sigma> ; \<tau>) ; \<rho> = \<sigma> ; (\<tau> ; \<rho>)"
  apply (rule ext)
  unfolding seq_def apply simp
  unfolding seq_def by simp

lemma lift_sub_seq_suc[simp]: "\<Up> \<sigma> = \<sigma> ; ren Suc"
  apply (rule ext)
  unfolding lift_def seq_def apply (simp add: ren_def) done

lemma cons_shift_ids[simp]: "Var 0 \<bullet> ren Suc = ids"
  apply (rule ext)
  unfolding ids_def apply (case_tac x) apply simp apply (simp add: ren_def) done

end

locale subst6 = subst5 +
  fixes ext :: "(var \<Rightarrow> 'a) \<Rightarrow> (var \<Rightarrow> 'a)"
  assumes sub_id[simp]: "sub ids M = M"
    and ext_def[simp]: "ext \<sigma> = Var 0 \<bullet> (\<sigma> ; ren Suc)"
begin

abbreviation subst_one :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" ("_[_]" 70) where
  "subst_one N M \<equiv> sub (M \<bullet> ids) N"
abbreviation subst_two :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" ("_\<lbrace>_\<rbrace>" 60) where
 "N \<lbrace> M \<rbrace> \<equiv> sub (ext (M \<bullet> ids)) N"

theorem seq_ids_right[simp]: "\<sigma> ; ids = \<sigma>"
  unfolding seq_def by simp

theorem subst_commute: "(sub (ext \<sigma>) N) [ sub \<sigma> M ] = sub \<sigma> (N [ M ])"
  by simp

theorem substitution: "M[N][L] = M\<lbrace>L\<rbrace>[N[L]]"
  by simp

theorem ext_sub_cons: "(sub (ext \<sigma>) N)[V] = sub (V \<bullet> \<sigma>) N" 
  by simp

end


end