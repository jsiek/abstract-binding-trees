theory Rename
  imports Main ABT
begin

(*
 Note: renamings are an internal device to help define substitution.
 Renamings are not meant to be used outside of this ABT library.
*)

interpretation var_s: substable "Var 0" "Suc" "\<lambda> x. x" "Var"
  by unfold_locales auto

definition extr :: "var sub \<Rightarrow> var sub" where
  "extr \<rho> \<equiv> var_s.ext \<rho>"

definition rename :: "var sub \<Rightarrow> 'op ABT \<Rightarrow> 'op ABT" where
  "rename \<equiv> var_s.map_abt"

definition seqrr :: "var sub \<Rightarrow> var sub \<Rightarrow> var sub" (infixr "r;r" 70) where
  "(\<sigma> r;r \<rho>) x \<equiv> \<rho> (\<sigma> x)"

lemma extr_cons_seq[simp]: "extr \<rho> = 0 \<bullet> (\<rho> r;r Suc)"
  unfolding extr_def seqrr_def by simp

theorem RIdL[simp]: "(\<lambda> x. x) r;r \<rho> = \<rho>"
  unfolding seqrr_def by simp

theorem RShiftId[simp]: "Suc r;r (\<lambda> x. x) = Suc"
  unfolding seqrr_def by simp

theorem RHeadCons[simp]: "(x \<bullet> \<rho>) 0 = x"
  unfolding cons_def by simp

theorem RHeadConsRen[simp]: "rename (x \<bullet> \<rho>) (Var 0) = Var x"
  unfolding rename_def by simp

theorem RTailCons[simp]: "(y \<bullet> \<sigma>) (Suc x) = \<sigma> x"
  unfolding cons_def by simp 

theorem RTailConsRen[simp]: "rename (y \<bullet> \<sigma>) (Var (Suc x)) = Var (\<sigma> x)"
  unfolding rename_def by simp 

theorem RShiftCons[simp]: "Suc r;r (x \<bullet> \<rho>) = \<rho>"
  unfolding cons_def  seqrr_def shift_def by simp

(********************** locale subst_quote_shift ***************************)
locale subst_quote_shift = substable +
  assumes quote_var: "quote \<lfloor>x\<rfloor> = Var x"
  and quote_shift: "quote (\<Up> v) = rename Suc (quote v)"
begin
  
  lemma id_ext: "(\<forall> x. quote (\<sigma> x) = Var x) \<Longrightarrow> quote ((ext \<sigma>) x) = Var x"
    apply (case_tac x)
    using quote_var apply (force simp add: cons_def)
    using quote_shift apply (force simp add: cons_def rename_def)
    done
  
  abbreviation P_id_abt :: "'a ABT \<Rightarrow> bool" where
    "P_id_abt M \<equiv> \<forall> \<sigma>. (\<forall> x. quote (\<sigma> x) = Var x)
       \<longrightarrow> map_abt \<sigma> M = M"
  abbreviation P_id_arg :: "'a Arg \<Rightarrow> bool" where
    "P_id_arg A \<equiv> \<forall> \<sigma>. (\<forall> x. quote (\<sigma> x) = Var x)
        \<longrightarrow> map_arg \<sigma> A = A"
  
  lemma map_id_aux: "P_id_abt M"
    apply (induction M rule: ABT.induct[of P_id_abt P_id_arg])
       apply force
      apply simp apply clarify apply (rule map_idI) apply blast
     apply force
    apply simp apply clarify using id_ext apply force
    done
  
  theorem map_abt_id: 
    assumes 1: "\<And> x. quote (\<sigma> x) = Var x"
    shows "map_abt \<sigma> M = M" using 1 map_id_aux by fast

end
(********************** end subst_quote_shift ***************************)

interpretation var_sqs: subst_quote_shift "Var 0" Suc "\<lambda> x. x" Var
  by unfold_locales (auto simp: rename_def)
  
theorem rename_id[simp]: "rename (\<lambda> x. x) M = M"
  unfolding rename_def by (rule var_sqs.map_abt_id) simp

theorem RIdR[simp]: "\<rho> r;r (\<lambda> x. x) = \<rho>"
  unfolding seqrr_def by (rule ext) simp

theorem RConsSeq[simp]: "(y \<bullet> \<sigma>) r;r \<tau> =  (\<tau> y) \<bullet> (\<sigma> r;r \<tau>)"
  apply (rule ext)
  apply (case_tac x)
  unfolding seqrr_def apply simp 
  apply simp
  done

theorem RAssoc[simp]: "(\<rho> r;r \<sigma>) r;r \<tau> = \<rho> r;r \<sigma> r;r \<tau>"
  unfolding seqrr_def by simp

interpretation rrr: 
  substable3 "Var 0" Suc "\<lambda> x. x" Var Suc Var "\<lambda> x. x" Suc Var "\<lambda> x. x"
  by unfold_locales 

lemma rrr_comp_cong_ext: assumes 1: "\<sigma> r;r \<tau> = \<rho>"
  shows "extr \<sigma> r;r extr \<tau> = extr \<rho>"
proof simp
  have            "0 \<bullet> (\<sigma> r;r (\<tau> r;r Suc))
                 = 0 \<bullet> ((\<sigma> r;r \<tau>) r;r Suc)" by simp
  also have "... = 0 \<bullet> (\<rho> r;r Suc)" using 1 by simp
  finally show "0 \<bullet> (\<sigma> r;r (\<tau> r;r Suc)) = 0 \<bullet> (\<rho> r;r Suc)" .
qed

theorem rename_fusion:
  shows "rename \<sigma> (rename \<rho> M) = rename (\<rho> r;r \<sigma>) M"
  unfolding rename_def 
proof (rule rrr.map_fusion)
  show " \<forall>x. var_s.map_abt \<sigma> (Var (\<rho> x)) = Var ((\<rho> r;r \<sigma>) x)"
    unfolding seqrr_def by simp
next
  show " \<forall>\<sigma> \<tau> \<rho>.
       (\<forall>x. var_s.map_abt \<tau> (Var (\<sigma> x)) = Var (\<rho> x)) \<longrightarrow>
       (\<forall>x. var_s.map_abt (var_s.ext \<tau>) (Var (var_s.ext \<sigma> x)) = Var (var_s.ext \<rho> x))"
  proof clarify
    fix \<sigma> :: "var sub" and \<tau> \<rho> x
    assume "\<forall>x. var_s.map_abt \<tau> (Var (\<sigma> x)) = Var (\<rho> x)"
    then have "\<sigma> r;r \<tau> = \<rho>" unfolding seqrr_def by simp
    then have "extr \<sigma> r;r extr \<tau> = extr \<rho>" by (rule rrr_comp_cong_ext)
    then have "(extr \<sigma> r;r extr \<tau>) x = (extr \<rho>) x" by simp
    then show "var_s.map_abt (var_s.ext \<tau>) (Var (var_s.ext \<sigma> x)) = Var (var_s.ext \<rho> x)"
      unfolding seqrr_def extr_def by simp
  qed
qed

end