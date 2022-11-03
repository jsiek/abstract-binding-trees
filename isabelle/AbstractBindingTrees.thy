theory AbstractBindingTrees
  imports Main
begin

lemma map_id: "(\<And>x. x \<in> set xs \<Longrightarrow> f x = x) \<Longrightarrow> map f xs = xs"
  by (induction xs) auto

section "Abstract Binding Trees"

type_synonym var = nat

datatype 'op ABT =
  Var var
  | App 'op "('op Arg) list"
and 'op Arg =
  Trm "'op ABT"
| Bnd "'op Arg"


section "Substitutions"

type_synonym 'v sub = "var \<Rightarrow> 'v"

fun cons :: "'v \<Rightarrow> 'v sub \<Rightarrow> 'v sub" (infixl "\<bullet>" 65) where
  "(v \<bullet> \<sigma>) 0 = v" |
  "(v \<bullet> \<sigma>) (Suc x) = \<sigma> x"

abbreviation drop :: "nat \<Rightarrow> 'v sub \<Rightarrow> 'v sub" where
  "drop k \<sigma> x \<equiv> \<sigma> (k + x)"

locale substable =
  fixes trm :: "'op ABT" (* just for purposes of talking about 'op *)
  and shift :: "'v \<Rightarrow> 'v" ("\<Up>")
  and var2val :: "var \<Rightarrow>'v" ("\<lfloor>_\<rfloor>")
  and quote :: "'v \<Rightarrow> 'op ABT"
  assumes var2val_lift: "\<lfloor>Suc x\<rfloor> \<equiv> \<Up> \<lfloor>x\<rfloor>"
  and quote_var: "quote \<lfloor>0\<rfloor> = Var 0"
begin

abbreviation lift_sub :: "'v sub \<Rightarrow> 'v sub" ("\<Up>") where
  "\<Up> \<sigma> x \<equiv> \<Up> (\<sigma> x)"

abbreviation ext :: "'v sub \<Rightarrow> 'v sub" where
  "ext \<sigma> \<equiv> \<lfloor>0\<rfloor> \<bullet> \<Up> \<sigma>"

fun map_abt :: "'v sub \<Rightarrow> 'op ABT \<Rightarrow> 'op ABT"
  and map_arg :: "'v sub \<Rightarrow> 'op Arg \<Rightarrow> 'op Arg"
  where
 "map_abt \<sigma> (Var x) = quote (\<sigma> x)" |
 "map_abt \<sigma> (App op args) = App op (map (map_arg \<sigma>) args)" |
 "map_arg \<sigma> (Trm M) = Trm (map_abt \<sigma> M)" |
 "map_arg \<sigma> (Bnd A) = Bnd (map_arg (ext \<sigma>) A)" 

end

interpretation var_s: substable "Var 0" "Suc" "\<lambda> x. x" "Var"
  by unfold_locales auto

abbreviation shift :: "('op ABT) sub" ("\<up>") where
  "\<up> x \<equiv> Var (Suc x)"

abbreviation shift_many :: "nat \<Rightarrow> ('op ABT) sub" ("\<up>") where
  "\<up> k x \<equiv> Var (k + x)"

abbreviation rename :: "var sub \<Rightarrow> 'op ABT \<Rightarrow> 'op ABT" where
  "rename \<equiv> var_s.map_abt"

interpretation abt_s: substable "Var 0" "rename Suc" "Var" "\<lambda> x. x"
  by unfold_locales auto
 
abbreviation subst :: "('op ABT) sub \<Rightarrow> 'op ABT \<Rightarrow> 'op ABT" ("\<llangle>_\<rrangle>") where
  "\<llangle> \<sigma> \<rrangle> \<equiv> abt_s.map_abt \<sigma>"

abbreviation ren_sub :: "var sub \<Rightarrow> ('op ABT) sub" ("\<lceil>_\<rceil>") where
  "\<lceil>\<rho>\<rceil> x \<equiv> Var (\<rho> x)"

fun subst_zero :: "'op ABT \<Rightarrow> var \<Rightarrow> 'op ABT" where
  "subst_zero M 0 = M" |
  "subst_zero M (Suc x) = Var x"

abbreviation subst_one :: "'op ABT \<Rightarrow> 'op ABT \<Rightarrow> 'op ABT" ("_[_]" 70) where
  "subst_one N M \<equiv> \<llangle> subst_zero M \<rrangle> N"

abbreviation seq :: "('op ABT) sub \<Rightarrow> ('op ABT) sub \<Rightarrow> ('op ABT) sub" ("_;_") where
  "(\<sigma> ; \<tau>) x \<equiv> \<llangle>\<tau>\<rrangle> (\<sigma> x)"

abbreviation id :: "('op ABT) sub" where
  "id x \<equiv> Var x"

theorem IdL: "id; \<sigma> = \<sigma>"
  by simp

theorem ShiftId: shows "(\<up> ; id) = \<up>"
  by simp

theorem HeadCons: "(M \<bullet> \<sigma>) 0 = M"
  by simp

theorem ShiftCons: "\<up> ; (M \<bullet> \<sigma>) = \<sigma>"
  by simp

locale subst_quote_shift = substable +
  assumes quote_shift: "quote (\<Up> v) = rename Suc (quote v)"
begin

lemma id_ext: "(\<forall> x. quote (\<sigma> x) = Var x) \<Longrightarrow> quote ((ext \<sigma>) x) = Var x"
  apply (case_tac x)
  using quote_var apply force
  using quote_shift apply force
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
    apply simp apply clarify apply (rule map_id) apply blast
   apply force
  apply simp apply clarify using id_ext apply force
  done

theorem map_abt_id: 
  assumes 1: "\<And> x. quote (\<sigma> x) = Var x"
  shows "map_abt \<sigma> M = M" using 1 map_id_aux by fast

end

interpretation abt_sqs: subst_quote_shift "Var 0" "rename Suc" Var "\<lambda> x. x"
  by unfold_locales auto

theorem id_id: "\<llangle>id\<rrangle> M = M"
  by (rule abt_sqs.map_abt_id) simp
  
theorem IdR: "\<sigma>; id = \<sigma>"
  using id_id by auto

theorem ConsSeq[simp]: "(v \<bullet> \<sigma>); \<tau> = \<llangle> \<tau> \<rrangle> v \<bullet> (\<sigma> ; \<tau>)"
  apply (rule ext)
  apply (case_tac x)
   apply auto
  done

theorem DistSeq: "(M \<bullet> \<sigma>) ; \<tau> = (\<llangle>\<tau>\<rrangle> M) \<bullet> (\<sigma> ; \<tau>)"
  by simp

locale substable2 = L: substable trm s v2v q + R: substable trm s' v2v' q'
    for trm and s and v2v and q and s' and q' and v2v'
begin

abbreviation cong :: "'b sub \<Rightarrow> 'c sub \<Rightarrow> bool" (infixl "\<cong>" 30) where
  "\<sigma> \<cong> \<tau> \<equiv> \<forall> x. q (\<sigma> x) =  q' (\<tau> x)"

abbreviation P1 :: "'a ABT \<Rightarrow> bool" where
  "P1 M \<equiv> \<forall> \<sigma> \<tau>. \<sigma> \<cong> \<tau> \<longrightarrow> (\<forall> \<sigma> \<tau>. \<sigma> \<cong> \<tau> \<longrightarrow> L.ext \<sigma> \<cong> R.ext \<tau> )
          \<longrightarrow> L.map_abt \<sigma> M = R.map_abt \<tau> M"

abbreviation P2 :: "'a Arg \<Rightarrow> bool" where
  "P2 A \<equiv> \<forall> \<sigma> \<tau>. \<sigma> \<cong> \<tau> \<longrightarrow> (\<forall> \<sigma> \<tau>. \<sigma> \<cong> \<tau> \<longrightarrow> L.ext \<sigma> \<cong> R.ext \<tau> )
          \<longrightarrow> L.map_arg \<sigma> A = R.map_arg \<tau> A"

lemma map_cong_aux: "P1 M"
  by (induction M rule: ABT.induct[of P1 P2]) auto

theorem map_cong: assumes 1: "\<sigma> \<cong> \<tau>" and 2: "\<And> \<sigma> \<tau>. \<sigma> \<cong> \<tau> \<Longrightarrow> L.ext \<sigma> \<cong> R.ext \<tau>"
  shows "L.map_abt \<sigma> M = R.map_abt \<tau> M"
  using 1 2 map_cong_aux[of M] by blast

end

interpretation ren_sub: 
  substable2 "Var 0" Suc "\<lambda> x. x" Var "rename Suc" "\<lambda> x. x" Var
  by unfold_locales auto

thm ren_sub.map_cong

lemma cong_ext:
 "ren_sub.cong \<sigma> \<tau> \<Longrightarrow> ren_sub.cong (var_s.ext \<sigma>) (abt_s.ext \<tau>)"
proof clarify
  fix x
  assume st: "ren_sub.cong \<sigma> \<tau>" 
  show "\<lceil>var_s.ext \<sigma>\<rceil> x = (abt_s.ext \<tau>) x" 
  proof (cases x)
    case 0
    then show ?thesis by simp
  next
    case (Suc y)
    with Suc have "\<lceil>var_s.ext \<sigma>\<rceil> x = Var (Suc (\<sigma> y))" by simp
    also have "... = rename Suc (Var (\<sigma> y))" by simp
    also have "... = rename Suc (\<tau> y)" using st by simp
    also have "... = abt_s.ext \<tau> x" using Suc by simp
    finally show ?thesis .
  qed  
qed

theorem rename_subst: "rename \<rho> M = \<llangle> \<lceil> \<rho> \<rceil> \<rrangle> M"
  apply (rule ren_sub.map_cong)
   apply force
  using cong_ext apply blast
  done

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