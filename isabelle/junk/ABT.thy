theory ABT
  imports Main
begin

type_synonym var = nat

datatype 'op ABT =
  Var var
  | App 'op "('op Arg) list"
and 'op Arg =
  Trm "'op ABT"
| Bnd "'op Arg"

type_synonym 'v sub = "var \<Rightarrow> 'v"

fun cons_aux :: "'v \<Rightarrow> 'v sub \<Rightarrow> 'v sub" where
  "(cons_aux v \<sigma>) 0 = v" |
  "(cons_aux v \<sigma>) (Suc x) = \<sigma> x"

definition cons :: "'v \<Rightarrow> 'v sub \<Rightarrow> 'v sub" (infixl "\<bullet>" 75) where
  "v \<bullet> \<sigma> \<equiv> cons_aux v \<sigma>"

(********************** locale substable ***************************)
locale substable =
  fixes trm :: "'op ABT" (* just for purposes of talking about 'op *)
  and shift :: "'v \<Rightarrow> 'v" ("\<Up>")
  and var2val :: "var \<Rightarrow>'v" ("\<lfloor>_\<rfloor>")
  and quote :: "'v \<Rightarrow> 'op ABT"
  assumes var2val_lift: "\<lfloor>Suc x\<rfloor> \<equiv> \<Up> \<lfloor>x\<rfloor>"
begin

  abbreviation lift_sub :: "'v sub \<Rightarrow> 'v sub" ("\<Up>") where
    "\<Up> \<sigma> x \<equiv> \<Up> (\<sigma> x)"
  
  abbreviation extend :: "'v sub \<Rightarrow> 'v sub" where
    "extend \<sigma> \<equiv> \<lfloor>0\<rfloor> \<bullet> (\<Up> \<sigma>)"
  
  fun map_abt :: "'v sub \<Rightarrow> 'op ABT \<Rightarrow> 'op ABT" ("\<llangle>_\<rrangle>_" 70)
    and map_arg :: "'v sub \<Rightarrow> 'op Arg \<Rightarrow> 'op Arg" ("\<llangle>_\<rrangle>\<^sub>a_" 70)
    where
   "\<llangle>\<sigma>\<rrangle> (Var x) = quote (\<sigma> x)" |
   "\<llangle>\<sigma>\<rrangle> (App op args) = App op (map (map_arg \<sigma>) args)" |
   "\<llangle>\<sigma>\<rrangle>\<^sub>a (Trm M) = Trm (\<llangle>\<sigma>\<rrangle> M)" |
   map_arg_bnd:"\<llangle>\<sigma>\<rrangle>\<^sub>a (Bnd A) = Bnd (\<llangle>extend \<sigma>\<rrangle>\<^sub>a A)" 

end

(********************** locale substable2 **************************************)
locale substable2 = L: substable trm s v2v q + R: substable trm s' v2v' q'
    for trm and s and v2v and q and s' and q' and v2v'
begin
  
  abbreviation cong :: "'b sub \<Rightarrow> 'c sub \<Rightarrow> bool" (infixl "\<cong>" 30) where
    "\<sigma> \<cong> \<tau> \<equiv> \<forall> x. q (\<sigma> x) =  q' (\<tau> x)"
  
  abbreviation map_cong_P1 :: "'a ABT \<Rightarrow> bool" where
    "map_cong_P1 M \<equiv> \<forall> \<sigma> \<tau>. \<sigma> \<cong> \<tau> \<longrightarrow> (\<forall> \<sigma> \<tau>. \<sigma> \<cong> \<tau> \<longrightarrow> L.extend \<sigma> \<cong> R.extend \<tau> )
            \<longrightarrow> L.map_abt \<sigma> M = R.map_abt \<tau> M"
  
  abbreviation map_cong_P2 :: "'a Arg \<Rightarrow> bool" where
    "map_cong_P2 A \<equiv> \<forall> \<sigma> \<tau>. \<sigma> \<cong> \<tau> \<longrightarrow> (\<forall> \<sigma> \<tau>. \<sigma> \<cong> \<tau> \<longrightarrow> L.extend \<sigma> \<cong> R.extend \<tau> )
            \<longrightarrow> L.map_arg \<sigma> A = R.map_arg \<tau> A"
  
  lemma map_cong_aux: "map_cong_P1 M"
    by (induction M rule: ABT.induct[of map_cong_P1 map_cong_P2]) 
       (auto simp add: L.map_arg_bnd R.map_arg_bnd)
  
  theorem map_cong: assumes 1: "\<sigma> \<cong> \<tau>" and 2: "\<And> \<sigma> \<tau>. \<sigma> \<cong> \<tau> \<Longrightarrow> L.extend \<sigma> \<cong> R.extend \<tau>"
    shows "L.map_abt \<sigma> M = R.map_abt \<tau> M"
    using 1 2 map_cong_aux[of M] by blast

end

(********************** locale substable3 **************************************)
locale substable3 = S1: substable trm s1 v2v1 q1 + S2: substable trm s2 v2v2 q2
    + S3: substable trm s3 v2v3 q3
    for trm and s1 and v2v1 and q1 and s2 and q2 and v2v2 and s3 and q3 and v2v3
begin
  
  (*   (\<sigma> ; \<tau>) = \<rho>    *)
  abbreviation comp_cong :: "'c sub \<Rightarrow> 'b sub \<Rightarrow> 'd sub \<Rightarrow> bool" where
    "comp_cong \<tau> \<sigma> \<rho> \<equiv> \<forall> x. S2.map_abt \<tau> (q1 (\<sigma> x)) = q3 (\<rho> x)"
  
  abbreviation map_fusion_P1 :: "'a ABT \<Rightarrow> bool" where
    "map_fusion_P1 M \<equiv> \<forall> \<sigma> \<tau> \<rho>. comp_cong \<tau> \<sigma> \<rho> 
          \<longrightarrow> S2.map_abt \<tau> (S1.map_abt \<sigma> M) = S3.map_abt \<rho> M"
  abbreviation map_fusion_P2 :: "'a Arg \<Rightarrow> bool" where
    "map_fusion_P2 M \<equiv> \<forall> \<sigma> \<tau> \<rho>. comp_cong \<tau> \<sigma> \<rho> 
          \<longrightarrow> S2.map_arg \<tau> (S1.map_arg \<sigma> M) = S3.map_arg \<rho> M"
  
  lemma map_fusion_aux: 
    assumes 1: "\<forall> \<sigma> \<tau> \<rho>. comp_cong \<tau> \<sigma> \<rho> \<longrightarrow> comp_cong (S2.extend \<tau>) (S1.extend \<sigma>) (S3.extend \<rho>)"
    shows "map_fusion_P1 M"
    apply (induction M rule: ABT.induct[of map_fusion_P1 map_fusion_P2])
    apply force
      apply force
     apply force
    apply simp apply clarify using 1 apply fast
    done
  
  theorem map_fusion:
    assumes 1: "comp_cong \<tau> \<sigma> \<rho>"
    and 2: "\<forall> \<sigma> \<tau> \<rho>. comp_cong \<tau> \<sigma> \<rho> \<longrightarrow> comp_cong (S2.extend \<tau>) (S1.extend \<sigma>) (S3.extend \<rho>)"
    shows "S2.map_abt \<tau> (S1.map_abt \<sigma> M) = S3.map_abt \<rho> M"
    using map_fusion_aux 1 2 by fast

end

(********************** locale abt_predicate **************************************)

locale abt_predicate =
  fixes op_pred :: "'op \<Rightarrow> 't list list \<Rightarrow> 't list \<Rightarrow> 't \<Rightarrow> bool"
begin

inductive wf_abt :: "'t list \<Rightarrow> 'op ABT \<Rightarrow> 't \<Rightarrow> bool" ("_\<turnstile>_:_" 55) 
  and wf_args :: "'t list \<Rightarrow> 't list list \<Rightarrow> ('op Arg) list \<Rightarrow> 't list \<Rightarrow> bool" ("_;_\<turnstile>\<^sub>+_:_") 
  and wf_arg :: "'t list \<Rightarrow> 't list \<Rightarrow> 'op Arg \<Rightarrow> 't \<Rightarrow> bool" ("_;_\<turnstile>\<^sub>a_:_") where
  wf_var[intro!]: "\<lbrakk> nth \<Gamma> x = T \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> Var x : T" |
  wf_app[intro!]: "\<lbrakk> \<Gamma>; Bss \<turnstile>\<^sub>+ args : Ts; op_pred op Bss Ts T \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> App op args : T" |
  wf_trm[intro!]: "\<Gamma> \<turnstile> M : T \<Longrightarrow> \<Gamma>; Bs \<turnstile>\<^sub>a Trm M : T" |
  wf_bnd[intro!]: "T' # \<Gamma>; Bs \<turnstile>\<^sub>a A : T \<Longrightarrow> \<Gamma>; T' # Bs \<turnstile>\<^sub>a Bnd A : T" |
  wf_nil[intro!]: "\<Gamma>; [] \<turnstile>\<^sub>+ [] : []" |
  wf_cons[intro!]: "\<lbrakk> \<Gamma>; Bs \<turnstile>\<^sub>a A : T; \<Gamma>; Bss \<turnstile>\<^sub>+ As : Ts\<rbrakk> \<Longrightarrow> \<Gamma>; Bs#Bss \<turnstile>\<^sub>+ A#As : T#Ts"

(*
inductive_cases
  wf_var_elim[elim!]: "\<Gamma> \<turnstile> Var x : T" and
  wf_app_elim[elim!]: "\<Gamma> \<turnstile> App op args : T" and
  wf_trm_elim[elim!]: "\<Gamma>; Bs \<turnstile>\<^sub>a Trm M : T" and
  wf_bnd_elim[elim!]: "\<Gamma>; Bs \<turnstile>\<^sub>a Bnd A : T" and
  wf_cons_elim[elim!]: "\<Gamma>; Bss \<turnstile>\<^sub>+ As : Ts"
*)

end

end