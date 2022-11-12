theory AbstractBindingTrees
  imports Main ABT Rename
begin

definition shift :: "('op ABT) sub" ("\<up>") where
  "\<up> x \<equiv> Var (Suc x)"

abbreviation shift_many :: "nat \<Rightarrow> ('op ABT) sub" ("\<up>") where
  "\<up> k x \<equiv> Var (k + x)"

interpretation abt_s: substable "Var 0" "rename Suc" "Var" "\<lambda> x. x"
  apply unfold_locales
  apply (auto simp add: rename_def)
  done

definition ext :: "('op ABT) sub \<Rightarrow> ('op ABT) sub" where
  "ext \<sigma> \<equiv> abt_s.extend \<sigma>"

definition subst :: "('op ABT) sub \<Rightarrow> 'op ABT \<Rightarrow> 'op ABT" ("\<llangle>_\<rrangle>") where
  "\<llangle> \<sigma> \<rrangle> \<equiv> abt_s.map_abt \<sigma>"

definition subst_arg :: "('op ABT) sub \<Rightarrow> 'op Arg \<Rightarrow> 'op Arg" ("\<llangle>_\<rrangle>\<^sub>a") where
  "\<llangle> \<sigma> \<rrangle>\<^sub>a \<equiv> abt_s.map_arg \<sigma>"

definition ren_sub :: "var sub \<Rightarrow> ('op ABT) sub" ("\<lceil>_\<rceil>") where
  "\<lceil>\<rho>\<rceil> x \<equiv> Var (\<rho> x)"

definition seqss :: "('op ABT) sub \<Rightarrow> ('op ABT) sub \<Rightarrow> ('op ABT) sub" (infixr ";" 70) where
  "(\<sigma> ; \<tau>) x \<equiv> \<llangle>\<tau>\<rrangle> (\<sigma> x)"

definition seqrs :: "var sub \<Rightarrow> ('op ABT) sub \<Rightarrow> ('op ABT) sub" (infixr "r;" 70) where
  "(\<rho> r; \<tau>) x \<equiv> \<tau> (\<rho> x)"

definition seqsr :: "('op ABT) sub \<Rightarrow> var sub \<Rightarrow> ('op ABT) sub" (infixr ";r" 70) where
  "(\<sigma> ;r \<rho>) x \<equiv> rename \<rho> (\<sigma> x)"

definition \<iota> :: "('op ABT) sub" where
  "\<iota> x \<equiv> Var x"

definition subst_one :: "'op ABT \<Rightarrow> 'op ABT \<Rightarrow> 'op ABT" ("_[_]" 70) where
  "subst_one N M \<equiv> \<llangle> M \<bullet> \<iota> \<rrangle> N"
declare subst_one_def[simp]

lemma lift_seq_suc: "abt_s.lift_sub \<sigma> = \<sigma> ;r Suc"
  unfolding seqsr_def by simp

theorem IdL[simp]: "\<iota> ; \<sigma> = \<sigma>"
  unfolding subst_def \<iota>_def seqss_def by simp

theorem ShiftId[simp]:  "(\<up> ; \<iota>) = \<up>"
  unfolding subst_def seqss_def \<iota>_def shift_def by simp

theorem VarId[simp]: "\<llangle>\<iota>\<rrangle> (Var x) = Var x"
  unfolding subst_def \<iota>_def by simp

theorem HeadCons[simp]: "(M \<bullet> \<sigma>) 0 = M"
  unfolding cons_def subst_def by simp

theorem HeadConsSub[simp]: "\<llangle>M \<bullet> \<sigma>\<rrangle> (Var 0) = M"
  unfolding subst_def by simp

theorem TailCons[simp]: "(M \<bullet> \<sigma>) (Suc x) = \<sigma> x"
  unfolding cons_def by simp 

theorem TailConsSub[simp]: "\<llangle>M \<bullet> \<sigma>\<rrangle> (Var (Suc x)) = \<sigma> x"
  unfolding subst_def by simp

theorem VarSub: "\<llangle>\<sigma>\<rrangle> (Var x) = \<sigma> x"
  unfolding subst_def by simp

theorem AppSub[simp]: "\<llangle>\<sigma>\<rrangle> (App op args) = App op (map (\<llangle>\<sigma>\<rrangle>\<^sub>a) args)"
  by (simp add: subst_def subst_arg_def)

theorem TrmSub[simp]: "\<llangle>\<sigma>\<rrangle>\<^sub>a (Trm M) = Trm (\<llangle>\<sigma>\<rrangle> M)"
  by (simp add: subst_def subst_arg_def)

theorem BndSub[simp]: "\<llangle>\<sigma>\<rrangle>\<^sub>a (Bnd A) = Bnd (\<llangle>ext \<sigma>\<rrangle>\<^sub>a A)"
  by (simp add: ext_def subst_arg_def)

theorem ShiftCons[simp]: "\<up> ; (M \<bullet> \<sigma>) = \<sigma>"
  unfolding cons_def subst_def seqss_def shift_def by simp

interpretation abt_sqs: subst_quote_shift "Var 0" "rename Suc" Var "\<lambda> x. x"
  by unfold_locales auto

theorem subst_id[simp]: "\<llangle>\<iota>\<rrangle> M = M"
  unfolding subst_def \<iota>_def by (rule abt_sqs.map_abt_id) simp
  
theorem IdR[simp]: "\<sigma> ; \<iota> = \<sigma>"
  unfolding seqss_def by (rule ext) simp

theorem ConsSeq[simp]: "(M \<bullet> \<sigma>) ; \<tau> = \<llangle> \<tau> \<rrangle> M \<bullet> (\<sigma> ; \<tau>)"
  apply (rule ext)
  apply (case_tac x)
  unfolding seqss_def apply simp 
  apply simp
  done

theorem ConsSeqRS[simp]: "(y \<bullet> \<rho>) r; \<tau> = \<tau> y \<bullet> (\<rho> r; \<tau>)"
  apply (rule ext)
  apply (case_tac x)
  unfolding seqrs_def apply simp
  apply simp
  done

theorem ConsSeqSR[simp]: "(M \<bullet> \<sigma>) ;r \<rho> = rename \<rho> M \<bullet> (\<sigma> ;r \<rho>)"
  apply (rule ext)
  apply (case_tac x)
  unfolding seqsr_def apply simp
  apply simp
  done

interpretation ren_sub: 
  substable2 "Var 0" Suc "\<lambda> x. x" Var "rename Suc" "\<lambda> x. x" Var
  by unfold_locales auto

lemma cong_ext:
 "ren_sub.cong \<sigma> \<tau> \<Longrightarrow> ren_sub.cong (extr \<sigma>) (ext \<tau>)"
proof clarify
  fix x
  assume st: "ren_sub.cong \<sigma> \<tau>" 
  show "Var (extr \<sigma> x) = (ext \<tau>) x"
  proof (cases x)
    case 0
    then show ?thesis unfolding ext_def by simp
  next
    case (Suc y)
    with Suc have "Var (extr \<sigma> x) = Var (Suc (\<sigma> y))" by (simp add: cons_def seqrr_def)
    also have "... = rename Suc (Var (\<sigma> y))" unfolding rename_def by simp
    also have "... = rename Suc (\<tau> y)" using st by simp
    also have "... = ext \<tau> x" using Suc unfolding ext_def by (simp add: cons_def)
    finally show ?thesis .
  qed  
qed

theorem rename_subst: "rename \<rho> M = \<llangle> \<lceil> \<rho> \<rceil> \<rrangle> M"
proof -
  have 1: "ren_sub.cong \<rho> \<lceil>\<rho>\<rceil>" unfolding ren_sub_def by auto
  from 1 cong_ext have "var_s.map_abt \<rho> M = abt_s.map_abt \<lceil>\<rho>\<rceil> M" 
    unfolding extr_def ext_def apply (rule ren_sub.map_cong) by simp
  then show ?thesis unfolding subst_def rename_def by auto
qed

 (*
lemma lift_seq_up: "abt_s.lift_sub \<sigma> = \<sigma> ; \<up>"
  apply (rule ext)
  unfolding seqss_def shift_def  using rename_subst[of Suc] apply auto done
*)

lemma ext_cons_seq: "ext \<sigma> = Var 0 \<bullet> (\<sigma> ; \<up>)"
proof -
  have 1: "(\<lambda> x. rename Suc (\<sigma> x)) = (\<lambda> x. \<llangle> \<lceil> Suc \<rceil> \<rrangle> (\<sigma> x))"
    using rename_subst[of Suc] by auto
  have "ext \<sigma> = Var 0 \<bullet> (\<lambda> x. \<llangle> \<lceil> Suc \<rceil> \<rrangle> (\<sigma> x))" using 1 unfolding ext_def by simp
  also have "... = Var 0 \<bullet> (\<sigma> ; \<up>)" unfolding seqss_def shift_def ren_sub_def by simp
  finally show "ext \<sigma> = Var 0 \<bullet> (\<sigma> ; \<up>)" .
qed

interpretation rss:
  substable3 "Var 0" Suc "\<lambda>x. x" Var "rename Suc" "\<lambda>x. x" Var "rename Suc" "\<lambda>x. x" Var
  by unfold_locales 

theorem ShiftConsRS[simp]: "Suc r; (M \<bullet> \<sigma>) = \<sigma>"
  unfolding cons_def subst_def seqrs_def shift_def by simp

theorem assoc_RRS[simp]: "(\<rho> r;r \<sigma>) r; \<tau> = \<rho> r; (\<sigma> r; \<tau>)"
  unfolding seqrr_def seqrs_def by auto

theorem assoc_RSS[simp]: "(\<rho> r; \<sigma>) ; \<tau> = \<rho> r; (\<sigma> ; \<tau>)"
  unfolding seqrs_def seqss_def by auto

lemma rss_comp_cong_ext: assumes 1: "\<rho> r; \<sigma> = \<tau>" shows "(extr \<rho>) r; (ext \<sigma>) = (ext \<tau>)"
proof (simp add: ext_cons_seq)
  have "Var 0 \<bullet> (\<rho> r; \<sigma> ; \<up>) = Var 0 \<bullet> ((\<rho> r; \<sigma>) ; \<up>)" unfolding shift_def by simp
  also have "... = Var 0 \<bullet> (\<tau> ; \<up>)" using 1 by simp
  finally show "Var 0 \<bullet> (\<rho> r; \<sigma> ; \<up>) = Var 0 \<bullet> (\<tau> ; \<up>)" .
qed

lemma rsscc_eq_seqrs: "(\<rho> r; \<sigma> = \<tau>) = (rss.comp_cong \<sigma> \<rho> \<tau>)" 
  unfolding seqrs_def by auto

theorem subst_rename_fusion:
  assumes 1: "\<rho> r; \<sigma> = \<tau>"
  shows "\<llangle>\<sigma>\<rrangle> (rename \<rho> M) = \<llangle>\<tau>\<rrangle> M"
proof -
  have 2: "rss.comp_cong \<sigma> \<rho> \<tau>" using 1 rsscc_eq_seqrs by fast
  {
    fix \<sigma>::"var sub" and \<tau> :: "('op ABT) sub" and \<rho> x
    assume 4: "rss.comp_cong \<tau> \<sigma> \<rho>"
    then have "\<sigma> r; \<tau> = \<rho>" using rsscc_eq_seqrs by fast
    then have 1: "(extr \<sigma>) r; (ext \<tau>) = (ext \<rho>)"
      by (rule rss_comp_cong_ext) 
    have "rss.comp_cong (abt_s.extend \<tau>) (var_s.extend \<sigma>) (abt_s.extend \<rho>)"
      apply auto apply (case_tac x) apply force 
    proof -
      fix x
      have "(extr \<sigma> r; ext \<tau>) x = (ext \<rho>) x " using 1 by auto
      then show "abt_s.extend \<tau> (var_s.extend \<sigma> x) = abt_s.extend \<rho> x"
        unfolding extr_def ext_def seqrs_def .
    qed      
  }
  then have 3: "\<forall>\<sigma> \<tau> \<rho>. rss.comp_cong \<tau> \<sigma> \<rho> \<longrightarrow> rss.comp_cong (ext \<tau>) (var_s.extend \<sigma>) (ext \<rho>)"
    unfolding ext_def by blast
  from 2 3 have "abt_s.map_abt \<sigma> (var_s.map_abt \<rho> M) = abt_s.map_abt \<tau> M"
    unfolding ext_def by (rule rss.map_fusion)
  then show ?thesis unfolding subst_def rename_def by simp  
qed

theorem assoc_SRS[simp]: "(\<sigma> ;r \<rho>) ; \<tau> = \<sigma> ; (\<rho> r; \<tau>)"
  unfolding seqsr_def seqss_def seqrs_def apply (rule ext)
  apply (rule subst_rename_fusion)
  unfolding seqrs_def by simp

interpretation srs: 
  substable3 "Var 0" 
    "rename Suc" Var "\<lambda> x. x" 
    Suc Var "\<lambda> x. x"
    "rename Suc" "\<lambda> x. x" Var
  by unfold_locales

lemma srscc_eq_seqsr: "(\<sigma> ;r \<rho> = \<tau>) = (srs.comp_cong \<rho> \<sigma> \<tau>)" 
  unfolding seqsr_def rename_def by auto

lemma srs_comp_cong_ext: fixes x :: var
  assumes cc: "\<sigma> ;r \<rho> = \<tau>"
  shows "rename (extr \<rho>) (ext \<sigma> x) = ext \<tau> x"
proof (cases x)
  case 0
  then show ?thesis unfolding ext_def by simp 
next
  case (Suc y)
  have            "((ext \<sigma>) ;r (extr \<rho>)) x 
                 = rename (extr \<rho>) (rename Suc (\<sigma> y))" using Suc seqsr_def unfolding ext_def by auto
  also have "... = rename (Suc r;r (extr \<rho>)) (\<sigma> y)" 
    by (rule rename_fusion[of "(extr \<rho>)" Suc "\<sigma> y"])
  also have "... = rename (\<rho> r;r Suc) (\<sigma> y)" by simp
  also have "... = rename Suc (rename \<rho> (\<sigma> y))" using rename_fusion[of Suc \<rho> "\<sigma> y"] by auto
  also have "... = rename Suc ((\<sigma> ;r \<rho>) y)" unfolding seqsr_def ..
  also have "... = rename Suc (\<tau> y)" using cc by simp
  also have "... = ext \<tau> x" using Suc unfolding ext_def by (simp add: cons_def)
  finally have "((ext \<sigma>) ;r (extr \<rho>)) x = ext \<tau> x" unfolding ext_def by simp
  then show ?thesis unfolding seqsr_def by simp
qed

(* This could instead be rename_map_fusion (more generic) *)

theorem rename_subst_fusion: "rename \<rho> (\<llangle>\<sigma>\<rrangle> M) = \<llangle>\<sigma> ;r \<rho>\<rrangle> M"
proof -
  have rst: "\<sigma> ;r \<rho> = \<sigma> ;r \<rho>" by simp
  have "srs.comp_cong \<rho> \<sigma> (\<sigma> ;r \<rho>)" unfolding seqsr_def rename_def by simp 
  then have "var_s.map_abt \<rho> (abt_s.map_abt \<sigma> M) = abt_s.map_abt (\<sigma> ;r \<rho>) M"
  proof (rule srs.map_fusion, clarify)
    fix \<sigma> \<tau> \<rho> x assume "srs.comp_cong \<tau> \<sigma> \<rho>"
    then have "\<sigma> ;r \<tau> = \<rho>" unfolding seqsr_def rename_def by auto
    then have "rename (extr \<tau>) (ext \<sigma> x) = ext \<rho> x" by (rule srs_comp_cong_ext)
    then show "var_s.map_abt (var_s.extend \<tau>) (abt_s.extend \<sigma> x) = abt_s.extend \<rho> x"
      unfolding rename_def extr_def ext_def by fast
  qed
  then show "rename \<rho> (\<llangle>\<sigma>\<rrangle> M) = \<llangle>\<sigma> ;r \<rho>\<rrangle> M"
    unfolding rename_def subst_def by fast
qed

theorem assoc_SSR[simp]: "(\<sigma> ; \<tau>) ;r \<rho> = \<sigma> ; (\<tau> ;r \<rho>)"
proof (rule ext)
  fix x
  have "((\<sigma> ; \<tau>) ;r \<rho>) x = rename \<rho> (\<llangle>\<tau>\<rrangle> (\<sigma> x))" 
    unfolding seqsr_def seqss_def by simp
  also have "... = \<llangle>\<tau> ;r \<rho>\<rrangle> (\<sigma> x)"
    by (rule rename_subst_fusion)
  also have "... = (\<sigma> ; (\<tau> ;r \<rho>)) x"
    unfolding seqss_def ..
  finally show "((\<sigma> ; \<tau>) ;r \<rho>) x = (\<sigma> ; (\<tau> ;r \<rho>)) x" .
qed

interpretation sss: 
  substable3 "Var 0" "rename Suc" Var "\<lambda> x. x"
   "rename Suc" "\<lambda> x. x" Var
   "rename Suc" "\<lambda> x. x" Var
  by unfold_locales

lemma ssscc_eq_seqss: "(\<sigma> ; \<rho> = \<tau>) = (sss.comp_cong \<rho> \<sigma> \<tau>)"
  unfolding subst_def seqss_def by auto

lemma seqss_eq_ssscc: "(sss.comp_cong \<rho> \<sigma> \<tau>) = (\<sigma> ; \<rho> = \<tau>)"
  unfolding subst_def seqss_def by auto

lemma sss_comp_cong_ext:
  fixes x :: var
  assumes 1: "(\<sigma> ; \<rho>) = \<tau>"
  shows "((ext \<sigma>) ; (ext \<rho>)) x = ext \<tau> x"
proof (cases x)
  case 0
  then show ?thesis unfolding ext_def by (simp add: subst_def)
next
  case (Suc y)
  thm subst_rename_fusion
  have "(ext \<sigma> ; ext \<rho>) x = \<llangle>ext \<rho>\<rrangle> (ext \<sigma> x)" unfolding seqss_def by simp
  also have "... = \<llangle>ext \<rho>\<rrangle> (rename Suc (\<sigma> y))" using Suc unfolding ext_def by simp
  also have "... = \<llangle>Suc r; ext \<rho>\<rrangle> (\<sigma> y)" by (rule subst_rename_fusion) simp
  also have "... = \<llangle> \<rho> ;r Suc \<rrangle> (\<sigma> y)" unfolding seqsr_def seqrs_def ext_def by simp  
  also have "... = rename Suc (\<llangle>\<rho>\<rrangle> (\<sigma> y))" using rename_subst_fusion[of Suc \<rho> "\<sigma> y"] by simp
  also have "... = rename Suc (\<tau> y)" using 1 unfolding seqss_def by auto
  also have "... = ext \<tau> x" using Suc unfolding ext_def by (simp add: cons_def)
  finally show ?thesis .
qed

theorem subst_subst_fusion: "\<llangle>\<rho>\<rrangle> (\<llangle>\<sigma>\<rrangle> M) = \<llangle>\<sigma> ; \<rho>\<rrangle> M"
proof -
  have 1: "sss.comp_cong \<rho> \<sigma> (\<sigma> ; \<rho>)" unfolding seqss_def subst_def by auto
  from 1 have "abt_s.map_abt \<rho> (abt_s.map_abt \<sigma> M) = abt_s.map_abt (\<sigma> ; \<rho>) M"
  proof (rule sss.map_fusion, clarify)
    fix \<sigma> \<tau> \<rho> x assume "sss.comp_cong \<tau> \<sigma> \<rho>"
    then have "\<sigma> ; \<tau> = \<rho>" using seqss_eq_ssscc[of \<tau> \<sigma> \<rho>] by simp
    then have "((ext \<sigma>) ; (ext \<tau>)) x = ext \<rho> x" by (rule sss_comp_cong_ext)
    then show "abt_s.map_abt (abt_s.extend \<tau>) (abt_s.extend \<sigma> x) = abt_s.extend \<rho> x" 
      unfolding seqss_def subst_def ext_def by simp
  qed
  then show ?thesis unfolding subst_def by simp
qed

declare subst_subst_fusion[simp]

theorem assoc_SSS[simp]: "(\<sigma> ; \<tau>) ; \<rho> = \<sigma> ; (\<tau> ; \<rho>)"
proof (rule ext)
  fix x
  have "((\<sigma> ; \<tau>) ; \<rho>) x = \<llangle>\<rho>\<rrangle> (\<llangle>\<tau>\<rrangle> (\<sigma> x))" unfolding seqss_def by fast
  also have "... = \<llangle> \<tau> ; \<rho> \<rrangle> (\<sigma> x)" by simp
  also have "... = (\<sigma> ; (\<tau> ; \<rho>)) x" unfolding seqss_def by fast
  finally show "((\<sigma> ; \<tau>) ; \<rho>) x = (\<sigma> ; \<tau> ; \<rho>) x" .
qed

declare ext_cons_seq[simp]

theorem subst_commute: "(\<llangle> ext \<sigma>\<rrangle> N) [ \<llangle> \<sigma> \<rrangle> M ] = \<llangle> \<sigma> \<rrangle> (N [ M ])"
  by simp

theorem commute_subst: " \<llangle> \<sigma> \<rrangle> (N [ M ]) = (\<llangle> ext \<sigma>\<rrangle> N) [ \<llangle> \<sigma> \<rrangle> M ]"
  using subst_commute by simp

lemma rename_subst_cons[simp]: "\<lceil>y \<bullet> \<rho>\<rceil> = Var y \<bullet> \<lceil>\<rho>\<rceil>"
  apply (rule ext) 
  apply (case_tac x)
   unfolding ren_sub_def apply simp
  apply simp
  done

lemma rename_subst_seq[simp]: "\<lceil>\<rho> r;r \<sigma>\<rceil> = \<lceil>\<rho>\<rceil> ; \<lceil>\<sigma>\<rceil>"
proof (rule ext)
  fix x
  have "\<lceil>\<rho> r;r \<sigma>\<rceil> x = Var (\<sigma> (\<rho> x))" unfolding seqrr_def ren_sub_def by simp
  also have "... = \<llangle>\<lceil>\<sigma>\<rceil>\<rrangle> (Var (\<rho> x))" unfolding subst_def ren_sub_def by simp
  also have "... = \<llangle>\<lceil>\<sigma>\<rceil>\<rrangle> (\<lceil>\<rho>\<rceil> x)" unfolding ren_sub_def by simp
  also have "... = (\<lceil>\<rho>\<rceil> ; \<lceil>\<sigma>\<rceil>) x" unfolding seqss_def by simp
  finally show "\<lceil>\<rho> r;r \<sigma>\<rceil> x = (\<lceil>\<rho>\<rceil> ; \<lceil>\<sigma>\<rceil>) x" .
qed

declare rename_subst[simp]

theorem ren_suc_shift[simp]: "\<lceil>Suc\<rceil> = \<up>"
  unfolding shift_def ren_sub_def by simp

theorem rename_subst_commute: "(rename (extr \<rho>) N) [ rename \<rho> M ] = rename \<rho> (N[M])"
  by simp

definition subst_two :: "'op ABT \<Rightarrow> 'op ABT \<Rightarrow> 'op ABT" ("_\<lbrace>_\<rbrace>" 60) where
 "N \<lbrace> M \<rbrace> = \<llangle> ext (M \<bullet> \<iota>) \<rrangle> N"
declare subst_two_def[simp]

theorem substitution: "M[N][L] = M\<lbrace>L\<rbrace>[N[L]]"
  by simp

theorem ext_sub_cons: "(\<llangle>ext \<sigma>\<rrangle> N)[V] = \<llangle>V \<bullet> \<sigma>\<rrangle> N" 
  by simp

context abt_predicate
begin

  definition sub_pres :: "('op ABT) sub \<Rightarrow> 't list \<Rightarrow> 't list \<Rightarrow> bool" ("_:_\<rightharpoonup>_" 55) where
    "\<sigma> : \<Gamma> \<rightharpoonup> \<Gamma>' \<equiv> \<forall> x T. nth \<Gamma> x = T \<longrightarrow> \<Gamma>' \<turnstile> \<sigma> x : T"

  abbreviation wf_abt_sub_P :: "'t list \<Rightarrow> 'op ABT \<Rightarrow> 't \<Rightarrow> bool" where
    "wf_abt_sub_P \<Gamma> M T \<equiv> \<forall> \<sigma> \<Gamma>'. \<sigma> : \<Gamma> \<rightharpoonup> \<Gamma>' \<longrightarrow> \<Gamma>' \<turnstile> \<llangle>\<sigma>\<rrangle> M : T"

  abbreviation wf_arg_sub_P :: "'t list \<Rightarrow> 't list \<Rightarrow> 'op Arg \<Rightarrow> 't \<Rightarrow> bool" where
    "wf_arg_sub_P \<Gamma> Bs A T \<equiv> \<forall> \<sigma> \<Gamma>'. (\<sigma> : \<Gamma> \<rightharpoonup> \<Gamma>') \<longrightarrow> (\<Gamma>' ; Bs \<turnstile>\<^sub>a \<llangle>\<sigma>\<rrangle>\<^sub>a A : T)"

  abbreviation wf_args_sub_P :: "'t list \<Rightarrow> 't list list \<Rightarrow> ('op Arg) list \<Rightarrow> 't list \<Rightarrow> bool" where
    "wf_args_sub_P \<Gamma> Bss As Ts \<equiv> \<forall> \<sigma> \<Gamma>'. (\<sigma> : \<Gamma> \<rightharpoonup> \<Gamma>') \<longrightarrow> (\<Gamma>' ; Bss \<turnstile>\<^sub>+ map (\<llangle>\<sigma>\<rrangle>\<^sub>a) As : Ts)"

  lemma subst_pres_aux: "(\<Gamma> \<turnstile> M : T \<longrightarrow> wf_abt_sub_P \<Gamma> M T) 
      \<and> (\<Gamma>; Bss \<turnstile>\<^sub>+ As : Ts \<longrightarrow> wf_args_sub_P \<Gamma> Bss As Ts)
      \<and> (\<Gamma>; Bs \<turnstile>\<^sub>a A : T \<longrightarrow> wf_arg_sub_P \<Gamma> Bs A T)"
  proof (induction rule: wf_abt_wf_args_wf_arg.induct)
    case (wf_var \<Gamma> x T)
    then show ?case apply clarify unfolding VarSub sub_pres_def by auto
  next
    case (wf_app \<Gamma> Bss args Ts op T)
    then show ?case by auto 
  next
    case (wf_trm \<Gamma> M T Bs)
    then show ?case by auto
  next
    case (wf_bnd T' \<Gamma> Bs A T)
    show ?case apply clarify apply simp
    proof -
      fix \<sigma> \<Gamma>'
      assume sub_ok: "\<sigma> : \<Gamma> \<rightharpoonup> \<Gamma>'"
      have 1: "Var 0 \<bullet> (\<sigma> ; \<up>) : (T'#\<Gamma>) \<rightharpoonup> (T'#\<Gamma>')" unfolding sub_pres_def apply clarify
        apply (case_tac x) apply force
      proof -
        fix x T y assume x: "x = Suc y"
        have "\<Gamma>' \<turnstile> \<sigma> y : \<Gamma> ! y" using sub_ok sub_pres_def by simp
        then have "T' # \<Gamma>' \<turnstile> rename Suc (\<sigma> y):\<Gamma> ! y" using shift_pres by blast
        then have "T' # \<Gamma>' \<turnstile> \<llangle>\<up>\<rrangle> (\<sigma> y):\<Gamma> ! y" by simp
        then show "T' # \<Gamma>'\<turnstile>(Var 0 \<bullet> (\<sigma> ; \<up>)) x:(T' # \<Gamma>) ! x" 
          unfolding seqss_def x by simp 
      qed
      with wf_bnd.IH show "\<Gamma>';T' # Bs \<turnstile>\<^sub>a Bnd (\<llangle>Var 0 \<bullet> (\<sigma> ; \<up>)\<rrangle>\<^sub>a A) : T" by blast
    qed
  next
    case (wf_nil \<Gamma>)
    then show ?case by auto
  next
    case (wf_cons \<Gamma> Bs A T Bss As Ts)
    then show ?case by auto
  qed

  theorem subst_pres: "\<lbrakk> \<Gamma> \<turnstile> M : T; \<sigma> : \<Gamma> \<rightharpoonup> \<Gamma>' \<rbrakk> \<Longrightarrow> \<Gamma>' \<turnstile> \<llangle>\<sigma>\<rrangle> M : T"
    using subst_pres_aux by blast

end

end