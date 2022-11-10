theory AbstractBindingTrees
  imports Main ABT Rename
begin

abbreviation shift :: "('op ABT) sub" ("\<up>") where
  "\<up> x \<equiv> Var (Suc x)"

abbreviation shift_many :: "nat \<Rightarrow> ('op ABT) sub" ("\<up>") where
  "\<up> k x \<equiv> Var (k + x)"

interpretation abt_s: substable "Var 0" "rename Suc" "Var" "\<lambda> x. x"
  apply unfold_locales
  apply (auto simp add: rename_def)
  done
 
definition exts :: "('op ABT) sub \<Rightarrow> ('op ABT) sub" where
  "exts \<sigma> \<equiv> abt_s.ext \<sigma>"

definition subst :: "('op ABT) sub \<Rightarrow> 'op ABT \<Rightarrow> 'op ABT" ("\<llangle>_\<rrangle>") where
  "\<llangle> \<sigma> \<rrangle> \<equiv> abt_s.map_abt \<sigma>"

abbreviation ren_sub :: "var sub \<Rightarrow> ('op ABT) sub" ("\<lceil>_\<rceil>") where
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
 "ren_sub.cong \<sigma> \<tau> \<Longrightarrow> ren_sub.cong (extr \<sigma>) (exts \<tau>)"
proof clarify
  fix x
  assume st: "ren_sub.cong \<sigma> \<tau>" 
  show "\<lceil>extr \<sigma>\<rceil> x = (exts \<tau>) x" 
  proof (cases x)
    case 0
    then show ?thesis unfolding exts_def by simp
  next
    case (Suc y)
    with Suc have "\<lceil>extr \<sigma>\<rceil> x = Var (Suc (\<sigma> y))" by (simp add: cons_def seqrr_def)
    also have "... = rename Suc (Var (\<sigma> y))" unfolding rename_def by simp
    also have "... = rename Suc (\<tau> y)" using st by simp
    also have "... = exts \<tau> x" using Suc unfolding exts_def by (simp add: cons_def)
    finally show ?thesis .
  qed  
qed

theorem rename_subst: "rename \<rho> M = \<llangle> \<lceil> \<rho> \<rceil> \<rrangle> M"
proof -
  have 1: "ren_sub.cong \<rho> \<lceil>\<rho>\<rceil>" by auto
  from 1 cong_ext have "var_s.map_abt \<rho> M = abt_s.map_abt \<lceil>\<rho>\<rceil> M" 
    unfolding extr_def exts_def apply (rule ren_sub.map_cong) by simp
  then show ?thesis unfolding subst_def rename_def by auto
qed

lemma lift_seq_up: "abt_s.lift_sub \<sigma> = \<sigma> ; \<up>"
  apply (rule ext)
  unfolding seqss_def shift_def using rename_subst[of Suc] apply auto done

lemma ren_suc_shift: "\<lceil>Suc\<rceil> = \<up>"
  unfolding shift_def by simp

lemma exts_cons_seq: "exts \<sigma> = Var 0 \<bullet> (\<sigma> ; \<up>)"
proof -
  have 1: "(\<lambda> x. rename Suc (\<sigma> x)) = (\<lambda> x. \<llangle> \<lceil> Suc \<rceil> \<rrangle> (\<sigma> x))"
    using rename_subst[of Suc] by auto
  have "exts \<sigma> = Var 0 \<bullet> (\<lambda> x. \<llangle> \<lceil> Suc \<rceil> \<rrangle> (\<sigma> x))" using 1 unfolding exts_def by simp
  also have "... = Var 0 \<bullet> (\<sigma> ; \<up>)" unfolding seqss_def by simp
  finally show "exts \<sigma> = Var 0 \<bullet> (\<sigma> ; \<up>)" .
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

lemma rss_comp_cong_ext: assumes 1: "\<rho> r; \<sigma> = \<tau>" shows "(extr \<rho>) r; (exts \<sigma>) = (exts \<tau>)"
proof (simp add: exts_cons_seq)
  have "Var 0 \<bullet> (\<rho> r; \<sigma> ; \<lceil>Suc\<rceil>) = Var 0 \<bullet> ((\<rho> r; \<sigma>) ; \<lceil>Suc\<rceil>)" by simp
  also have "... = Var 0 \<bullet> (\<tau> ; \<lceil>Suc\<rceil>)" using 1 by simp
  finally show "Var 0 \<bullet> (\<rho> r; \<sigma> ; \<lceil>Suc\<rceil>) = Var 0 \<bullet> (\<tau> ; \<lceil>Suc\<rceil>)" .
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
    then have 1: "(extr \<sigma>) r; (exts \<tau>) = (exts \<rho>)"
      by (rule rss_comp_cong_ext) 
    have "rss.comp_cong (abt_s.ext \<tau>) (var_s.ext \<sigma>) (abt_s.ext \<rho>)"
      apply auto apply (case_tac x) apply force 
    proof -
      fix x
      have "(extr \<sigma> r; exts \<tau>) x = (exts \<rho>) x " using 1 by auto
      then show "abt_s.ext \<tau> (var_s.ext \<sigma> x) = abt_s.ext \<rho> x"
        unfolding extr_def exts_def seqrs_def .
    qed      
  }
  then have 3: "\<forall>\<sigma> \<tau> \<rho>. rss.comp_cong \<tau> \<sigma> \<rho> \<longrightarrow> rss.comp_cong (exts \<tau>) (var_s.ext \<sigma>) (exts \<rho>)"
    unfolding exts_def by blast
  from 2 3 have "abt_s.map_abt \<sigma> (var_s.map_abt \<rho> M) = abt_s.map_abt \<tau> M"
    unfolding exts_def by (rule rss.map_fusion)
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
  shows "rename (extr \<rho>) (exts \<sigma> x) = exts \<tau> x"
proof (cases x)
  case 0
  then show ?thesis unfolding exts_def by simp 
next
  case (Suc y)
  have            "((exts \<sigma>) ;r (extr \<rho>)) x 
                 = rename (extr \<rho>) (rename Suc (\<sigma> y))" using Suc seqsr_def unfolding exts_def by auto
  also have "... = rename (Suc r;r (extr \<rho>)) (\<sigma> y)" 
    by (rule rename_fusion[of "(extr \<rho>)" Suc "\<sigma> y"])
  also have "... = rename (\<rho> r;r Suc) (\<sigma> y)" by simp
  also have "... = rename Suc (rename \<rho> (\<sigma> y))" using rename_fusion[of Suc \<rho> "\<sigma> y"] by auto
  also have "... = rename Suc ((\<sigma> ;r \<rho>) y)" unfolding seqsr_def ..
  also have "... = rename Suc (\<tau> y)" using cc by simp
  also have "... = exts \<tau> x" using Suc unfolding exts_def by (simp add: cons_def)
  finally have "((exts \<sigma>) ;r (extr \<rho>)) x = exts \<tau> x" unfolding exts_def by simp
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
    then have "rename (extr \<tau>) (exts \<sigma> x) = exts \<rho> x" by (rule srs_comp_cong_ext)
    then show "var_s.map_abt (var_s.ext \<tau>) (abt_s.ext \<sigma> x) = abt_s.ext \<rho> x"
      unfolding rename_def extr_def exts_def by fast
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
  shows "((exts \<sigma>) ; (exts \<rho>)) x = exts \<tau> x"
proof (cases x)
  case 0
  then show ?thesis unfolding exts_def by (simp add: subst_def)
next
  case (Suc y)
  thm subst_rename_fusion
  have "(exts \<sigma> ; exts \<rho>) x = \<llangle>exts \<rho>\<rrangle> (exts \<sigma> x)" unfolding seqss_def by simp
  also have "... = \<llangle>exts \<rho>\<rrangle> (rename Suc (\<sigma> y))" using Suc unfolding exts_def by simp
  also have "... = \<llangle>Suc r; exts \<rho>\<rrangle> (\<sigma> y)" by (rule subst_rename_fusion) simp
  also have "... = \<llangle> \<rho> ;r Suc \<rrangle> (\<sigma> y)" unfolding seqsr_def seqrs_def exts_def by simp  
  also have "... = rename Suc (\<llangle>\<rho>\<rrangle> (\<sigma> y))" using rename_subst_fusion[of Suc \<rho> "\<sigma> y"] by simp
  also have "... = rename Suc (\<tau> y)" using 1 unfolding seqss_def by auto
  also have "... = exts \<tau> x" using Suc unfolding exts_def by (simp add: cons_def)
  finally show ?thesis .
qed

theorem subst_subst_fusion: "\<llangle>\<rho>\<rrangle> (\<llangle>\<sigma>\<rrangle> M) = \<llangle>\<sigma> ; \<rho>\<rrangle> M"
proof -
  have 1: "sss.comp_cong \<rho> \<sigma> (\<sigma> ; \<rho>)" unfolding seqss_def subst_def by auto
  from 1 have "abt_s.map_abt \<rho> (abt_s.map_abt \<sigma> M) = abt_s.map_abt (\<sigma> ; \<rho>) M"
  proof (rule sss.map_fusion, clarify)
    fix \<sigma> \<tau> \<rho> x assume "sss.comp_cong \<tau> \<sigma> \<rho>"
    then have "\<sigma> ; \<tau> = \<rho>" using seqss_eq_ssscc[of \<tau> \<sigma> \<rho>] by simp
    then have "((exts \<sigma>) ; (exts \<tau>)) x = exts \<rho> x" by (rule sss_comp_cong_ext)
    then show "abt_s.map_abt (abt_s.ext \<tau>) (abt_s.ext \<sigma> x) = abt_s.ext \<rho> x" 
      unfolding seqss_def subst_def exts_def by simp
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

declare exts_cons_seq[simp]

theorem subst_commute: "(\<llangle> exts \<sigma>\<rrangle> N) [ \<llangle> \<sigma> \<rrangle> M ] = \<llangle> \<sigma> \<rrangle> (N [ M ])"
  by simp

theorem commute_subst: " \<llangle> \<sigma> \<rrangle> (N [ M ]) = (\<llangle> exts \<sigma>\<rrangle> N) [ \<llangle> \<sigma> \<rrangle> M ]"
  using subst_commute by simp


lemma rename_subst_cons[simp]: "\<lceil>y \<bullet> \<rho>\<rceil> = Var y \<bullet> \<lceil>\<rho>\<rceil>"
  apply (rule ext) 
  apply (case_tac x)
   apply simp
  apply simp
  done

lemma rename_subst_seq[simp]: "\<lceil>\<rho> r;r \<sigma>\<rceil> = \<lceil>\<rho>\<rceil> ; \<lceil>\<sigma>\<rceil>"
proof (rule ext)
  fix x
  have "\<lceil>\<rho> r;r \<sigma>\<rceil> x = Var (\<sigma> (\<rho> x))" unfolding seqrr_def by simp
  also have "... = \<llangle>\<lceil>\<sigma>\<rceil>\<rrangle> (Var (\<rho> x))" unfolding subst_def by simp
  also have "... = \<llangle>\<lceil>\<sigma>\<rceil>\<rrangle> (\<lceil>\<rho>\<rceil> x)" by simp
  also have "... = (\<lceil>\<rho>\<rceil> ; \<lceil>\<sigma>\<rceil>) x" unfolding seqss_def by simp
  finally show "\<lceil>\<rho> r;r \<sigma>\<rceil> x = (\<lceil>\<rho>\<rceil> ; \<lceil>\<sigma>\<rceil>) x" .
qed

declare rename_subst[simp]

theorem rename_subst_commute: "(rename (extr \<rho>) N) [ rename \<rho> M ] = rename \<rho> (N[M])"
  by simp 

definition subst_two :: "'op ABT \<Rightarrow> 'op ABT \<Rightarrow> 'op ABT" ("_\<lbrace>_\<rbrace>" 60) where
 "N \<lbrace> M \<rbrace> = \<llangle> exts (M \<bullet> \<iota>) \<rrangle> N"
declare subst_two_def[simp]

theorem substitution: "M[N][L] = M\<lbrace>L\<rbrace>[N[L]]"
  by simp

theorem exts_sub_cons: "(\<llangle>exts \<sigma>\<rrangle> N)[V] = \<llangle>V \<bullet> \<sigma>\<rrangle> N" 
  by simp

end