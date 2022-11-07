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
 
abbreviation exts :: "('op ABT) sub \<Rightarrow> ('op ABT) sub" where
  "exts \<sigma> \<equiv> abt_s.ext \<sigma>"

definition subst :: "('op ABT) sub \<Rightarrow> 'op ABT \<Rightarrow> 'op ABT" ("\<llangle>_\<rrangle>") where
  "\<llangle> \<sigma> \<rrangle> \<equiv> abt_s.map_abt \<sigma>"

abbreviation ren_sub :: "var sub \<Rightarrow> ('op ABT) sub" ("\<lceil>_\<rceil>") where
  "\<lceil>\<rho>\<rceil> x \<equiv> Var (\<rho> x)"

fun subst_zero :: "'op ABT \<Rightarrow> var \<Rightarrow> 'op ABT" where
  "subst_zero M 0 = M" |
  "subst_zero M (Suc x) = Var x"

abbreviation subst_one :: "'op ABT \<Rightarrow> 'op ABT \<Rightarrow> 'op ABT" ("_[_]" 70) where
  "subst_one N M \<equiv> \<llangle> subst_zero M \<rrangle> N"

definition seqss :: "('op ABT) sub \<Rightarrow> ('op ABT) sub \<Rightarrow> ('op ABT) sub" (infixl ";" 60) where
  "(\<sigma> ; \<tau>) x \<equiv> \<llangle>\<tau>\<rrangle> (\<sigma> x)"

definition seqrs :: "var sub \<Rightarrow> ('op ABT) sub \<Rightarrow> ('op ABT) sub" ("_ r; _") where
  "(\<rho> r; \<tau>) x \<equiv> \<tau> (\<rho> x)"

definition seqsr :: "('op ABT) sub \<Rightarrow> var sub \<Rightarrow> ('op ABT) sub" ("_ ;r _") where
  "(\<sigma> ;r \<rho>) x \<equiv> rename \<rho> (\<sigma> x)"

definition id :: "('op ABT) sub" where
  "id x \<equiv> Var x"

lemma lift_seq_suc: "abt_s.lift_sub \<sigma> = \<sigma> ;r Suc"
  unfolding seqsr_def by simp

theorem IdL[simp]: "id ; \<sigma> = \<sigma>"
  unfolding subst_def id_def seqss_def by simp

theorem ShiftId[simp]:  "(\<up> ; id) = \<up>"
  unfolding subst_def seqss_def id_def shift_def by simp

theorem VarId[simp]: "\<llangle>id\<rrangle> (Var x) = Var x"
  unfolding subst_def id_def by simp

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

theorem subst_id[simp]: "\<llangle>id\<rrangle> M = M"
  unfolding subst_def id_def by (rule abt_sqs.map_abt_id) simp
  
theorem IdR[simp]: "\<sigma> ; id = \<sigma>"
  unfolding seqss_def by (rule ext) simp

theorem ConsSeq[simp]: "(M \<bullet> \<sigma>); \<tau> = \<llangle> \<tau> \<rrangle> M \<bullet> (\<sigma> ; \<tau>)"
  apply (rule ext)
  apply (case_tac x)
  unfolding seqss_def apply simp 
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
    then show ?thesis by simp
  next
    case (Suc y)
    with Suc have "\<lceil>extr \<sigma>\<rceil> x = Var (Suc (\<sigma> y))" by (simp add: cons_def seqrr_def)
    also have "... = rename Suc (Var (\<sigma> y))" unfolding rename_def by simp
    also have "... = rename Suc (\<tau> y)" using st by simp
    also have "... = exts \<tau> x" using Suc by (simp add: cons_def)
    finally show ?thesis .
  qed  
qed

theorem rename_subst: "rename \<rho> M = \<llangle> \<lceil> \<rho> \<rceil> \<rrangle> M"
proof -
  have 1: "ren_sub.cong \<rho> \<lceil>\<rho>\<rceil>" by auto
  from 1 cong_ext have "var_s.map_abt \<rho> M = abt_s.map_abt \<lceil>\<rho>\<rceil> M" 
    unfolding extr_def apply (rule ren_sub.map_cong) by simp
  then show ?thesis unfolding subst_def rename_def by auto
qed

lemma lift_seq_up: "abt_s.lift_sub \<sigma> = \<sigma> ; \<up>"
  apply (rule ext)
  unfolding seqss_def shift_def using rename_subst[of Suc] apply auto done

lemma ren_suc_shift[simp]: "\<lceil>Suc\<rceil> = \<up>"
  unfolding shift_def by simp

interpretation rss:
  substable3 "Var 0" Suc "\<lambda>x. x" Var "rename Suc" "\<lambda>x. x" Var "rename Suc" "\<lambda>x. x" Var
  by unfold_locales 

lemma rss_comp_cong_ext: "\<rho> r; \<sigma> = \<tau> \<Longrightarrow>
       rss.comp_cong (abt_s.ext \<sigma>) (extr \<rho>) (abt_s.ext \<tau>)"
  unfolding extr_def apply clarify
  apply (case_tac x)
  apply simp 
   apply (simp add: seqrs_def)
  done

lemma rsscc_eq_seqrs: "(\<rho> r; \<sigma> = \<tau>) = (rss.comp_cong \<sigma> \<rho> \<tau>)" 
  unfolding seqrs_def by auto

theorem subst_rename_fusion:
  assumes 1: "\<rho> r; \<sigma> = \<tau>"
  shows "\<llangle>\<sigma>\<rrangle> (rename \<rho> M) = \<llangle>\<tau>\<rrangle> M"
proof -
  have 2: "rss.comp_cong \<sigma> \<rho> \<tau>" using 1 unfolding seqrs_def by auto
  {
    fix \<sigma>::"var sub" and \<tau> :: "('op ABT) sub" and \<rho> x
    assume 4: "rss.comp_cong \<tau> \<sigma> \<rho>"
    then have "\<sigma> r; \<tau> = \<rho>" unfolding seqrs_def by simp
    then have "rss.comp_cong (abt_s.ext \<tau>) (extr \<sigma>) (abt_s.ext \<rho>)"
      by (rule rss_comp_cong_ext) 
  }
  then have 3: "\<forall>\<sigma> \<tau> \<rho>. rss.comp_cong \<tau> \<sigma> \<rho> \<longrightarrow> rss.comp_cong (exts \<tau>) (var_s.ext \<sigma>) (exts \<rho>)"
    unfolding extr_def by blast
  have "abt_s.map_abt \<sigma> (var_s.map_abt \<rho> M) = abt_s.map_abt \<tau> M"
    apply (rule rss.map_fusion)
    using 2 apply fast
    using 3 apply blast
    done
  then show ?thesis unfolding subst_def rename_def apply simp done  
qed


(*






interpretation srs: 
  substable3 "Var 0" 
  "rename Suc" Var "\<lambda> x. x" 
  Suc Var "\<lambda> x. x"
  "rename Suc" "\<lambda> x. x" Var
  by unfold_locales

lemma srscc_eq_seqsr[simp]: "(\<sigma> ;r \<rho> = \<tau>) = (srs.comp_cong \<rho> \<sigma> \<tau>)" by auto

lemma srs_comp_cong_ext: fixes x :: var
  assumes cc: "\<sigma> ;r \<rho> = \<tau>"
  shows "rename (extr \<rho>) (exts \<sigma> x) = exts \<tau> x"
proof (cases x)
  case 0
  then show ?thesis by (simp add: cons_def)
next
  case (Suc y)
  have            "((exts \<sigma>) ;r (extr \<rho>)) x 
                 = rename (extr \<rho>) (rename Suc (\<sigma> y))" using Suc by (simp add: cons_def)
  also have "... = rename (Suc r;r (extr \<rho>)) (\<sigma> y)" using rename_fusion[of "(extr \<rho>)" Suc "(\<lambda> x. (extr \<rho>) (Suc x))" "\<sigma> y"] by fast
  also have "... = rename (\<rho> r;r Suc) (\<sigma> y)" by (simp add: cons_def)
  also have "... = rename Suc (rename \<rho> (\<sigma> y))" using rename_fusion[of Suc \<rho> "\<rho> r;r Suc" "\<sigma> y"] by auto
  also have "... = rename Suc (\<tau> y)" using cc by auto
  also have "... = exts \<tau> x" using Suc by (simp add: cons_def)
  finally show ?thesis .
qed

(* This could instead be rename_map_fusion (more generic) *)
theorem rename_subst_fusion:
  assumes 1: "srs.comp_cong \<rho> \<sigma> \<tau>"
  shows "rename \<rho> (\<llangle>\<sigma>\<rrangle> M) = \<llangle>\<tau>\<rrangle> M"
  unfolding subst_def apply (rule srs.map_fusion)
  using 1 apply fast
  using srs_comp_cong_ext apply auto
  done

interpretation sss: 
  substable3 "Var 0" "rename Suc" Var "\<lambda> x. x"
   "rename Suc" "\<lambda> x. x" Var
   "rename Suc" "\<lambda> x. x" Var
  by unfold_locales

lemma ssscc_eq_seqss: "(\<sigma> ; \<rho> = \<tau>) = (sss.comp_cong \<rho> \<sigma> \<tau>)"
  unfolding subst_def by auto

lemma seqss_eq_ssscc: "(sss.comp_cong \<rho> \<sigma> \<tau>) = (\<sigma> ; \<rho> = \<tau>)"
  unfolding subst_def by auto

lemma sss_comp_cong_ext:
  fixes x :: var
  assumes 1: "(\<sigma> ; \<rho>) = \<tau>"
  shows "((exts \<sigma>) ; (exts \<rho>)) x = exts \<tau> x"
proof (cases x)
  case 0
  then show ?thesis by (simp add: cons_def subst_def)
next
  case (Suc y)
  have "(exts \<sigma> ; exts \<rho>) x = ((\<sigma> ;r Suc) ; (exts \<rho>)) y" using Suc by (simp add: cons_def)
  also have "... = \<llangle>Suc r; exts \<rho>\<rrangle> (\<sigma> y)" using subst_rename_fusion[of "exts \<rho>" Suc "Suc r; exts \<rho>"] by auto
  also have "... = rename Suc (\<llangle>\<rho>\<rrangle> (\<sigma> y))" 
    using rename_subst_fusion[of Suc \<rho> "Suc r; exts \<rho>" "\<sigma> y"] by (auto simp add: cons_def)
  also have "... = rename Suc (\<tau> y)" using 1 unfolding subst_def by auto
  also have "... = exts \<tau> x" using Suc by (simp add: cons_def)
  finally show ?thesis .
qed

theorem subst_subst_fusion: "\<llangle>\<rho>\<rrangle> (\<llangle>\<sigma>\<rrangle> M) = \<llangle>\<sigma> ; \<rho>\<rrangle> M"
  unfolding subst_def apply (rule sss.map_fusion)
   apply force
proof clarify
  fix \<sigma> \<tau> \<rho> x
  assume 1: "sss.comp_cong \<tau> \<sigma> \<rho>" 
  from 1 have "\<sigma> ; \<tau> = \<rho>" unfolding subst_def by auto
  then have "(exts \<sigma> ; exts \<tau>) x = exts \<rho> x" by (rule sss_comp_cong_ext)
  then show "abt_s.map_abt (exts \<tau>) (exts \<sigma> x) = exts \<rho> x" unfolding subst_def by simp
qed


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
*)


end