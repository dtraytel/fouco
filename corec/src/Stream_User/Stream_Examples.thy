(*<*)
header {* Motivating Examples *}

theory Stream_Examples
imports Stream_Lib
begin
(*>*)

section {* Sum *}

definition pls :: "stream \<Rightarrow> stream \<Rightarrow> stream" where
  "pls xs ys = dtor_corec_J (\<lambda>(xs, ys). (head xs + head ys, Inr (tail xs, tail ys))) (xs, ys)"

lemma head_pls[simp]: "head (pls xs ys) = head xs + head ys"
  unfolding pls_def J.dtor_corec map_pre_J_def BNF_Comp.id_bnf_comp_def by simp

lemma tail_pls[simp]: "tail (pls xs ys) = pls (tail xs) (tail ys)"
  unfolding pls_def J.dtor_corec map_pre_J_def BNF_Comp.id_bnf_comp_def by simp

lemma pls_code[code]: "pls xs ys = SCons (head xs + head ys) (pls (tail xs) (tail ys))"
  by (metis J.ctor_dtor prod.collapse head_pls tail_pls)

lemma pls_uniform: "pls xs ys = alg\<rho>1 (xs, ys)"
  unfolding pls_def
  apply (rule fun_cong[OF sym[OF J.dtor_corec_unique]])
  unfolding alg\<rho>1
  by (simp add: map_pre_J_def BNF_Comp.id_bnf_comp_def fun_eq_iff convol_def \<rho>1_def alg\<rho>1_def)


section {* Onetwo *}

definition onetwo :: stream where
  "onetwo = corecUU0 (\<lambda>_. GUARD0 (1, SCONS0 (2, CONT0 ()))) ()"

lemma onetwo_code[code]: "onetwo = SCons 1 (SCons 2 onetwo)"
  apply (subst onetwo_def)
  unfolding corecUU0
  by (simp add: map_pre_J_def BNF_Comp.id_bnf_comp_def J.dtor_ctor eval0_leaf0'
    o_eq_dest[OF eval0_gg0] o_eq_dest[OF gg0_natural] onetwo_def)

definition onetwo' :: stream where
  "onetwo' = corecUU0 (\<lambda>_. SCONS0 (1, GUARD0 (2, CONT0 ()))) ()"

lemma onetwo'_code[code]: "onetwo' = SCons 1 (SCons 2 onetwo')"
  apply (subst onetwo'_def)
  unfolding corecUU0
  by (simp add: map_pre_J_def BNF_Comp.id_bnf_comp_def J.dtor_ctor eval0_leaf0'
    o_eq_dest[OF eval0_gg0] o_eq_dest[OF gg0_natural] onetwo'_def)

definition stutter :: stream where
  "stutter = corecUU1 (\<lambda>_. SCONS1 (1, GUARD1 (1, PLS1 (CONT1 (), CONT1 ())))) ()"

lemma stutter_code[code]: "stutter = SCons 1 (SCons 1 (pls stutter stutter))"
  apply (subst stutter_def)
  unfolding corecUU1 prod.case
  by (simp add: map_pre_J_def BNF_Comp.id_bnf_comp_def J.dtor_ctor eval1_leaf1'
    eval1_\<oo>\<pp>1 alg\<Lambda>1_Inr o_eq_dest[OF Abs_\<Sigma>1_natural]
    o_eq_dest[OF eval1_gg1] o_eq_dest[OF gg1_natural] pls_uniform stutter_def)


section {* Shuffle product *}

definition prd :: "stream \<Rightarrow> stream \<Rightarrow> stream" where
  "prd xs ys = corecUU1 (\<lambda>(xs, ys). GUARD1 (head xs * head ys,
     PLS1 (CONT1 (xs, tail ys), CONT1 (tail xs, ys)))) (xs, ys)"

lemma head_prd[simp]: "head (prd xs ys) = head xs * head ys"
  unfolding prd_def corecUU1
  by (simp add: map_pre_J_def BNF_Comp.id_bnf_comp_def J.dtor_ctor eval1_leaf1')

lemma tail_prd[simp]: "tail (prd xs ys) = pls (prd xs (tail ys)) (prd (tail xs) ys)"
  apply (subst prd_def)
  unfolding corecUU1 prod.case
  by (simp add: map_pre_J_def BNF_Comp.id_bnf_comp_def J.dtor_ctor eval1_leaf1'
    eval1_\<oo>\<pp>1 alg\<Lambda>1_Inr o_eq_dest[OF Abs_\<Sigma>1_natural] pls_uniform prd_def)

lemma prd_code[code]: "prd xs ys = SCons (head xs * head ys) (pls (prd xs (tail ys)) (prd (tail xs) ys))"
  by (metis J.ctor_dtor prod.collapse head_prd tail_prd)

lemma prd_uniform: "prd xs ys = alg\<rho>2 (xs, ys)"
  unfolding prd_def
  apply (rule fun_cong[OF sym[OF corecUU1_unique]])
  apply (rule iffD1[OF dtor_J_o_inj])
  unfolding alg\<rho>2
  apply (simp add: map_pre_J_def BNF_Comp.id_bnf_comp_def fun_eq_iff J.dtor_ctor
    \<rho>2_def Let_def convol_def eval2_\<oo>\<pp>2 eval1_\<oo>\<pp>1 eval1_leaf1'
    o_eq_dest[OF Abs_\<Sigma>1_natural] o_eq_dest[OF Abs_\<Sigma>2_natural] alg\<Lambda>2_Inl alg\<rho>2_def)
  done

abbreviation "scale n s \<equiv> prd (sconst n) s"

section {* Exponentiation *}

definition Exp :: "stream \<Rightarrow> stream" where
  "Exp = corecUU2 (\<lambda>xs. GUARD2 (exp (head xs), PRD2 (END2 (tail xs), CONT2 xs)))"

lemma head_Exp[simp]: "head (Exp xs) = exp (head xs)"
  unfolding Exp_def corecUU2
  by (simp add: map_pre_J_def BNF_Comp.id_bnf_comp_def J.dtor_ctor eval2_leaf2')

lemma tail_Exp[simp]: "tail (Exp xs) = prd (tail xs) (Exp xs)"
  apply (subst Exp_def)
  unfolding corecUU2
  by (simp add: map_pre_J_def BNF_Comp.id_bnf_comp_def J.dtor_ctor eval2_leaf2'
    eval2_\<oo>\<pp>2 alg\<Lambda>2_Inr o_eq_dest[OF Abs_\<Sigma>2_natural] prd_uniform Exp_def)

lemma Exp_code[code]: "Exp xs = SCons (exp (head xs)) (prd (tail xs) (Exp xs))"
  by (metis J.ctor_dtor prod.collapse head_Exp tail_Exp)

lemma Exp_uniform: "Exp xs = alg\<rho>3 (K3.I xs)"
  unfolding Exp_def
  apply (rule fun_cong[OF sym[OF corecUU2_unique]])
  apply (rule iffD1[OF dtor_J_o_inj])
  unfolding alg\<rho>3 o_def[symmetric] o_assoc
  apply (simp add: map_pre_J_def BNF_Comp.id_bnf_comp_def fun_eq_iff J.dtor_ctor
    \<rho>3_def Let_def convol_def eval3_\<oo>\<pp>3 eval2_\<oo>\<pp>2 eval2_leaf2' eval3_leaf3'
    o_eq_dest[OF Abs_\<Sigma>2_natural] o_eq_dest[OF Abs_\<Sigma>3_natural] alg\<Lambda>3_Inl alg\<rho>3_def)
  done


section {* Supremum *}

definition sup :: "stream fset \<Rightarrow> stream" where
  "sup = dtor_corec_J (\<lambda>F. (fMax (head |`| F), Inr (tail |`| F)))"

lemma head_sup[simp]: "head (sup F) = fMax (head |`| F)"
  unfolding sup_def J.dtor_corec map_pre_J_def BNF_Comp.id_bnf_comp_def by simp

lemma tail_sup[simp]: "tail (sup F) = sup (tail |`| F)"
  unfolding sup_def J.dtor_corec map_pre_J_def BNF_Comp.id_bnf_comp_def by simp

lemma sup_code[code]: "sup F = SCons (fMax (head |`| F)) (sup (tail |`| F))"
  by (metis J.ctor_dtor prod.collapse head_sup tail_sup)

lemma sup_uniform: "sup F = alg\<rho>4 F"
  unfolding sup_def
  apply (rule fun_cong[OF sym[OF J.dtor_corec_unique]])
  unfolding alg\<rho>4
  by (simp add: map_pre_J_def BNF_Comp.id_bnf_comp_def fun_eq_iff convol_def \<rho>4_def alg\<rho>4_def o_def)

section {* Skewed product *}

definition prd' :: "stream \<Rightarrow> stream \<Rightarrow> stream" where
  "prd' xs ys = corecUU5 (\<lambda>(xs, ys). GUARD5 (head xs * head ys,
     PRD5 (CONT5 (xs, tail ys), PLS5 (END5 (tail xs), END5 ys)))) (xs, ys)"

lemma prd'_uniform: "prd' xs ys = alg\<rho>5 (xs, ys)"
  unfolding prd'_def
  apply (rule fun_cong[OF sym[OF corecUU5_unique]])
  apply (rule iffD1[OF dtor_J_o_inj])
  unfolding alg\<rho>5
  apply (simp add: map_pre_J_def BNF_Comp.id_bnf_comp_def fun_eq_iff J.dtor_ctor
    \<rho>5_def Let_def convol_def eval5_\<oo>\<pp>5 eval4_\<oo>\<pp>4 eval3_\<oo>\<pp>3 eval2_\<oo>\<pp>2 eval1_\<oo>\<pp>1 eval5_leaf5'
    o_eq_dest[OF Abs_\<Sigma>1_natural] o_eq_dest[OF Abs_\<Sigma>2_natural] o_eq_dest[OF Abs_\<Sigma>3_natural]
      o_eq_dest[OF Abs_\<Sigma>4_natural] o_eq_dest[OF Abs_\<Sigma>5_natural] alg\<Lambda>5_Inl alg\<rho>5_def)
  done

lemma head_prd'[simp]: "head (prd' xs ys) = head xs * head ys"
  unfolding prd'_def corecUU5
  by (simp add: map_pre_J_def BNF_Comp.id_bnf_comp_def J.dtor_ctor eval5_leaf5')

lemma tail_prd'[simp]: "tail (prd' xs ys) = prd' (prd' xs (tail ys)) (pls (tail xs) ys)"
  apply (subst prd'_def, subst (2) prd'_uniform)
  unfolding corecUU5 prod.case
  by (simp add: map_pre_J_def BNF_Comp.id_bnf_comp_def J.dtor_ctor
    eval5_\<oo>\<pp>5 eval4_\<oo>\<pp>4 eval3_\<oo>\<pp>3 eval2_\<oo>\<pp>2 eval1_\<oo>\<pp>1 eval5_leaf5'
    alg\<Lambda>5_Inr alg\<Lambda>5_Inl alg\<Lambda>4_Inl alg\<Lambda>3_Inl alg\<Lambda>2_Inl alg\<Lambda>1_Inr
      o_eq_dest[OF Abs_\<Sigma>5_natural] o_eq_dest[OF Abs_\<Sigma>4_natural]
      o_eq_dest[OF Abs_\<Sigma>3_natural] o_eq_dest[OF Abs_\<Sigma>2_natural] o_eq_dest[OF Abs_\<Sigma>1_natural]
      pls_uniform prd'_def)

lemma prd'_code[code]:
  "prd' xs ys = SCons (head xs * head ys) (prd' (prd' xs (tail ys)) (pls (tail xs) ys))"
  by (metis J.ctor_dtor prod.collapse head_prd' tail_prd')



section {* Coinduction Up-To Congruence *}

lemma SCons_uniform: "SCons x s = eval0 (gg0 (x, leaf0 s))"
  by (rule iffD1[OF J.dtor_inject])
    (simp add: map_pre_J_def BNF_Comp.id_bnf_comp_def J.dtor_ctor o_eq_dest[OF eval0_gg0] eval0_leaf0')

lemma genCngdd0_SCons: "\<lbrakk>x1 = x2; genCngdd0 R xs1 xs2\<rbrakk> \<Longrightarrow> 
  genCngdd0 R (SCons x1 xs1) (SCons x2 xs2)"
  unfolding SCons_uniform
  apply (rule genCngdd0_eval0)
  apply (rule rel_funD[OF gg0_transfer])
  unfolding rel_pre_J_def BNF_Comp.id_bnf_comp_def vimage2p_def
  apply (rule rel_funD[OF rel_funD[OF Pair_transfer], rotated])
  apply (erule rel_funD[OF leaf0_transfer])
  apply assumption
  done

lemma genCngdd0_genCngdd1: "genCngdd0 R xs ys \<Longrightarrow> genCngdd1 R xs ys"
  unfolding genCngdd0_def cngdd0_def cptdd0_def genCngdd1_def cngdd1_def cptdd1_def eval1_embL1[symmetric]
  apply (intro allI impI)
  apply (erule conjE)+
  apply (drule spec)
  apply (erule mp conjI)+
  apply (erule rel_funD[OF rel_funD[OF comp_transfer]])
  apply (rule embL1_transfer)
  done

lemma genCngdd1_SCons: "\<lbrakk>x1 = x2; genCngdd1 R xs1 xs2\<rbrakk> \<Longrightarrow> 
  genCngdd1 R (SCons x1 xs1) (SCons x2 xs2)"
  apply (subst I1.idem_Cl[symmetric])
  apply (rule genCngdd0_genCngdd1)
  apply (rule genCngdd0_SCons)
  apply auto
  done

lemma genCngdd1_pls: "\<lbrakk>genCngdd1 R xs1 xs2; genCngdd1 R ys1 ys2\<rbrakk> \<Longrightarrow> 
  genCngdd1 R (pls xs1 ys1) (pls xs2 ys2)"
  unfolding pls_uniform alg\<rho>1_def o_apply
  apply (rule genCngdd1_eval1)
  apply (rule rel_funD[OF K1_as_\<Sigma>\<Sigma>1_transfer])
  apply simp
  done

lemma genCngdd1_genCngdd2: "genCngdd1 R xs ys \<Longrightarrow> genCngdd2 R xs ys"
  unfolding genCngdd1_def cngdd1_def cptdd1_def genCngdd2_def cngdd2_def cptdd2_def eval2_embL2[symmetric]
  apply (intro allI impI)
  apply (erule conjE)+
  apply (drule spec)
  apply (erule mp conjI)+
  apply (erule rel_funD[OF rel_funD[OF comp_transfer]])
  apply (rule embL2_transfer)
  done

lemma genCngdd2_SCons: "\<lbrakk>x1 = x2; genCngdd2 R xs1 xs2\<rbrakk> \<Longrightarrow> 
  genCngdd2 R (SCons x1 xs1) (SCons x2 xs2)"
  apply (subst I2.idem_Cl[symmetric])
  apply (rule genCngdd1_genCngdd2)
  apply (rule genCngdd1_SCons)
  apply auto
  done

lemma genCngdd2_pls: "\<lbrakk>genCngdd2 R xs1 xs2; genCngdd2 R ys1 ys2\<rbrakk> \<Longrightarrow> 
  genCngdd2 R (pls xs1 ys1) (pls xs2 ys2)"
  apply (subst I2.idem_Cl[symmetric])
  apply (rule genCngdd1_genCngdd2)
  apply (rule genCngdd1_pls)
  apply auto
  done

lemma genCngdd2_prd: "\<lbrakk>genCngdd2 R xs1 xs2; genCngdd2 R ys1 ys2\<rbrakk> \<Longrightarrow> 
  genCngdd2 R (prd xs1 ys1) (prd xs2 ys2)"
  unfolding prd_uniform alg\<rho>2_def o_apply
  apply (rule genCngdd2_eval2)
  apply (rule rel_funD[OF K2_as_\<Sigma>\<Sigma>2_transfer])
  apply simp
  done

lemma genCngdd2_genCngdd3: "genCngdd2 R xs ys \<Longrightarrow> genCngdd3 R xs ys"
  unfolding genCngdd2_def cngdd2_def cptdd2_def genCngdd3_def cngdd3_def cptdd3_def eval3_embL3[symmetric]
  apply (intro allI impI)
  apply (erule conjE)+
  apply (drule spec)
  apply (erule mp conjI)+
  apply (erule rel_funD[OF rel_funD[OF comp_transfer]])
  apply (rule embL3_transfer)
  done

lemma genCngdd3_SCons: "\<lbrakk>x1 = x2; genCngdd3 R xs1 xs2\<rbrakk> \<Longrightarrow> 
  genCngdd3 R (SCons x1 xs1) (SCons x2 xs2)"
  apply (subst I3.idem_Cl[symmetric])
  apply (rule genCngdd2_genCngdd3)
  apply (rule genCngdd2_SCons)
  apply auto
  done

lemma genCngdd3_pls: "\<lbrakk>genCngdd3 R xs1 xs2; genCngdd3 R ys1 ys2\<rbrakk> \<Longrightarrow> 
  genCngdd3 R (pls xs1 ys1) (pls xs2 ys2)"
  apply (subst I3.idem_Cl[symmetric])
  apply (rule genCngdd2_genCngdd3)
  apply (rule genCngdd2_pls)
  apply auto
  done

lemma genCngdd3_prd: "\<lbrakk>genCngdd3 R xs1 xs2; genCngdd3 R ys1 ys2\<rbrakk> \<Longrightarrow> 
  genCngdd3 R (prd xs1 ys1) (prd xs2 ys2)"
  apply (subst I3.idem_Cl[symmetric])
  apply (rule genCngdd2_genCngdd3)
  apply (rule genCngdd2_prd)
  apply auto
  done

lemma genCngdd3_Exp: "genCngdd3 R xs ys \<Longrightarrow> 
  genCngdd3 R (Exp xs) (Exp ys)"
  unfolding Exp_uniform alg\<rho>3_def o_apply
  apply (rule genCngdd3_eval3)
  apply (rule rel_funD[OF K3_as_\<Sigma>\<Sigma>3_transfer])
  apply simp
  done

lemma genCngdd3_genCngdd4: "genCngdd3 R xs ys \<Longrightarrow> genCngdd4 R xs ys"
  unfolding genCngdd3_def cngdd3_def cptdd3_def genCngdd4_def cngdd4_def cptdd4_def eval4_embL4[symmetric]
  apply (intro allI impI)
  apply (erule conjE)+
  apply (drule spec)
  apply (erule mp conjI)+
  apply (erule rel_funD[OF rel_funD[OF comp_transfer]])
  apply (rule embL4_transfer)
  done

lemma genCngdd4_SCons: "\<lbrakk>x1 = x2; genCngdd4 R xs1 xs2\<rbrakk> \<Longrightarrow> 
  genCngdd4 R (SCons x1 xs1) (SCons x2 xs2)"
  apply (subst I4.idem_Cl[symmetric])
  apply (rule genCngdd3_genCngdd4)
  apply (rule genCngdd3_SCons)
  apply auto
  done

lemma genCngdd4_pls: "\<lbrakk>genCngdd4 R xs1 xs2; genCngdd4 R ys1 ys2\<rbrakk> \<Longrightarrow> 
  genCngdd4 R (pls xs1 ys1) (pls xs2 ys2)"
  apply (subst I4.idem_Cl[symmetric])
  apply (rule genCngdd3_genCngdd4)
  apply (rule genCngdd3_pls)
  apply auto
  done

lemma genCngdd4_prd: "\<lbrakk>genCngdd4 R xs1 xs2; genCngdd4 R ys1 ys2\<rbrakk> \<Longrightarrow> 
  genCngdd4 R (prd xs1 ys1) (prd xs2 ys2)"
  apply (subst I4.idem_Cl[symmetric])
  apply (rule genCngdd3_genCngdd4)
  apply (rule genCngdd3_prd)
  apply auto
  done

lemma genCngdd4_Exp: "genCngdd4 R xs ys \<Longrightarrow> 
  genCngdd4 R (Exp xs) (Exp ys)"
  apply (subst I4.idem_Cl[symmetric])
  apply (rule genCngdd3_genCngdd4)
  apply (rule genCngdd3_Exp)
  apply auto
  done

lemma genCngdd4_sup: "rel_fset (genCngdd4 R) xs ys \<Longrightarrow> 
  genCngdd4 R (sup xs) (sup ys)"
  unfolding sup_uniform alg\<rho>4_def o_apply
  apply (rule genCngdd4_eval4)
  apply (rule rel_funD[OF K4_as_\<Sigma>\<Sigma>4_transfer])
  apply simp
  done

lemma genCngdd4_genCngdd5: "genCngdd4 R xs ys \<Longrightarrow> genCngdd5 R xs ys"
  unfolding genCngdd4_def cngdd4_def cptdd4_def genCngdd5_def cngdd5_def cptdd5_def eval5_embL5[symmetric]
  apply (intro allI impI)
  apply (erule conjE)+
  apply (drule spec)
  apply (erule mp conjI)+
  apply (erule rel_funD[OF rel_funD[OF comp_transfer]])
  apply (rule embL5_transfer)
  done

lemma genCngdd5_SCons: "\<lbrakk>x1 = x2; genCngdd5 R xs1 xs2\<rbrakk> \<Longrightarrow> 
  genCngdd5 R (SCons x1 xs1) (SCons x2 xs2)"
  apply (subst I5.idem_Cl[symmetric])
  apply (rule genCngdd4_genCngdd5)
  apply (rule genCngdd4_SCons)
  apply auto
  done

lemma genCngdd5_pls: "\<lbrakk>genCngdd5 R xs1 xs2; genCngdd5 R ys1 ys2\<rbrakk> \<Longrightarrow> 
  genCngdd5 R (pls xs1 ys1) (pls xs2 ys2)"
  apply (subst I5.idem_Cl[symmetric])
  apply (rule genCngdd4_genCngdd5)
  apply (rule genCngdd4_pls)
  apply auto
  done

lemma genCngdd5_prd: "\<lbrakk>genCngdd5 R xs1 xs2; genCngdd5 R ys1 ys2\<rbrakk> \<Longrightarrow> 
  genCngdd5 R (prd xs1 ys1) (prd xs2 ys2)"
  apply (subst I5.idem_Cl[symmetric])
  apply (rule genCngdd4_genCngdd5)
  apply (rule genCngdd4_prd)
  apply auto
  done

lemma genCngdd5_Exp: "genCngdd5 R xs ys \<Longrightarrow> 
  genCngdd5 R (Exp xs) (Exp ys)"
  apply (subst I5.idem_Cl[symmetric])
  apply (rule genCngdd4_genCngdd5)
  apply (rule genCngdd4_Exp)
  apply auto
  done

lemma genCngdd5_sup: "rel_fset (genCngdd5 R) xs ys \<Longrightarrow> 
  genCngdd5 R (sup xs) (sup ys)"
  apply (subst I5.idem_Cl[symmetric])
  apply (rule genCngdd4_genCngdd5)
  apply (rule genCngdd4_sup)
  apply (auto intro: predicate2D[OF fset.rel_mono])
  done

lemma genCngdd5_prd': "\<lbrakk>genCngdd5 R xs1 xs2; genCngdd5 R ys1 ys2\<rbrakk> \<Longrightarrow> 
  genCngdd5 R (prd' xs1 ys1) (prd' xs2 ys2)"
  unfolding prd'_uniform alg\<rho>5_def o_apply
  apply (rule genCngdd5_eval5)
  apply (rule rel_funD[OF K5_as_\<Sigma>\<Sigma>5_transfer])
  apply simp
  done

lemma stream_coinduct[case_names Eq_stream, case_conclusion Eq_stream head tail]:
  assumes "R s s'" "\<And>s s'. R s s' \<Longrightarrow> head s = head s' \<and> R (tail s) (tail s')"
  shows "s = s'"
using assms(1) proof (rule mp[OF J.dtor_coinduct, rotated], safe)
  fix a b
  assume "R a b"
  from assms(2)[OF this] show "F_rel R (dtor_J a) (dtor_J b)"
    by (cases "dtor_J a" "dtor_J b" rule: prod.exhaust[case_product prod.exhaust])
      (auto simp: rel_pre_J_def vimage2p_def BNF_Comp.id_bnf_comp_def)
qed

lemma stream_coinduct0[case_names Eq_stream, case_conclusion Eq_stream head tail]:
  assumes "R s s'" "\<And>s s'. R s s' \<Longrightarrow> head s = head s' \<and> genCngdd0 R (tail s) (tail s')"
  shows "s = s'"
using assms(1) proof (rule mp[OF coinductionU_genCngdd0, rotated], safe)
  fix a b
  assume "R a b"
  from assms(2)[OF this] show "F_rel (genCngdd0 R) (dtor_J a) (dtor_J b)"
    by (cases "dtor_J a" "dtor_J b" rule: prod.exhaust[case_product prod.exhaust])
      (auto simp: rel_pre_J_def vimage2p_def BNF_Comp.id_bnf_comp_def)
qed

lemma stream_coinduct1[case_names Eq_stream, case_conclusion Eq_stream head tail]:
  assumes "R s s'" "\<And>s s'. R s s' \<Longrightarrow> head s = head s' \<and> genCngdd1 R (tail s) (tail s')"
  shows "s = s'"
using assms(1) proof (rule mp[OF coinductionU_genCngdd1, rotated], safe)
  fix a b
  assume "R a b"
  from assms(2)[OF this] show "F_rel (genCngdd1 R) (dtor_J a) (dtor_J b)"
    by (cases "dtor_J a" "dtor_J b" rule: prod.exhaust[case_product prod.exhaust])
      (auto simp: rel_pre_J_def vimage2p_def BNF_Comp.id_bnf_comp_def)
qed

lemma stream_coinduct2[case_names Eq_stream, case_conclusion Eq_stream head tail]:
  assumes "R s s'" "\<And>s s'. R s s' \<Longrightarrow> head s = head s' \<and> genCngdd2 R (tail s) (tail s')"
  shows "s = s'"
using assms(1) proof (rule mp[OF coinductionU_genCngdd2, rotated], safe)
  fix a b
  assume "R a b"
  from assms(2)[OF this] show "F_rel (genCngdd2 R) (dtor_J a) (dtor_J b)"
    by (cases "dtor_J a" "dtor_J b" rule: prod.exhaust[case_product prod.exhaust])
      (auto simp: rel_pre_J_def vimage2p_def BNF_Comp.id_bnf_comp_def)
qed

lemma stream_coinduct3[case_names Eq_stream, case_conclusion Eq_stream head tail]:
  assumes "R s s'" "\<And>s s'. R s s' \<Longrightarrow> head s = head s' \<and> genCngdd3 R (tail s) (tail s')"
  shows "s = s'"
using assms(1) proof (rule mp[OF coinductionU_genCngdd3, rotated], safe)
  fix a b
  assume "R a b"
  from assms(2)[OF this] show "F_rel (genCngdd3 R) (dtor_J a) (dtor_J b)"
    by (cases "dtor_J a" "dtor_J b" rule: prod.exhaust[case_product prod.exhaust])
      (auto simp: rel_pre_J_def vimage2p_def BNF_Comp.id_bnf_comp_def)
qed

lemma stream_coinduct4[case_names Eq_stream, case_conclusion Eq_stream head tail]:
  assumes "R s s'" "\<And>s s'. R s s' \<Longrightarrow> head s = head s' \<and> genCngdd4 R (tail s) (tail s')"
  shows "s = s'"
using assms(1) proof (rule mp[OF coinductionU_genCngdd4, rotated], safe)
  fix a b
  assume "R a b"
  from assms(2)[OF this] show "F_rel (genCngdd4 R) (dtor_J a) (dtor_J b)"
    by (cases "dtor_J a" "dtor_J b" rule: prod.exhaust[case_product prod.exhaust])
      (auto simp: rel_pre_J_def vimage2p_def BNF_Comp.id_bnf_comp_def)
qed

lemma stream_coinduct5[case_names Eq_stream, case_conclusion Eq_stream head tail]:
  assumes "R s s'" "\<And>s s'. R s s' \<Longrightarrow> head s = head s' \<and> genCngdd5 R (tail s) (tail s')"
  shows "s = s'"
using assms(1) proof (rule mp[OF coinductionU_genCngdd5, rotated], safe)
  fix a b
  assume "R a b"
  from assms(2)[OF this] show "F_rel (genCngdd5 R) (dtor_J a) (dtor_J b)"
    by (cases "dtor_J a" "dtor_J b" rule: prod.exhaust[case_product prod.exhaust])
      (auto simp: rel_pre_J_def vimage2p_def BNF_Comp.id_bnf_comp_def)
qed


section {* Proofs by Coinduction Up-To Congruence *}

lemma pls_commute: "pls xs ys = pls ys xs"
  by (coinduction arbitrary: xs ys rule: stream_coinduct) auto

lemma prd_commute: "prd xs ys = prd ys xs"
proof (coinduction arbitrary: xs ys rule: stream_coinduct1)
  case Eq_stream
  then show ?case unfolding tail_prd
    by (subst pls_commute) (auto intro: genCngdd1_pls)
qed

lemma pls_assoc: "pls (pls xs ys) zs = pls xs (pls ys zs)"
  by (coinduction arbitrary: xs ys zs rule: stream_coinduct) auto

lemma pls_commute_assoc: "pls xs (pls ys zs) = pls ys (pls xs zs)"
  by (metis pls_assoc pls_commute)

lemmas pls_ac_simps = pls_assoc pls_commute pls_commute_assoc

lemma "onetwo = onetwo'"
  by (coinduction rule: stream_coinduct0)
    (auto simp: arg_cong[OF onetwo_code, of head] arg_cong[OF onetwo'_code, of head] J.dtor_ctor
      arg_cong[OF onetwo_code, of tail] arg_cong[OF onetwo'_code, of tail] intro: genCngdd0_SCons)

lemma prd_distribL: "prd xs (pls ys zs) = pls (prd xs ys) (prd xs zs)"
proof (coinduction arbitrary: xs ys zs rule: stream_coinduct1)
  case Eq_stream
  have "\<And>a b c d. pls (pls a b) (pls c d) = pls (pls a c) (pls b d)" by (metis pls_assoc pls_commute)
  then have ?tail by (auto intro!: genCngdd1_pls)
  then show ?case by (simp add: algebra_simps)
qed

lemma prd_distribR: "prd (pls xs ys) zs = pls (prd xs zs) (prd ys zs)"
proof (coinduction arbitrary: xs ys zs rule: stream_coinduct1)
  case Eq_stream
  have "\<And>a b c d. pls (pls a b) (pls c d) = pls (pls a c) (pls b d)" by (metis pls_assoc pls_commute)
  then have ?tail by (auto intro!: genCngdd1_pls)
  then show ?case by (simp add: algebra_simps)
qed

lemma prd_assoc: "prd (prd xs ys) zs = prd xs (prd ys zs)"
proof (coinduction arbitrary: xs ys zs rule: stream_coinduct1)
  case Eq_stream
  have ?tail unfolding tail_prd pls_ac_simps prd_distribL prd_distribR by (auto intro!: genCngdd1_pls)
  then show ?case by simp
qed

lemma prd_commute_assoc: "prd xs (prd ys zs) = prd ys (prd xs zs)"
  by (metis prd_assoc prd_commute)

lemmas prd_ac_simps = prd_assoc prd_commute prd_commute_assoc

lemma sconst_0[simp]: "same 0 = sconst 0"
  by (coinduction rule: stream_coinduct0) auto

lemma pls_sconst_0L[simp]: "pls (sconst 0) s = s"
  by (coinduction arbitrary: s rule: stream_coinduct) auto

lemma pls_sconst_0R[simp]: "pls s (sconst 0) = s"
  by (coinduction arbitrary: s rule: stream_coinduct) auto

lemma scale_0[simp]: "scale 0 s = sconst 0"
  apply (coinduction arbitrary: s rule: stream_coinduct1)
  apply simp
  apply (subst (5) pls_sconst_0L[of "sconst 0", symmetric])
  apply (rule genCngdd1_pls)
  apply auto
  done

lemma scale_Suc: "scale (Suc n) s = pls s (scale n s)"
  by (coinduction arbitrary: s rule: stream_coinduct1) auto

lemma scale_add: "scale (m + n) s = pls (scale m s) (scale n s)"
  by (induct m) (auto simp: scale_Suc pls_assoc)

lemma scale_mult: "scale (m * n) s = scale m (scale n s)"
  by (induct m) (auto simp: scale_Suc scale_add)

lemma sup_empty: "sup {||} = sconst 0"
  by (coinduction rule: stream_coinduct1) (auto simp: fMax_def)

lemma Exp_pls: "Exp (pls xs ys) = prd (Exp xs) (Exp ys)"
  by (coinduction arbitrary: xs ys rule: stream_coinduct2)
    (auto simp: exp_def power_add prd_distribR pls_commute prd_assoc prd_commute_assoc[of "Exp x" for x]
      intro!: genCngdd2_pls genCngdd2_prd)

(*<*)
end
(*>*)
