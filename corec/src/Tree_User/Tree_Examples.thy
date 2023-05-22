(*<*)
header {* Motivating Examples *}

theory Tree_Examples
imports Tree_Lib
begin
(*>*)

section {* Sum *}

definition pls :: "tree \<Rightarrow> tree \<Rightarrow> tree" where
  "pls xs ys = dtor_corec_J (\<lambda>(xs, ys). (val xs + val ys, map Inr (zip (sub xs) (sub ys)))) (xs, ys)"

lemma val_pls[simp]: "val (pls t u) = val t + val u"
  unfolding pls_def J.dtor_corec map_pre_J_def BNF_Comp.id_bnf_comp_def by simp

lemma sub_pls[simp]: "sub (pls t u) = map (split pls) (zip (sub t) (sub u))"
  unfolding pls_def[abs_def] J.dtor_corec map_pre_J_def BNF_Comp.id_bnf_comp_def by simp

lemma pls_code[code]: "pls t u = Node (val t + val u) (map (split pls) (zip (sub t) (sub u)))"
  by (metis J.ctor_dtor prod.collapse val_pls sub_pls)

lemma pls_uniform: "pls t u = alg\<rho>1 (t, u)"
  unfolding pls_def
  apply (rule fun_cong[OF sym[OF J.dtor_corec_unique]])
  unfolding alg\<rho>1
  by (simp add: map_pre_J_def BNF_Comp.id_bnf_comp_def fun_eq_iff convol_def \<rho>1_def alg\<rho>1_def)



section {* Shuffle product *}

definition prd :: "tree \<Rightarrow> tree \<Rightarrow> tree" where
  "prd t u = corecUU1 (\<lambda>(t, u). GUARD1 (val t * val u, 
     map (\<lambda>(t', u'). PLS1 (CONT1 (t, u'), CONT1 (t', u))) (zip (sub t) (sub u)))) (t, u)"

lemma val_prd[simp]: "val (prd t u) = val t * val u"
  unfolding prd_def corecUU1
  by (simp add: map_pre_J_def BNF_Comp.id_bnf_comp_def J.dtor_ctor eval1_leaf1')

lemma sub_prd[simp]:
  "sub (prd t u) = map (\<lambda>(t', u'). pls (prd t u') (prd t' u)) (zip (sub t) (sub u))"
  apply (subst prd_def)
  unfolding corecUU1 prod.case
  by (simp add: map_pre_J_def BNF_Comp.id_bnf_comp_def J.dtor_ctor eval1_leaf1'
    eval1_\<oo>\<pp>1 alg\<Lambda>1_Inr o_eq_dest[OF Abs_\<Sigma>1_natural] pls_uniform prd_def split_beta)

lemma prd_code[code]: "prd t u =
  Node (val t * val u) (map (\<lambda>(t', u'). pls (prd t u') (prd t' u)) (zip (sub t) (sub u)))"
  by (metis J.ctor_dtor prod.collapse val_prd sub_prd)

lemma prd_uniform: "prd t u = alg\<rho>2 (t, u)"
  unfolding prd_def
  apply (rule fun_cong[OF sym[OF corecUU1_unique]])
  apply (rule iffD1[OF dtor_J_o_inj])
  unfolding alg\<rho>2
  apply (simp add: map_pre_J_def BNF_Comp.id_bnf_comp_def fun_eq_iff J.dtor_ctor
    \<rho>2_def Let_def convol_def eval2_\<oo>\<pp>2 eval1_\<oo>\<pp>1 eval1_leaf1'
    o_eq_dest[OF Abs_\<Sigma>1_natural] o_eq_dest[OF Abs_\<Sigma>2_natural] alg\<Lambda>2_Inl alg\<rho>2_def split_beta)
  done


section {* Coinduction Up-To Congruence *}

lemma Node_uniform: "Node x ts = eval0 (gg0 (x, map leaf0 ts))"
  by (rule iffD1[OF J.dtor_inject])
    (simp add: map_pre_J_def BNF_Comp.id_bnf_comp_def J.dtor_ctor o_eq_dest[OF eval0_gg0] eval0_leaf0)

lemma genCngdd0_Node: "\<lbrakk>x1 = x2; list_all2 (genCngdd0 R) ts1 ts2\<rbrakk> \<Longrightarrow> 
  genCngdd0 R (Node x1 ts1) (Node x2 ts2)"
  unfolding Node_uniform
  apply (rule genCngdd0_eval0)
  apply (rule rel_funD[OF gg0_transfer])
  unfolding rel_pre_J_def BNF_Comp.id_bnf_comp_def vimage2p_def
  apply (rule rel_funD[OF rel_funD[OF Pair_transfer], rotated])
   apply (erule rel_funD[OF rel_funD[OF map_transfer], rotated])
  apply (rule leaf0_transfer)
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

lemma genCngdd1_Node: "\<lbrakk>x1 = x2; list_all2 (genCngdd1 R) ts1 ts2\<rbrakk> \<Longrightarrow> 
  genCngdd1 R (Node x1 ts1) (Node x2 ts2)"
  apply (subst I1.idem_Cl[symmetric])
  apply (rule genCngdd0_genCngdd1)
  apply (rule genCngdd0_Node)
  apply (auto intro: predicate2D[OF list.rel_mono])
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

lemma genCngdd2_Node: "\<lbrakk>x1 = x2; list_all2 (genCngdd2 R) ts1 ts2\<rbrakk> \<Longrightarrow> 
  genCngdd2 R (Node x1 ts1) (Node x2 ts2)"
  apply (subst I2.idem_Cl[symmetric])
  apply (rule genCngdd1_genCngdd2)
  apply (rule genCngdd1_Node)
  apply (auto intro: predicate2D[OF list.rel_mono])
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

lemma tree_coinduct[case_names Eq_tree, case_conclusion Eq_tree val sub]:
  assumes "R s s'" "\<And>s s'. R s s' \<Longrightarrow> val s = val s' \<and> list_all2 R (sub s) (sub s')"
  shows "s = s'"
using assms(1) proof (rule mp[OF J.dtor_coinduct, rotated], safe)
  fix a b
  assume "R a b"
  from assms(2)[OF this] show "F_rel R (dtor_J a) (dtor_J b)"
    by (cases "dtor_J a" "dtor_J b" rule: prod.exhaust[case_product prod.exhaust])
      (auto simp: rel_pre_J_def vimage2p_def BNF_Comp.id_bnf_comp_def)
qed

lemma tree_coinduct0[case_names Eq_tree, case_conclusion Eq_tree val sub]:
  assumes "R s s'" "\<And>s s'. R s s' \<Longrightarrow> val s = val s' \<and> list_all2 (genCngdd0 R) (sub s) (sub s')"
  shows "s = s'"
using assms(1) proof (rule mp[OF coinductionU_genCngdd0, rotated], safe)
  fix a b
  assume "R a b"
  from assms(2)[OF this] show "F_rel (genCngdd0 R) (dtor_J a) (dtor_J b)"
    by (cases "dtor_J a" "dtor_J b" rule: prod.exhaust[case_product prod.exhaust])
      (auto simp: rel_pre_J_def vimage2p_def BNF_Comp.id_bnf_comp_def)
qed

lemma tree_coinduct1[case_names Eq_tree, case_conclusion Eq_tree val sub]:
  assumes "R s s'" "\<And>s s'. R s s' \<Longrightarrow> val s = val s' \<and> list_all2 (genCngdd1 R) (sub s) (sub s')"
  shows "s = s'"
using assms(1) proof (rule mp[OF coinductionU_genCngdd1, rotated], safe)
  fix a b
  assume "R a b"
  from assms(2)[OF this] show "F_rel (genCngdd1 R) (dtor_J a) (dtor_J b)"
    by (cases "dtor_J a" "dtor_J b" rule: prod.exhaust[case_product prod.exhaust])
      (auto simp: rel_pre_J_def vimage2p_def BNF_Comp.id_bnf_comp_def)
qed

lemma tree_coinduct2[case_names Eq_tree, case_conclusion Eq_tree val sub]:
  assumes "R s s'" "\<And>s s'. R s s' \<Longrightarrow> val s = val s' \<and> list_all2 (genCngdd2 R) (sub s) (sub s')"
  shows "s = s'"
using assms(1) proof (rule mp[OF coinductionU_genCngdd2, rotated], safe)
  fix a b
  assume "R a b"
  from assms(2)[OF this] show "F_rel (genCngdd2 R) (dtor_J a) (dtor_J b)"
    by (cases "dtor_J a" "dtor_J b" rule: prod.exhaust[case_product prod.exhaust])
      (auto simp: rel_pre_J_def vimage2p_def BNF_Comp.id_bnf_comp_def)
qed


section {* Proofs by Coinduction Up-To Congruence *}

lemma pls_assoc: "pls (pls t u) zs = pls t (pls u zs)"
  by (coinduction arbitrary: t u zs rule: tree_coinduct) (force simp: list_all2_iff in_set_zip)

lemma pls_commute: "pls t u = pls u t"
  by (coinduction arbitrary: t u rule: tree_coinduct) (force simp: list_all2_iff in_set_zip)

lemma pls_commute_assoc: "pls t (pls u zs) = pls u (pls t zs)"
  by (metis pls_assoc pls_commute)

lemmas pls_ac_simps = pls_assoc pls_commute pls_commute_assoc

lemma prd_commute: "prd t u = prd u t"
proof (coinduction arbitrary: t u rule: tree_coinduct1)
  case Eq_tree
  have ?sub unfolding sub_prd
    by (subst pls_commute) (fastforce simp: list_all2_iff in_set_zip intro!: genCngdd1_pls)
  then show ?case by simp
qed

lemma prd_distribL: "prd xs (pls ys zs) = pls (prd xs ys) (prd xs zs)"
proof (coinduction arbitrary: xs ys zs rule: tree_coinduct1)
  case Eq_tree
  have "\<And>a b c d. pls (pls a b) (pls c d) = pls (pls a c) (pls b d)" by (metis pls_assoc pls_commute)
  then have ?sub by (fastforce simp: list_all2_iff in_set_zip intro!: genCngdd1_pls)
  then show ?case by (simp add: algebra_simps)
qed

lemma prd_distribR: "prd (pls xs ys) zs = pls (prd xs zs) (prd ys zs)"
proof (coinduction arbitrary: xs ys zs rule: tree_coinduct1)
  case Eq_tree
  have "\<And>a b c d. pls (pls a b) (pls c d) = pls (pls a c) (pls b d)" by (metis pls_assoc pls_commute)
  then have ?sub by (fastforce simp: list_all2_iff in_set_zip intro!: genCngdd1_pls)
  then show ?case by (simp add: algebra_simps)
qed

lemma prd_assoc: "prd (prd xs ys) zs = prd xs (prd ys zs)"
proof (coinduction arbitrary: xs ys zs rule: tree_coinduct1)
  case Eq_tree
  have ?sub unfolding sub_prd zip_map1 zip_map2 list.map_comp
    by (fastforce simp: list_all2_iff in_set_zip pls_ac_simps prd_distribL prd_distribR
      intro!: genCngdd1_pls)
  then show ?case by simp
qed

lemma prd_commute_assoc: "prd xs (prd ys zs) = prd ys (prd xs zs)"
  by (metis prd_assoc prd_commute)

lemmas prd_ac_simps = prd_assoc prd_commute prd_commute_assoc

(*<*)
end
(*>*)
