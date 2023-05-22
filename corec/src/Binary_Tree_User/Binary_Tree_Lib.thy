theory Binary_Tree_Lib
imports "../Binary_Tree/Binary_Tree_Behavior_BNF" "../Binary_Tree/Binary_Tree_More_Corec_Upto2"
begin

(* todo: make them defs eventually: *)
type_synonym btree = J
abbreviation "val t \<equiv> fst (dtor_J t)"
abbreviation "left t \<equiv> fst (snd (dtor_J t))"
abbreviation "right t \<equiv> snd (snd (dtor_J t))"
abbreviation "Node n l r \<equiv> ctor_J (n, l, r)"
code_datatype ctor_J
declare J.dtor_ctor[code]

section {* Abbreviations *}
          
abbreviation "SCONS0 \<equiv> gg0  :: 'a \<Sigma>\<Sigma>0 F \<Rightarrow> 'a \<Sigma>\<Sigma>0"
abbreviation "LEAF0 \<equiv> leaf0"
abbreviation GUARD0 :: "'a F \<Rightarrow> 'a F \<Sigma>\<Sigma>0" where "GUARD0 \<equiv> LEAF0"
(* local ("inside") end and continuation: within the upto-corecursive definition of a function f,
END immediately an element of J, while CONT calls f corecursively  *)
abbreviation END0 :: "J \<Rightarrow> (J + 'a) \<Sigma>\<Sigma>0" where "END0 xs \<equiv> LEAF0 (Inl xs)"
abbreviation CONT0 :: "'a \<Rightarrow> (J + 'a) \<Sigma>\<Sigma>0" where "CONT0 a \<equiv> LEAF0 (Inr a)"

abbreviation "SCONS1 \<equiv> gg1  :: 'a \<Sigma>\<Sigma>1 F \<Rightarrow> 'a \<Sigma>\<Sigma>1"
abbreviation "LEAF1 \<equiv> leaf1"
abbreviation GUARD1 :: "'a F \<Rightarrow> 'a F \<Sigma>\<Sigma>1" where "GUARD1 \<equiv> LEAF1"
(* local ("inside") end and continuation: within the upto-corecursive definition of a function f,
END immediately an element of J, while CONT calls f corecursively  *)
abbreviation END1 :: "J \<Rightarrow> (J + 'a) \<Sigma>\<Sigma>1" where "END1 xs \<equiv> LEAF1 (Inl xs)"
abbreviation CONT1 :: "'a \<Rightarrow> (J + 'a) \<Sigma>\<Sigma>1" where "CONT1 a \<equiv> LEAF1 (Inr a)"

abbreviation "SCONS2 \<equiv> gg2  :: 'a \<Sigma>\<Sigma>2 F \<Rightarrow> 'a \<Sigma>\<Sigma>2"
abbreviation "LEAF2 \<equiv> leaf2"
abbreviation GUARD2 :: "'a F \<Rightarrow> 'a F \<Sigma>\<Sigma>2" where "GUARD2 \<equiv> LEAF2"
(* local ("inside") end and continuation: within the upto-corecursive definition of a function f,
END immediately an element of J, while CONT calls f corecursively  *)
abbreviation END2 :: "J \<Rightarrow> (J + 'a) \<Sigma>\<Sigma>2" where "END2 xs \<equiv> LEAF2 (Inl xs)"
abbreviation CONT2 :: "'a \<Rightarrow> (J + 'a) \<Sigma>\<Sigma>2" where "CONT2 a \<equiv> LEAF2 (Inr a)"

lemma Node_uniform: "Node x l r = eval0 (gg0 (x, leaf0 l, leaf0 r))"
  by (rule iffD1[OF J.dtor_inject])
    (simp add: map_pre_J_def BNF_Comp.id_bnf_comp_def J.dtor_ctor o_eq_dest[OF eval0_gg0] eval0_leaf0')

lemma genCngdd0_Node: "\<lbrakk>x1 = x2; genCngdd0 R l1 l2; genCngdd0 R r1 r2\<rbrakk> \<Longrightarrow> 
  genCngdd0 R (Node x1 l1 r1) (Node x2 l2 r2)"
  unfolding Node_uniform
  apply (rule genCngdd0_eval0)
  apply (rule rel_funD[OF gg0_transfer])
  unfolding rel_pre_J_def BNF_Comp.id_bnf_comp_def vimage2p_def
  apply (rule rel_funD[OF rel_funD[OF Pair_transfer], rotated])
  apply (rule rel_funD[OF rel_funD[OF Pair_transfer], rotated])
  apply (erule rel_funD[OF leaf0_transfer])
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

lemma genCngdd1_Node: "\<lbrakk>x1 = x2; genCngdd1 R l1 l2; genCngdd1 R r1 r2\<rbrakk> \<Longrightarrow> 
  genCngdd1 R (Node x1 l1 r1) (Node x2 l2 r2)"
  apply (subst I1.idem_Cl[symmetric])
  apply (rule genCngdd0_genCngdd1)
  apply (rule genCngdd0_Node)
  apply auto
  done

lemma genCngdd1_alg\<rho>1: "\<lbrakk>genCngdd1 R t1 t2; genCngdd1 R u1 u2\<rbrakk> \<Longrightarrow> 
  genCngdd1 R (alg\<rho>1 (t1, u1)) (alg\<rho>1 (t2, u2))"
  unfolding alg\<rho>1_def o_apply
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

lemma genCngdd2_Node: "\<lbrakk>x1 = x2; genCngdd2 R l1 l2; genCngdd2 R r1 r2\<rbrakk> \<Longrightarrow> 
  genCngdd2 R (Node x1 l1 r1) (Node x2 l2 r2)"
  apply (subst I2.idem_Cl[symmetric])
  apply (rule genCngdd1_genCngdd2)
  apply (rule genCngdd1_Node)
  apply auto
  done

lemma genCngdd2_alg\<rho>1: "\<lbrakk>genCngdd2 R t1 t2; genCngdd2 R u1 u2\<rbrakk> \<Longrightarrow> 
  genCngdd2 R (alg\<rho>1 (t1, u1)) (alg\<rho>1 (t2, u2))"
  apply (subst I2.idem_Cl[symmetric])
  apply (rule genCngdd1_genCngdd2)
  apply (rule genCngdd1_alg\<rho>1)
  apply auto
  done

lemma genCngdd2_alg\<rho>2: "\<lbrakk>genCngdd2 R t1 t2; genCngdd2 R u1 u2\<rbrakk> \<Longrightarrow> 
  genCngdd2 R (alg\<rho>2 (t1, u1)) (alg\<rho>2 (t2, u2))"
  unfolding alg\<rho>2_def o_apply
  apply (rule genCngdd2_eval2)
  apply (rule rel_funD[OF K2_as_\<Sigma>\<Sigma>2_transfer])
  apply simp
  done

lemma btree_coinduct[case_names Eq_btree, case_conclusion Eq_btree head tail]:
  assumes "R s s'" "\<And>s s'. R s s' \<Longrightarrow> val s = val s' \<and> R (left s) (left s') \<and> R (right s) (right s')"
  shows "s = s'"
using assms(1) proof (rule mp[OF J.dtor_coinduct, rotated], safe)
  fix a b
  assume "R a b"
  from assms(2)[OF this] show "F_rel R (dtor_J a) (dtor_J b)"
    by (cases "dtor_J a" "dtor_J b" rule: prod.exhaust[case_product prod.exhaust])
      (auto simp: rel_pre_J_def vimage2p_def BNF_Comp.id_bnf_comp_def)
qed

lemma btree_coinduct0[case_names Eq_btree, case_conclusion Eq_btree head tail]:
  assumes "R s s'" "\<And>s s'. R s s' \<Longrightarrow> val s = val s' \<and> genCngdd0 R (left s) (left s') \<and> genCngdd0 R (right s) (right s')"
  shows "s = s'"
using assms(1) proof (rule mp[OF coinductionU_genCngdd0, rotated], safe)
  fix a b
  assume "R a b"
  from assms(2)[OF this] show "F_rel (genCngdd0 R) (dtor_J a) (dtor_J b)"
    by (cases "dtor_J a" "dtor_J b" rule: prod.exhaust[case_product prod.exhaust])
      (auto simp: rel_pre_J_def vimage2p_def BNF_Comp.id_bnf_comp_def)
qed

lemma btree_coinduct1[case_names Eq_btree, case_conclusion Eq_btree head tail]:
  assumes "R s s'" "\<And>s s'. R s s' \<Longrightarrow> val s = val s' \<and> genCngdd1 R (left s) (left s') \<and> genCngdd1 R (right s) (right s')"
  shows "s = s'"
using assms(1) proof (rule mp[OF coinductionU_genCngdd1, rotated], safe)
  fix a b
  assume "R a b"
  from assms(2)[OF this] show "F_rel (genCngdd1 R) (dtor_J a) (dtor_J b)"
    by (cases "dtor_J a" "dtor_J b" rule: prod.exhaust[case_product prod.exhaust])
      (auto simp: rel_pre_J_def vimage2p_def BNF_Comp.id_bnf_comp_def)
qed

lemma btree_coinduct2[case_names Eq_btree, case_conclusion Eq_btree head tail]:
  assumes "R s s'" "\<And>s s'. R s s' \<Longrightarrow> val s = val s' \<and> genCngdd2 R (left s) (left s') \<and> genCngdd2 R (right s) (right s')"
  shows "s = s'"
using assms(1) proof (rule mp[OF coinductionU_genCngdd2, rotated], safe)
  fix a b
  assume "R a b"
  from assms(2)[OF this] show "F_rel (genCngdd2 R) (dtor_J a) (dtor_J b)"
    by (cases "dtor_J a" "dtor_J b" rule: prod.exhaust[case_product prod.exhaust])
      (auto simp: rel_pre_J_def vimage2p_def BNF_Comp.id_bnf_comp_def)
qed

end
