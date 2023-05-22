header {* Binary Tree Examples *}

(*<*)
theory Binary_Tree_UFP_Examples
imports Binary_Tree_Lib
begin
(*>*)

subsection {* one *}

definition one :: "btree" where
  "one = dtor_corec_J (\<lambda>_. (1, Inr (), Inr ())) ()"

lemma val_one[simp]: "val one = 1"
  unfolding one_def J.dtor_corec
  by (simp add: map_pre_J_def BNF_Comp.id_bnf_comp_def)

lemma left_one[simp]: "left one = one"
  unfolding one_def J.dtor_corec
  by (simp add: map_pre_J_def BNF_Comp.id_bnf_comp_def)

lemma right_one[simp]: "right one = one"
  unfolding one_def J.dtor_corec
  by (simp add: map_pre_J_def BNF_Comp.id_bnf_comp_def)

lemma one_code[code]:
  "one = Node 1 one one"
  by (metis J.ctor_dtor prod.collapse val_one left_one right_one)


subsection {* plus *}

definition plus :: "btree \<Rightarrow> btree \<Rightarrow> btree" where
  "plus t u = dtor_corec_J
     (\<lambda>(t, u). (val t + val u, Inr (left t, left u), Inr (right t, right u))) (t, u)"

lemma val_plus[simp]: "val (plus t u) = val t + val u"
  unfolding plus_def J.dtor_corec
  by (simp add: map_pre_J_def BNF_Comp.id_bnf_comp_def)

lemma left_plus[simp]: "left (plus t u) = plus (left t) (left u)"
  unfolding plus_def J.dtor_corec
  by (simp add: map_pre_J_def BNF_Comp.id_bnf_comp_def)

lemma right_plus[simp]: "right (plus t u) = plus (right t) (right u)"
  unfolding plus_def J.dtor_corec
  by (simp add: map_pre_J_def BNF_Comp.id_bnf_comp_def)

lemma plus_code[code]:
  "plus (Node x1 l1 r1) (Node x2 l2 r2) = Node (x1 + x2) (plus l1 l2) (plus r1 r2)"
  by (smt2 J.ctor_dtor J.dtor_ctor fst_conv snd_conv prod.collapse val_plus left_plus right_plus)

lemma plus_uniform: "plus s t = alg\<rho>1 (s, t)"
  unfolding plus_def
  apply (rule fun_cong[OF sym[OF J.dtor_corec_unique]])
  unfolding alg\<rho>1 o_def[symmetric] o_assoc
  apply (simp add: map_pre_J_def BNF_Comp.id_bnf_comp_def fun_eq_iff J.dtor_ctor
    \<rho>1_def Let_def convol_def eval1_\<oo>\<pp>1 eval1_leaf1'
    o_eq_dest[OF Abs_\<Sigma>1_natural] alg\<Lambda>1_Inr alg\<rho>1_def)
  done


subsection {* divide *}

definition divide :: "btree \<Rightarrow> btree \<Rightarrow> btree" where
  "divide t u = dtor_corec_J
     (\<lambda>(t, u). (val t / val u, Inr (left t, left u), Inr (right t, right u))) (t, u)"

lemma val_divide[simp]: "val (divide t u) = val t / val u"
  unfolding divide_def J.dtor_corec
  by (simp add: map_pre_J_def BNF_Comp.id_bnf_comp_def)

lemma left_divide[simp]: "left (divide t u) = divide (left t) (left u)"
  unfolding divide_def J.dtor_corec
  by (simp add: map_pre_J_def BNF_Comp.id_bnf_comp_def)

lemma right_divide[simp]: "right (divide t u) = divide (right t) (right u)"
  unfolding divide_def J.dtor_corec
  by (simp add: map_pre_J_def BNF_Comp.id_bnf_comp_def)

lemma divide_code[code]:
  "divide (Node x1 l1 r1) (Node x2 l2 r2) = Node (x1 / x2) (divide l1 l2) (divide r1 r2)"
  by (smt2 J.ctor_dtor J.dtor_ctor fst_conv snd_conv prod.collapse val_divide left_divide right_divide)

lemma divide_uniform: "divide s t = alg\<rho>2 (s, t)"
  unfolding divide_def
  apply (rule fun_cong[OF sym[OF J.dtor_corec_unique]])
  unfolding alg\<rho>2 o_def[symmetric] o_assoc
  apply (simp add: map_pre_J_def BNF_Comp.id_bnf_comp_def fun_eq_iff J.dtor_ctor
    \<rho>2_def Let_def convol_def eval2_\<oo>\<pp>2 eval2_leaf2'
    o_eq_dest[OF Abs_\<Sigma>2_natural] alg\<Lambda>2_Inr alg\<rho>2_def)
  done


subsection {* bird *}

definition bird where
  "bird = corecUU2 (\<lambda>_. GUARD2 (1,
     DIV2 (END2 one, PLS2 (CONT2 (), END2 one)),
     PLS2 (DIV2 (END2 one, CONT2 ()), END2 one))) ()"

lemma val_bird[simp]: "val bird = 1"
  unfolding bird_def corecUU2
  by (simp add: map_pre_J_def BNF_Comp.id_bnf_comp_def J.dtor_ctor eval2_leaf2')

lemma left_bird[simp]: "left bird = divide one (plus bird one)"
  apply (subst bird_def) unfolding corecUU2
  by (simp add: map_pre_J_def BNF_Comp.id_bnf_comp_def J.dtor_ctor eval2_leaf2' eval2_\<oo>\<pp>2
    alg\<Lambda>2_Inl alg\<Lambda>2_Inr alg\<Lambda>1_Inr o_eq_dest[OF Abs_\<Sigma>2_natural] o_eq_dest[OF Abs_\<Sigma>1_natural]
    plus_uniform divide_uniform bird_def)

lemma right_bird[simp]: "right bird = plus (divide one bird) one"
  apply (subst bird_def) unfolding corecUU2
  by (simp add: map_pre_J_def BNF_Comp.id_bnf_comp_def J.dtor_ctor eval2_leaf2' eval2_\<oo>\<pp>2
    alg\<Lambda>2_Inl alg\<Lambda>2_Inr alg\<Lambda>1_Inr o_eq_dest[OF Abs_\<Sigma>2_natural] o_eq_dest[OF Abs_\<Sigma>1_natural]
    plus_uniform divide_uniform bird_def)

lemma bird_code[code]: "bird = Node 1 (divide one (plus bird one)) (plus (divide one bird) one)"
  by (metis J.ctor_dtor prod.collapse val_bird left_bird right_bird)

subsection {* mirror *}

definition mirror :: "btree \<Rightarrow> btree" where
  "mirror t = dtor_corec_J (\<lambda>t. (val t, Inr (right t), Inr (left t))) t"

lemma val_mirror[simp]: "val (mirror t) = val t"
  unfolding mirror_def J.dtor_corec
  by (simp add: map_pre_J_def BNF_Comp.id_bnf_comp_def)

lemma left_mirror[simp]: "left (mirror t) = mirror (right t)"
  unfolding mirror_def J.dtor_corec
  by (simp add: map_pre_J_def BNF_Comp.id_bnf_comp_def)

lemma right_mirror[simp]: "right (mirror t) = mirror (left t)"
  unfolding mirror_def J.dtor_corec
  by (simp add: map_pre_J_def BNF_Comp.id_bnf_comp_def)

lemma mirror_code[code]:
  "mirror (Node x l r) = Node x (mirror r) (mirror l)"
  by (metis J.ctor_dtor J.dtor_ctor fst_conv snd_conv prod.collapse val_mirror left_mirror right_mirror)

subsection {* Some Proofs *}

theorem mirror_one[simp]: "mirror one = one"
  by (coinduction rule: btree_coinduct) auto

theorem mirror_plus[simp]: "mirror (plus r s) = plus (mirror r) (mirror s)"
  by (coinduction arbitrary: r s rule: btree_coinduct) auto

theorem mirror_divide[simp]: "mirror (divide r s) = divide (mirror r) (mirror s)"
  by (coinduction arbitrary: r s rule: btree_coinduct) auto

theorem divide_divide_one[simp]: "divide one (divide one r) = r"
  by (coinduction arbitrary: r rule: btree_coinduct) auto

theorem mirror_bird: "mirror bird = divide one bird"
  by (coinduction rule: btree_coinduct2)
    (auto intro!: genCngdd2_alg\<rho>1[folded plus_uniform] intro: genCngdd2_alg\<rho>2[folded divide_uniform]
      genCngdd2_trans[OF genCngdd2_alg\<rho>2[folded divide_uniform], of _ _ _ _ "divide one bird"])

(*<*)
end
(*>*)
