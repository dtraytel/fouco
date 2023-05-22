theory Stream_Lib
imports "../Stream/Stream_Behavior_BNF" "../Stream/Stream_More_Corec_Upto9"
begin

(* todo: make them defs eventually: *)
type_synonym stream = J
abbreviation "head xs \<equiv> fst (dtor_J xs)"
abbreviation "tail xs \<equiv> snd (dtor_J xs)"
abbreviation "SCons n xs \<equiv> ctor_J (n, xs)"
code_datatype ctor_J
declare J.dtor_ctor[code]

definition smap where
  "smap f = corec_J (\<lambda>xs. (f (head xs), Inr (tail xs)))"

lemma head_smap[simp]: "head (smap f xs) = f (head xs)"
  unfolding smap_def corec_J_def J.dtor_corec BNF_Comp.id_bnf_comp_def map_pre_J_def by simp

lemma tail_smap[simp]: "tail (smap f xs) = smap f (tail xs)"
  unfolding smap_def corec_J_def J.dtor_corec BNF_Comp.id_bnf_comp_def map_pre_J_def by simp

lemma smap_code[code]: "smap f xs = SCons (f (head xs)) (smap f (tail xs))"
  by (metis J.ctor_dtor prod.collapse head_smap tail_smap)

definition same where
  "same x = corec_J (\<lambda>x. (x, Inr x)) x"

lemma head_same[simp]: "head (same x) = x"
  unfolding same_def corec_J_def J.dtor_corec BNF_Comp.id_bnf_comp_def map_pre_J_def by simp

lemma tail_same[simp]: "tail (same x) = same x"
  unfolding same_def corec_J_def J.dtor_corec BNF_Comp.id_bnf_comp_def map_pre_J_def by simp

definition "sconst x = ctor_J (x, same 0)"

lemma head_sconst[simp]: "head (sconst x) = x"
  unfolding sconst_def by (simp add: J.dtor_ctor)

lemma tail_sconst[simp]: "tail (sconst x) = same 0"
  unfolding sconst_def by (simp add: J.dtor_ctor)

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

abbreviation "SCONS3 \<equiv> gg3  :: 'a \<Sigma>\<Sigma>3 F \<Rightarrow> 'a \<Sigma>\<Sigma>3"
abbreviation "LEAF3 \<equiv> leaf3"
abbreviation GUARD3 :: "'a F \<Rightarrow> 'a F \<Sigma>\<Sigma>3" where "GUARD3 \<equiv> LEAF3"
(* local ("inside") end and continuation: within the upto-corecursive definition of a function f,
END immediately an element of J, while CONT calls f corecursively  *)
abbreviation END3 :: "J \<Rightarrow> (J + 'a) \<Sigma>\<Sigma>3" where "END3 xs \<equiv> LEAF3 (Inl xs)"
abbreviation CONT3 :: "'a \<Rightarrow> (J + 'a) \<Sigma>\<Sigma>3" where "CONT3 a \<equiv> LEAF3 (Inr a)"

abbreviation "SCONS4 \<equiv> gg4  :: 'a \<Sigma>\<Sigma>4 F \<Rightarrow> 'a \<Sigma>\<Sigma>4"
abbreviation "LEAF4 \<equiv> leaf4"
abbreviation GUARD4 :: "'a F \<Rightarrow> 'a F \<Sigma>\<Sigma>4" where "GUARD4 \<equiv> LEAF4"
(* local ("inside") end and continuation: within the upto-corecursive definition of a function f,
END immediately an element of J, while CONT calls f corecursively  *)
abbreviation END4 :: "J \<Rightarrow> (J + 'a) \<Sigma>\<Sigma>4" where "END4 xs \<equiv> LEAF4 (Inl xs)"
abbreviation CONT4 :: "'a \<Rightarrow> (J + 'a) \<Sigma>\<Sigma>4" where "CONT4 a \<equiv> LEAF4 (Inr a)"

abbreviation "SCONS5 \<equiv> gg5  :: 'a \<Sigma>\<Sigma>5 F \<Rightarrow> 'a \<Sigma>\<Sigma>5"
abbreviation "LEAF5 \<equiv> leaf5"
abbreviation GUARD5 :: "'a F \<Rightarrow> 'a F \<Sigma>\<Sigma>5" where "GUARD5 \<equiv> LEAF5"
(* local ("inside") end and continuation: within the upto-corecursive definition of a function f,
END immediately an element of J, while CONT calls f corecursively  *)
abbreviation END5 :: "J \<Rightarrow> (J + 'a) \<Sigma>\<Sigma>5" where "END5 xs \<equiv> LEAF5 (Inl xs)"
abbreviation CONT5 :: "'a \<Rightarrow> (J + 'a) \<Sigma>\<Sigma>5" where "CONT5 a \<equiv> LEAF5 (Inr a)"

abbreviation "SCONS6 \<equiv> gg6  :: 'a \<Sigma>\<Sigma>6 F \<Rightarrow> 'a \<Sigma>\<Sigma>6"
abbreviation "LEAF6 \<equiv> leaf6"
abbreviation GUARD6 :: "'a F \<Rightarrow> 'a F \<Sigma>\<Sigma>6" where "GUARD6 \<equiv> LEAF6"
(* local ("inside") end and continuation: within the upto-corecursive definition of a function f,
END immediately an element of J, while CONT calls f corecursively  *)
abbreviation END6 :: "J \<Rightarrow> (J + 'a) \<Sigma>\<Sigma>6" where "END6 xs \<equiv> LEAF6 (Inl xs)"
abbreviation CONT6 :: "'a \<Rightarrow> (J + 'a) \<Sigma>\<Sigma>6" where "CONT6 a \<equiv> LEAF6 (Inr a)"

abbreviation "SCONS7 \<equiv> gg7  :: 'a \<Sigma>\<Sigma>7 F \<Rightarrow> 'a \<Sigma>\<Sigma>7"
abbreviation "LEAF7 \<equiv> leaf7"
abbreviation GUARD7 :: "'a F \<Rightarrow> 'a F \<Sigma>\<Sigma>7" where "GUARD7 \<equiv> LEAF7"
(* local ("inside") end and continuation: within the upto-corecursive definition of a function f,
END immediately an element of J, while CONT calls f corecursively  *)
abbreviation END7 :: "J \<Rightarrow> (J + 'a) \<Sigma>\<Sigma>7" where "END7 xs \<equiv> LEAF7 (Inl xs)"
abbreviation CONT7 :: "'a \<Rightarrow> (J + 'a) \<Sigma>\<Sigma>7" where "CONT7 a \<equiv> LEAF7 (Inr a)"

abbreviation "SCONS8 \<equiv> gg8  :: 'a \<Sigma>\<Sigma>8 F \<Rightarrow> 'a \<Sigma>\<Sigma>8"
abbreviation "LEAF8 \<equiv> leaf8"
abbreviation GUARD8 :: "'a F \<Rightarrow> 'a F \<Sigma>\<Sigma>8" where "GUARD8 \<equiv> LEAF8"
(* local ("inside") end and continuation: within the upto-corecursive definition of a function f,
END immediately an element of J, while CONT calls f corecursively  *)
abbreviation END8 :: "J \<Rightarrow> (J + 'a) \<Sigma>\<Sigma>8" where "END8 xs \<equiv> LEAF8 (Inl xs)"
abbreviation CONT8 :: "'a \<Rightarrow> (J + 'a) \<Sigma>\<Sigma>8" where "CONT8 a \<equiv> LEAF8 (Inr a)"

abbreviation "SCONS9 \<equiv> gg9  :: 'a \<Sigma>\<Sigma>9 F \<Rightarrow> 'a \<Sigma>\<Sigma>9"
abbreviation "LEAF9 \<equiv> leaf9"
abbreviation GUARD9 :: "'a F \<Rightarrow> 'a F \<Sigma>\<Sigma>9" where "GUARD9 \<equiv> LEAF9"
(* local ("inside") end and continuation: within the upto-corecursive definition of a function f,
END immediately an element of J, while CONT calls f corecursively  *)
abbreviation END9 :: "J \<Rightarrow> (J + 'a) \<Sigma>\<Sigma>9" where "END9 xs \<equiv> LEAF9 (Inl xs)"
abbreviation CONT9 :: "'a \<Rightarrow> (J + 'a) \<Sigma>\<Sigma>9" where "CONT9 a \<equiv> LEAF9 (Inr a)"

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

lemma genCngdd1_alg\<rho>1: "\<lbrakk>genCngdd1 R xs1 xs2; genCngdd1 R ys1 ys2\<rbrakk> \<Longrightarrow> 
  genCngdd1 R (alg\<rho>1 (xs1, ys1)) (alg\<rho>1 (xs2, ys2))"
  unfolding alg\<rho>1_def o_apply
  apply (rule genCngdd1_eval1)
  apply (rule rel_funD[OF K1_as_\<Sigma>\<Sigma>1_transfer])
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

end