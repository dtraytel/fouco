theory LList_Lib
imports "../LList/LList_Behavior_BNF" "../LList/LList_More_Corec_Upto0"
begin

(* todo: make them defs eventually: *)
type_synonym llist = J
abbreviation "LNil \<equiv> ctor_J (Inl ())"
abbreviation "LCons n xs \<equiv> ctor_J (Inr (n, xs))"
abbreviation "head xs \<equiv> (case dtor_J xs of Inr (x, xs) \<Rightarrow> x)"
abbreviation "tail xs \<equiv> (case dtor_J xs of Inr (x, xs) \<Rightarrow> xs | _ \<Rightarrow> LNil)"
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

lemma LNil_uniform: "LNil = eval0 (gg0 (Inl ()))"
  by (rule iffD1[OF J.dtor_inject])
    (simp add: map_pre_J_def BNF_Comp.id_bnf_comp_def o_eq_dest[OF eval0_gg0])

lemma LCons_uniform: "LCons x s = eval0 (gg0 (Inr (x, leaf0 s)))"
  by (rule iffD1[OF J.dtor_inject])
    (simp add: map_pre_J_def BNF_Comp.id_bnf_comp_def J.dtor_ctor o_eq_dest[OF eval0_gg0] eval0_leaf0')

lemma genCngdd0_LNil: "genCngdd0 R LNil LNil"
  unfolding LNil_uniform
  apply (rule genCngdd0_eval0)
  apply (rule rel_funD[OF gg0_transfer])
  unfolding rel_pre_J_def BNF_Comp.id_bnf_comp_def vimage2p_def rel_sum_simps
  apply (rule refl)
  done

lemma genCngdd0_LCons: "\<lbrakk>x1 = x2; genCngdd0 R xs1 xs2\<rbrakk> \<Longrightarrow> 
  genCngdd0 R (LCons x1 xs1) (LCons x2 xs2)"
  unfolding LCons_uniform
  apply (rule genCngdd0_eval0)
  apply (rule rel_funD[OF gg0_transfer])
  unfolding rel_pre_J_def BNF_Comp.id_bnf_comp_def vimage2p_def rel_sum_simps
  apply (rule rel_funD[OF rel_funD[OF Pair_transfer], rotated])
  apply (erule rel_funD[OF leaf0_transfer])
  apply assumption
  done

lemma llist_coinduct[case_names Eq_llist, case_conclusion Eq_llist head tail]:
  assumes "R s s'" "\<And>s s'. R s s' \<Longrightarrow> (s = LNil \<longleftrightarrow> s' = LNil) \<and>
    (s \<noteq> LNil \<longrightarrow> s' \<noteq> LNil \<longrightarrow> head s = head s' \<and> R (tail s) (tail s'))"
  shows "s = s'"
using assms(1) proof (rule mp[OF J.dtor_coinduct, rotated], safe)
  fix a b
  assume "R a b"
  from assms(2)[OF this] show "F_rel R (dtor_J a) (dtor_J b)"
    by (cases "dtor_J a" "dtor_J b" rule: sum.exhaust[case_product sum.exhaust])
      (auto simp: rel_pre_J_def vimage2p_def BNF_Comp.id_bnf_comp_def J.dtor_ctor, (metis J.ctor_dtor)+)
qed

lemma llist_coinduct0[case_names Eq_llist, case_conclusion Eq_llist head tail]:
  assumes "R s s'" "\<And>s s'. R s s' \<Longrightarrow> (s = LNil \<longleftrightarrow> s' = LNil) \<and>
    (s \<noteq> LNil \<longrightarrow> s' \<noteq> LNil \<longrightarrow> head s = head s' \<and> genCngdd0 R (tail s) (tail s'))"
  shows "s = s'"
using assms(1) proof (rule mp[OF coinductionU_genCngdd0, rotated], safe)
  fix a b
  assume "R a b"
  from assms(2)[OF this] show "F_rel (genCngdd0 R) (dtor_J a) (dtor_J b)"
    by (cases "dtor_J a" "dtor_J b" rule: sum.exhaust[case_product sum.exhaust])
      (auto simp: rel_pre_J_def vimage2p_def BNF_Comp.id_bnf_comp_def J.dtor_ctor, (metis J.ctor_dtor)+)
qed

end