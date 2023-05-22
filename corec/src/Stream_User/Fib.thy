header {* Two Examples of Fibonacci streams *}

(*<*)
theory Fib
imports Stream_Examples
begin
(*>*)

definition fibA :: stream where
  "fibA = corecUU1 (\<lambda>xs. GUARD1 (0, PLS1 (SCONS1 (1, CONT1 xs), CONT1 xs))) ()"

lemma head_fibA[simp]: "head fibA = 0"
  unfolding fibA_def corecUU1
  by (simp add: map_pre_J_def BNF_Comp.id_bnf_comp_def J.dtor_ctor eval1_leaf1')

lemma tail_fibA[simp]: "tail fibA = pls (SCons 1 fibA) fibA"
  apply (subst fibA_def)
  unfolding corecUU1
  by (simp add: map_pre_J_def BNF_Comp.id_bnf_comp_def J.dtor_ctor eval1_leaf1'
    eval1_\<oo>\<pp>1 alg\<Lambda>1_Inr o_eq_dest[OF Abs_\<Sigma>1_natural] o_eq_dest[OF gg1_natural]
    o_eq_dest[OF eval1_gg1] pls_uniform fibA_def)

lemma fibA_code[code]: "fibA = SCons 0 (pls (SCons 1 fibA) fibA)"
  by (metis J.ctor_dtor prod.collapse head_fibA tail_fibA)


definition fibB :: stream where
  "fibB = corecUU1 (\<lambda>xs. PLS1 (GUARD1 (0, (SCONS1 (1, CONT1 xs))), GUARD1 (0, CONT1 xs))) ()"

lemma fibB_code[code]: "fibB = pls (SCons 0 (SCons 1 fibB)) (SCons 0 fibB)"
  apply (subst fibB_def)
  unfolding corecUU1
  by (simp add: map_pre_J_def BNF_Comp.id_bnf_comp_def J.dtor_ctor eval1_leaf1'
    eval1_\<oo>\<pp>1 alg\<Lambda>1_Inr o_eq_dest[OF Abs_\<Sigma>1_natural] o_eq_dest[OF gg1_natural]
    o_eq_dest[OF eval1_gg1] pls_uniform fibB_def)

lemma "fibA = fibB"
proof (coinduction rule: stream_coinduct1)
  case Eq_stream
  have ?head by (subst fibB_code) (simp add: J.dtor_ctor)
  moreover
  have ?tail by (subst (2) fibB_code) (auto simp add: J.dtor_ctor intro: genCngdd1_pls genCngdd1_SCons)
  ultimately show ?case ..
qed

(*<*)
end
(*>*)
