header {* Streams of Factorials *}

(*<*)
theory Factorial
imports Stream_Examples Fact
begin
(*>*)

definition "facsA = corecUU2 (\<lambda>xs. PRD2 (GUARD2 (1, CONT2 xs), GUARD2 (1, CONT2 xs))) ()"

lemma facsA_code[code]: "facsA = prd (SCons 1 facsA) (SCons 1 facsA)"
  apply (subst facsA_def)
  unfolding corecUU2
  by (simp add: map_pre_J_def BNF_Comp.id_bnf_comp_def J.dtor_ctor eval2_leaf2'
    eval2_\<oo>\<pp>2 alg\<Lambda>2_Inr o_eq_dest[OF Abs_\<Sigma>2_natural] o_eq_dest[OF gg2_natural]
    o_eq_dest[OF eval2_gg2] prd_uniform facsA_def)

definition "facsB = corecUU3 (\<lambda>xs. EXP3 (K3.I (GUARD3 (0, CONT3 xs)))) ()"

lemma facsB_code[code]: "facsB = Exp (SCons 0 facsB)"
  apply (subst facsB_def)
  unfolding corecUU3
  by (simp add: map_pre_J_def BNF_Comp.id_bnf_comp_def J.dtor_ctor eval3_leaf3'
    eval3_\<oo>\<pp>3 alg\<Lambda>3_Inr o_eq_dest[OF Abs_\<Sigma>3_natural] o_eq_dest[OF gg3_natural]
    o_eq_dest[OF eval3_gg3] Exp_uniform facsB_def)

lemma head_facsB[simp]: "head facsB = 1"
  by (subst facsB_code) (simp add: J.dtor_ctor exp_def)

lemma tail_facsB[simp]: "tail facsB = prd facsB facsB"
  by (subst facsB_code, subst tail_Exp) (simp add: J.dtor_ctor facsB_code[symmetric])

lemma facsA_facsB: "SCons 1 facsA = facsB"
proof (coinduction rule: stream_coinduct3)
  case Eq_stream
  have ?head by (subst facsA_code) (simp add: J.dtor_ctor exp_def)
  moreover
  have ?tail by (subst (2) facsA_code) (auto intro!: genCngdd3_prd simp: J.dtor_ctor)
  ultimately show ?case ..
qed

fun facsC\<^sub>r\<^sub>e\<^sub>c where
  "facsC\<^sub>r\<^sub>e\<^sub>c (n, fn, i) =
     (if i = 0 then GUARD0 (fn, CONT0 (n + 1, 1, n + 1)) else facsC\<^sub>r\<^sub>e\<^sub>c (n, fn * i, i - 1))"

definition "facsC = corecUU0 facsC\<^sub>r\<^sub>e\<^sub>c (1, 1, 1)"

lemma factsD\<^sub>r\<^sub>e\<^sub>c_code:
  "corecUU0 facsC\<^sub>r\<^sub>e\<^sub>c (n, fn, i) =
    (if i = 0 then SCons fn (corecUU0 facsC\<^sub>r\<^sub>e\<^sub>c (n + 1, 1, n + 1))
    else corecUU0 facsC\<^sub>r\<^sub>e\<^sub>c (n, fn * i, i - 1))"
  by (subst corecUU0, subst facsC\<^sub>r\<^sub>e\<^sub>c.simps)
    (simp del: facsC\<^sub>r\<^sub>e\<^sub>c.simps add: map_pre_J_def BNF_Comp.id_bnf_comp_def eval0_leaf0' corecUU0)

definition "fromN = dtor_corec_J (\<lambda>n. (n, Inr (Suc n)))"

lemma head_fromN[simp]: "head (fromN n) = n"
  unfolding fromN_def J.dtor_corec map_pre_J_def BNF_Comp.id_bnf_comp_def by simp

lemma tail_fromN[simp]: "tail (fromN n) = fromN (Suc n)"
  unfolding fromN_def J.dtor_corec map_pre_J_def BNF_Comp.id_bnf_comp_def by simp

abbreviation "facsD n \<equiv> smap fact (fromN n)"

primrec prds where
  "prds 0 s = s"
| "prds (Suc n) s = prd s (prds n s)"

lemma head_prds[simp]: "head (prds n s) = head s ^ (Suc n)"
  by (induct n) auto

lemma tail_prds_fac[simp]: "tail (prds n facsB) = scale (Suc n) (prds (Suc n) facsB)"
  by (induct n) (auto simp: scale_Suc, auto simp: prd_distribL pls_ac_simps prd_ac_simps)

lemma facsD_facsB: "facsD n = scale (fact n) (prds n facsB)"
proof (coinduction arbitrary: n rule: stream_coinduct3)
  case Eq_stream
  have ?head by (subst facsB_code) (simp add: J.dtor_ctor exp_def)
  moreover
  have ?tail by (subst (2) facsB_code) (auto simp add: J.dtor_ctor facsB_code[symmetric]
    scale_mult[symmetric] trans[OF mult.commute fact_Suc[symmetric]]
    simp del: mult_Suc_right mult_Suc fact_Suc prds.simps)
  ultimately show ?case ..
qed

corollary "facsA = facsD 1"
  unfolding facsD_facsB facsA_facsB[symmetric] by (subst facsA_code) (simp add: scale_Suc)

corollary "facsB = facsD 0"
  unfolding facsD_facsB by (simp add: scale_Suc)

primrec ffac where
  "ffac fn 0 = fn"
| "ffac fn (Suc i) = ffac (fn * Suc i) i"

lemma ffac_fact: "ffac m n = m * fact n"
  by (induct n arbitrary: m) (auto simp: algebra_simps)

lemma ffac_fact_Suc: "ffac (Suc n) n = fact (Suc n)"
  unfolding ffac_fact fact_Suc ..

lemma factsD\<^sub>r\<^sub>e\<^sub>c_facsD: "corecUU0 facsC\<^sub>r\<^sub>e\<^sub>c (n, fn, i) = SCons (ffac fn i) (facsD (n + 1))"
proof (coinduction arbitrary: n fn i rule: stream_coinduct)
  case Eq_stream
  have ?head
  proof (induct i arbitrary: fn)
    case 0 then show ?case by (subst factsD\<^sub>r\<^sub>e\<^sub>c_code) (simp add: J.dtor_ctor)
  next
    case (Suc i) then show ?case by (subst factsD\<^sub>r\<^sub>e\<^sub>c_code) simp
  qed
  moreover have ?tail
  proof (induct i arbitrary: fn)
    case 0
    have "facsD (Suc n) = SCons (ffac (Suc n) n) (facsD (Suc (Suc n)))"
      by (coinduction rule: stream_coinduct0) (auto simp: J.dtor_ctor ffac_fact_Suc)
    then show ?case by (subst factsD\<^sub>r\<^sub>e\<^sub>c_code) (force simp: J.dtor_ctor)
  next
    case (Suc i)
    then show ?case by (subst factsD\<^sub>r\<^sub>e\<^sub>c_code) simp
  qed
  ultimately show ?case by blast
qed

lemma facsC_facsD: "facsC = facsD 1"
  unfolding facsC_def factsD\<^sub>r\<^sub>e\<^sub>c_facsD by (subst (2) smap_code) auto

(*<*)
end
(*>*)
