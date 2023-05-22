header {* Mixed Recursion-Corecursion *}

(*<*)
theory Mixed
imports Stream_Examples GCD
begin
(*>*)

function primes\<^sub>r\<^sub>e\<^sub>c :: "(nat * nat) \<Rightarrow> (stream + nat * nat) \<Sigma>\<Sigma>0 F \<Sigma>\<Sigma>0" where
  "primes\<^sub>r\<^sub>e\<^sub>c (m, n) =
     (if (m = 0 \<and> n > 1) \<or> coprime m n then GUARD0 (n, CONT0 (m * n, Suc n))
     else (primes\<^sub>r\<^sub>e\<^sub>c (m, Suc n)))"
by pat_completeness auto
termination
  apply (relation "measure (\<lambda>(m, n).
    if n = 0 then 1 else if coprime m n then 0 else m - n mod m)")
  apply (auto simp: mod_Suc intro: Suc_lessI)
      apply (metis One_nat_def coprime_Suc_nat gcd_nat.commute gcd_red_nat)
     apply (metis diff_less_mono2 lessI mod_less_divisor)
  done

definition primes :: "nat \<Rightarrow> nat \<Rightarrow> stream" where
  "primes = curry (corecUU0 primes\<^sub>r\<^sub>e\<^sub>c)"

lemma primes_code:
  "primes m n =
    (if (m = 0 \<and> n > 1) \<or> coprime m n then SCons n (primes (m * n) (Suc n))
     else primes m (Suc n))"
  unfolding primes_def curry_def
  by (subst corecUU0, subst primes\<^sub>r\<^sub>e\<^sub>c.simps)
    (simp del: primes\<^sub>r\<^sub>e\<^sub>c.simps add: map_pre_J_def BNF_Comp.id_bnf_comp_def eval0_leaf0' corecUU0)

lemma primes: "primes 1 2 = SCons 2 (primes 2 3)"
  by (subst primes_code) auto

fun catalan\<^sub>r\<^sub>e\<^sub>c :: "nat \<Rightarrow> (stream + nat) \<Sigma>\<Sigma>1 F \<Sigma>\<Sigma>1" where
  "catalan\<^sub>r\<^sub>e\<^sub>c n =
     (if n > 0 then PLS1 (catalan\<^sub>r\<^sub>e\<^sub>c (n - 1), GUARD1 (0, CONT1 (n+1))) else GUARD1 (1, CONT1 1))"

definition catalan :: "nat \<Rightarrow> stream" where
  "catalan = corecUU1 catalan\<^sub>r\<^sub>e\<^sub>c"

lemma catalan_code:
  "catalan n =
    (if n > 0 then pls (catalan (n - 1)) (SCons 0 (catalan (n + 1)))
     else SCons 1 (catalan 1))"
  unfolding catalan_def
  by (subst corecUU1, subst catalan\<^sub>r\<^sub>e\<^sub>c.simps)
    (simp del: catalan\<^sub>r\<^sub>e\<^sub>c.simps add: map_pre_J_def BNF_Comp.id_bnf_comp_def
      eval1_\<oo>\<pp>1 eval1_leaf1' alg\<Lambda>1_Inr o_eq_dest[OF Abs_\<Sigma>1_natural] corecUU1 pls_uniform)

(*<*)
end
(*>*)
