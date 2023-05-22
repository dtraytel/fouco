header {* Stream Examples *}

(*<*)
theory Stream_UFP_Examples
imports Stream_Lib
begin
(*>*)

subsection {* one *}

definition one :: stream where
  "one = dtor_corec_J (\<lambda>_. (1, Inr ())) ()"

lemma head_one[simp]: "head one = 1"
  unfolding one_def J.dtor_corec
  by (simp add: map_pre_J_def BNF_Comp.id_bnf_comp_def)

lemma tail_one[simp]: "tail one = one"
  unfolding one_def J.dtor_corec
  by (simp add: map_pre_J_def BNF_Comp.id_bnf_comp_def)

lemma one_code[code]: "one = SCons 1 one"
  by (metis J.ctor_dtor prod.collapse head_one tail_one)


subsection {* plus *}

definition plus :: "stream \<Rightarrow> stream \<Rightarrow> stream" where
  "plus s t = dtor_corec_J (\<lambda>(s, t). (head s + head t, Inr (tail s, tail t))) (s, t)"

lemma head_plus[simp]: "head (plus s t) = head s + head t"
  unfolding plus_def J.dtor_corec map_pre_J_def BNF_Comp.id_bnf_comp_def by simp

lemma tail_plus[simp]: "tail (plus s t) = plus (tail s) (tail t)"
  unfolding plus_def J.dtor_corec map_pre_J_def BNF_Comp.id_bnf_comp_def by simp

lemma plus_code[code]: "plus (SCons m s) (SCons n t) = SCons (m + n) (plus s t)"
  by (smt2 J.ctor_dtor J.dtor_ctor fst_conv snd_conv prod.collapse head_plus tail_plus)

lemma plus_uniform: "plus xs ys = alg\<rho>1 (xs, ys)"
  unfolding plus_def
  apply (rule fun_cong[OF sym[OF J.dtor_corec_unique]])
  unfolding alg\<rho>1
  by (simp add: map_pre_J_def BNF_Comp.id_bnf_comp_def fun_eq_iff convol_def \<rho>1_def alg\<rho>1_def)


subsection {* nat *}

definition nat :: "stream" where
  "nat = corecUU1 (\<lambda>_. GUARD1 (0, PLS1 (CONT1 (), END1 one))) ()"

lemma head_nat[simp]: "head nat = 0"
  unfolding nat_def corecUU1
  by (simp add: map_pre_J_def BNF_Comp.id_bnf_comp_def J.dtor_ctor eval1_leaf1')

lemma tail_nat[simp]: "tail nat = plus nat one"
  apply (subst nat_def) unfolding corecUU1
  by (simp add: map_pre_J_def BNF_Comp.id_bnf_comp_def J.dtor_ctor eval1_leaf1'
    eval1_\<oo>\<pp>1 alg\<Lambda>1_Inr o_eq_dest[OF Abs_\<Sigma>1_natural] plus_uniform nat_def)

lemma nat_code[code]: "nat = SCons 0 (plus nat one)"
  by (metis J.ctor_dtor prod.collapse head_nat tail_nat)


subsection {* id *}

definition id :: "stream \<Rightarrow> stream" where
  "id s = dtor_corec_J (\<lambda>s. (head s, Inl (tail s))) s"

lemma head_id[simp]: "head (id s) = head s"
  unfolding id_def J.dtor_corec
  by (simp add: map_pre_J_def BNF_Comp.id_bnf_comp_def)

lemma tail_id[simp]: "tail (id s) = tail s"
  unfolding id_def J.dtor_corec
  by (simp add: map_pre_J_def BNF_Comp.id_bnf_comp_def)

lemma id_code[code]: "id (SCons m s) = SCons m s"
  by (metis J.ctor_dtor prod.collapse head_id tail_id)


subsection {* fib *}

definition fib :: stream where
  "fib = corecUU1 (\<lambda>xs. GUARD1 (0, PLS1 (SCONS1 (1, CONT1 xs), CONT1 xs))) ()"

lemma head_fib[simp]: "head fib = 0"
  unfolding fib_def corecUU1
  by (simp add: map_pre_J_def BNF_Comp.id_bnf_comp_def J.dtor_ctor eval1_leaf1')

lemma tail_fib[simp]: "tail fib = plus (SCons 1 fib) fib"
  apply (subst fib_def) unfolding corecUU1
  by (simp add: map_pre_J_def BNF_Comp.id_bnf_comp_def J.dtor_ctor eval1_leaf1'
    eval1_\<oo>\<pp>1 alg\<Lambda>1_Inr o_eq_dest[OF Abs_\<Sigma>1_natural] o_eq_dest[OF gg1_natural]
    o_eq_dest[OF eval1_gg1] plus_uniform fib_def)

lemma fib_code[code]: "fib = SCons 0 (plus (SCons 1 fib) fib)"
  by (metis J.ctor_dtor prod.collapse head_fib tail_fib)


subsection {* sum *}

definition sum :: "stream \<Rightarrow> stream" where
  "sum s = corecUU1 (\<lambda>s. GUARD1 (0, PLS1 (END1 s, CONT1 s))) s"

lemma head_sum[simp]: "head (sum s) = 0"
  unfolding sum_def corecUU1
  by (simp add: map_pre_J_def BNF_Comp.id_bnf_comp_def J.dtor_ctor eval1_leaf1')

lemma tail_sum[simp]: "tail (sum s) = plus s (sum s)"
  apply (subst sum_def) unfolding corecUU1
  by (simp add: map_pre_J_def BNF_Comp.id_bnf_comp_def J.dtor_ctor eval1_leaf1'
    eval1_\<oo>\<pp>1 alg\<Lambda>1_Inr o_eq_dest[OF Abs_\<Sigma>1_natural] o_eq_dest[OF gg1_natural]
    o_eq_dest[OF eval1_gg1] plus_uniform sum_def)

lemma sum_code[code]: "sum s = SCons 0 (plus s (sum s))"
  by (metis J.ctor_dtor prod.collapse head_sum tail_sum)


subsection {* alternate *}

definition alternate :: "stream \<Rightarrow> stream \<Rightarrow> stream" where
  "alternate s t = dtor_corec_J (\<lambda>(s, t). (head s, Inr (tail t, tail s))) (s, t)"

lemma head_alternate[simp]: "head (alternate s t) = head s"
  unfolding alternate_def J.dtor_corec
  by (simp add: map_pre_J_def BNF_Comp.id_bnf_comp_def)

lemma tail_alternate[simp]: "tail (alternate s t) = alternate (tail t) (tail s)"
  apply (subst alternate_def) unfolding J.dtor_corec
  by (simp add: map_pre_J_def BNF_Comp.id_bnf_comp_def alternate_def)

lemma alternate_code[code]: "alternate (SCons m s) (SCons n t) = SCons m (alternate t s)"
  by (metis J.ctor_dtor J.dtor_ctor fst_conv snd_conv prod.collapse head_alternate tail_alternate)


subsection {* interleave *}

definition interleave :: "stream \<Rightarrow> stream \<Rightarrow> stream" where
  "interleave s t = dtor_corec_J (\<lambda>(s, t). (head s, Inr (t, tail s))) (s, t)"

lemma head_interleave[simp]: "head (interleave s t) = head s"
  unfolding interleave_def J.dtor_corec
  by (simp add: map_pre_J_def BNF_Comp.id_bnf_comp_def)

lemma tail_interleave[simp]: "tail (interleave s t) = interleave t (tail s)"
  apply (subst interleave_def) unfolding J.dtor_corec
  by (simp add: map_pre_J_def BNF_Comp.id_bnf_comp_def interleave_def)

lemma interleave_code[code]: "interleave (SCons m s) (SCons n t) = SCons m (interleave (SCons n t) s)"
  by (metis J.ctor_dtor J.dtor_ctor fst_conv snd_conv prod.collapse head_interleave tail_interleave)

lemma interleave_uniform: "interleave s t = alg\<rho>6 (s, t)"
  unfolding interleave_def
  apply (rule fun_cong[OF sym[OF J.dtor_corec_unique]])
  unfolding alg\<rho>6 o_def[symmetric] o_assoc
  apply (simp add: map_pre_J_def BNF_Comp.id_bnf_comp_def fun_eq_iff J.dtor_ctor
    \<rho>6_def Let_def convol_def eval6_\<oo>\<pp>6 eval6_leaf6'
    o_eq_dest[OF Abs_\<Sigma>6_natural] alg\<Lambda>6_Inr alg\<rho>6_def)
  done


subsection {* merge *}

definition merge where
  "merge s t = dtor_corec_J (\<lambda>(s, t).
    if head s \<le> head t then (head s, Inr (tail s, t)) else (head t, Inr (s, tail t))) (s, t)"

lemma head_merge[simp]: "head (merge s t) = (if head s \<le> head t then head s else head t)"
  unfolding merge_def J.dtor_corec
  by (simp add: map_pre_J_def BNF_Comp.id_bnf_comp_def)

lemma tail_merge[simp]: "tail (merge s t) = (if head s \<le> head t then merge (tail s) t else merge s (tail t))"
  apply (subst merge_def) unfolding J.dtor_corec
  by (simp add: map_pre_J_def BNF_Comp.id_bnf_comp_def merge_def)

lemma merge_code[code]:
  "merge (SCons m s) (SCons n t) =
  (if m \<le> n then SCons m (merge s (SCons n t)) else SCons n (merge (SCons m s) t))"
  by (smt2 J.ctor_dtor J.dtor_ctor fst_conv snd_conv prod.collapse head_merge tail_merge)

lemma merge_uniform: "merge s t = alg\<rho>8 (s, t)"
  unfolding merge_def
  apply (rule fun_cong[OF sym[OF J.dtor_corec_unique]])
  unfolding alg\<rho>8 o_def[symmetric] o_assoc
  apply (simp add: map_pre_J_def BNF_Comp.id_bnf_comp_def fun_eq_iff J.dtor_ctor
    \<rho>8_def Let_def convol_def eval8_\<oo>\<pp>8 eval8_leaf8'
    o_eq_dest[OF Abs_\<Sigma>8_natural] alg\<Lambda>8_Inr alg\<rho>8_def)
  done


subsection {* dup *}

definition dup where
  "dup s = dtor_corec_J (\<lambda>s. (head s, Inl s)) s"

lemma head_dup[simp]: "head (dup s) = head s"
  unfolding dup_def J.dtor_corec
  by (simp add: map_pre_J_def BNF_Comp.id_bnf_comp_def)

lemma tail_dup[simp]: "tail (dup s) = s"
  unfolding dup_def J.dtor_corec
  by (simp add: map_pre_J_def BNF_Comp.id_bnf_comp_def)

lemma dup_code[code]: "dup (SCons m s) = SCons m (SCons m s)"
  by (metis J.ctor_dtor J.dtor_ctor fst_conv prod.collapse head_dup tail_dup)


subsection {* inv *}

definition inv :: "stream \<Rightarrow> stream" where
  "inv s = dtor_corec_J (\<lambda>s. (1 - head s, Inr (tail s))) s"

lemma head_inv[simp]: "head (inv s) = 1 - head s"
  unfolding inv_def J.dtor_corec
  by (simp add: map_pre_J_def BNF_Comp.id_bnf_comp_def)

lemma tail_inv[simp]: "tail (inv s) = inv (tail s)"
  apply (subst inv_def) unfolding J.dtor_corec
  by (simp add: map_pre_J_def BNF_Comp.id_bnf_comp_def inv_def)

lemma inv_code[code]: "inv (SCons m s) = SCons (1 - m) (inv s)"
  by (metis J.ctor_dtor J.dtor_ctor fst_conv snd_conv prod.collapse head_inv tail_inv)

lemma inv_uniform: "inv s = alg\<rho>7 (K7.I s)"
  unfolding inv_def
  apply (rule fun_cong[OF sym[OF J.dtor_corec_unique]])
  unfolding alg\<rho>7 o_def[symmetric] o_assoc
  apply (simp add: map_pre_J_def BNF_Comp.id_bnf_comp_def fun_eq_iff J.dtor_ctor
    \<rho>7_def Let_def convol_def eval7_\<oo>\<pp>7 eval7_leaf7'
    o_eq_dest[OF Abs_\<Sigma>7_natural] alg\<Lambda>7_Inr alg\<rho>7_def)
  done


subsection {* thue *}

definition thue' :: stream where
  "thue' = corecUU7 (\<lambda>_. GUARD7 (1, INTERLEAVE7 (CONT7 (), INV7 (I (CONT7 ()))))) ()"

lemma head_thue'[simp]: "head thue' = 1"
  unfolding thue'_def corecUU7
  by (simp add: map_pre_J_def BNF_Comp.id_bnf_comp_def J.dtor_ctor eval7_leaf7')

lemma tail_thue'[simp]: "tail thue' = interleave thue' (inv thue')"
  apply (subst thue'_def) unfolding corecUU7
  by (simp add: map_pre_J_def BNF_Comp.id_bnf_comp_def J.dtor_ctor eval7_leaf7' eval7_\<oo>\<pp>7
    alg\<Lambda>7_Inl alg\<Lambda>7_Inr alg\<Lambda>6_Inr o_eq_dest[OF Abs_\<Sigma>7_natural] o_eq_dest[OF Abs_\<Sigma>6_natural]
    interleave_uniform inv_uniform thue'_def)

lemma thue'_code[code]: "thue' = SCons 1 (interleave thue' (inv thue'))"
  by (metis J.ctor_dtor prod.collapse head_thue' tail_thue')

definition thue :: stream where
  "thue = SCons 0 thue'"


subsection {* times *}

definition times :: "nat \<Rightarrow> stream \<Rightarrow> stream" where
  "times n s = dtor_corec_J (\<lambda>s. (n * head s, Inr (tail s))) s"

lemma head_times[simp]: "head (times n s) = n * head s"
  unfolding times_def J.dtor_corec
  by (simp add: map_pre_J_def BNF_Comp.id_bnf_comp_def)

lemma tail_times[simp]: "tail (times n s) = times n (tail s)"
  apply (subst times_def) unfolding J.dtor_corec
  by (simp add: map_pre_J_def BNF_Comp.id_bnf_comp_def times_def)

lemma times_code[code]: "times n (SCons m s) = SCons (n * m) (times n s)"
  by (metis J.ctor_dtor J.dtor_ctor fst_conv snd_conv prod.collapse head_times tail_times)

lemma times_uniform: "times m s = alg\<rho>9 (m, s)"
  unfolding times_def
  apply (rule fun_cong[OF sym[OF J.dtor_corec_unique]])
  unfolding alg\<rho>9 o_def[symmetric] o_assoc
  apply (simp add: map_pre_J_def BNF_Comp.id_bnf_comp_def fun_eq_iff J.dtor_ctor
    \<rho>9_def Let_def convol_def eval9_\<oo>\<pp>9 eval9_leaf9'
    o_eq_dest[OF Abs_\<Sigma>9_natural] alg\<Lambda>9_Inr alg\<rho>9_def)
  done


subsection {* ham *}

definition ham :: stream where
  "ham = corecUU9 (\<lambda>_. GUARD9 (1, MERGE9 (TIMES9 (2, CONT9 ()), TIMES9 (3, CONT9 ())))) ()"

lemma head_ham[simp]: "head ham = 1"
  unfolding ham_def corecUU9
  by (simp add: map_pre_J_def BNF_Comp.id_bnf_comp_def J.dtor_ctor eval9_leaf9')

lemma tail_ham[simp]: "tail ham = merge (times 2 ham) (times 3 ham)"
  apply (subst ham_def) unfolding corecUU9
  by (simp add: map_pre_J_def BNF_Comp.id_bnf_comp_def J.dtor_ctor eval9_leaf9' eval9_\<oo>\<pp>9
    alg\<Lambda>9_Inl alg\<Lambda>9_Inr alg\<Lambda>8_Inr o_eq_dest[OF Abs_\<Sigma>9_natural] o_eq_dest[OF Abs_\<Sigma>8_natural]
    merge_uniform times_uniform ham_def)

lemma ham_code[code]: "ham = SCons 1 (merge (times 2 ham) (times 3 ham))"
  by (metis J.ctor_dtor prod.collapse head_ham tail_ham)


subsection {* even *}

definition even :: "stream \<Rightarrow> stream" where
  "even s = dtor_corec_J (\<lambda>s. (head s, Inr (tail (tail s)))) s"

lemma head_even[simp]: "head (even s) = head s"
  unfolding even_def J.dtor_corec
  by (simp add: map_pre_J_def BNF_Comp.id_bnf_comp_def)

lemma tail_even[simp]: "tail (even s) = even (tail (tail s))"
  apply (subst even_def) unfolding J.dtor_corec
  by (simp add: map_pre_J_def BNF_Comp.id_bnf_comp_def even_def)

lemma even_code[code]: "even (SCons n (SCons m s)) = SCons n (even s)"
  by (metis J.ctor_dtor J.dtor_ctor fst_conv snd_conv prod.collapse head_even tail_even)


subsection {* odd *}

definition odd :: "stream \<Rightarrow> stream" where
  "odd s = dtor_corec_J (\<lambda>s. (head (tail s), Inr (tail (tail s)))) s"

lemma head_odd[simp]: "head (odd s) = head (tail s)"
  unfolding odd_def J.dtor_corec
  by (simp add: map_pre_J_def BNF_Comp.id_bnf_comp_def)

lemma tail_odd[simp]: "tail (odd s) = odd (tail (tail s))"
  apply (subst odd_def) unfolding J.dtor_corec
  by (simp add: map_pre_J_def BNF_Comp.id_bnf_comp_def odd_def)

lemma odd_code[code]: "odd (SCons n (SCons m s)) = SCons m (odd s)"
  by (metis J.ctor_dtor J.dtor_ctor fst_conv snd_conv prod.collapse head_odd tail_odd)


subsection {* drop *}

definition drop :: "nat \<Rightarrow> nat \<Rightarrow> stream \<Rightarrow> stream" where
  "drop i l s = dtor_corec_J (\<lambda>(i, l, s).
     case i of
       Suc i \<Rightarrow> (head s, Inr (i, l, tail s))
     | 0 \<Rightarrow> (head (tail s), Inr (l - 2, l, tail (tail s)))) (i, l, s)"

lemma head_drop[simp]: "head (drop i l s) = (case i of Suc _ \<Rightarrow> head s | 0 \<Rightarrow> head (tail s))"
  unfolding drop_def J.dtor_corec
  by (simp add: map_pre_J_def BNF_Comp.id_bnf_comp_def split: nat.splits)

lemma tail_drop[simp]:
  "tail (drop i l s) = (case i of Suc i \<Rightarrow> drop i l (tail s) | 0 \<Rightarrow> drop (l - 2) l (tail (tail s)))"
  unfolding drop_def J.dtor_corec
  by (simp add: map_pre_J_def BNF_Comp.id_bnf_comp_def split: nat.splits)

lemma drop_code[code]:
  "drop (Suc i) l (SCons m s) = SCons m (drop i l s)"
  "drop 0 l (SCons m (SCons n s)) = SCons n (drop (l - 2) l s)"
  by (smt2 J.ctor_dtor J.dtor_ctor fst_conv snd_conv prod.collapse head_drop tail_drop nat.case)+


subsection {* diff *}

definition diff :: "stream \<Rightarrow> stream" where
  "diff s = dtor_corec_J (\<lambda>s. (head (tail s) - head s, Inr (tail s))) s"

lemma head_diff[simp]: "head (diff s) = head (tail s) - head s"
  unfolding diff_def J.dtor_corec
  by (simp add: map_pre_J_def BNF_Comp.id_bnf_comp_def)

lemma tail_diff[simp]: "tail (diff s) = diff (tail s)"
  apply (subst diff_def) unfolding J.dtor_corec
  by (simp add: map_pre_J_def BNF_Comp.id_bnf_comp_def diff_def)

lemma diff_code[code]: "diff (SCons m (SCons n s)) = SCons (n - m) (diff (SCons n s))"
  by (metis J.ctor_dtor J.dtor_ctor fst_conv snd_conv prod.collapse head_diff tail_diff)


subsection {* Some Proofs *}

theorem thue_code[code]: "thue = SCons 0 (interleave (inv thue) (tail thue))"
  unfolding thue_def J.ctor_inject Pair_eq
  by (rule conjI[OF refl], coinduction rule: stream_coinduct0) (auto simp: J.dtor_ctor)

theorem plus_commute: "plus s t = plus t s"
  by (coinduction arbitrary: s t rule: stream_coinduct) auto

theorem plus_assoc: "plus (plus s t) u = plus s (plus t u)"
  by (coinduction arbitrary: s t u rule: stream_coinduct) auto

theorem plus_commute_assoc: "plus s (plus t u) = plus t (plus s u)"
  by (metis plus_assoc plus_commute)

theorem even_plus[simp]: "even (plus s t) = plus (even s) (even t)"
  by (coinduction arbitrary: s t rule: stream_coinduct) auto

theorem odd_alt: "odd s = even (tail s)"
  by (coinduction arbitrary: s rule: stream_coinduct) auto

theorem even_alt: "even s = SCons (head s) (odd (tail s))"
  by (coinduction arbitrary: s rule: stream_coinduct0) (auto simp: J.dtor_ctor odd_alt)

theorem sum_odd_fib: "sum (odd fib) = even fib"
  by (coinduction rule: stream_coinduct1)
    (auto simp: J.dtor_ctor plus_assoc plus_commute_assoc odd_alt
      intro: genCngdd1_alg\<rho>1[folded plus_uniform])

(*<*)
end
(*>*)
