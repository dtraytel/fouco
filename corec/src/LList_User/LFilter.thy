(*<*)
theory LFilter
imports LList_Lib
begin
(*>*)

section \<open>lfilter\<close>

text \<open>
Here, we define a monomorphic filter function on lazy lists over natural numbers.
Unlike, the theory presented in the paper in general the rudimentary package currently
does not support polymorphism.
\<close>

inductive llist_in where
  "llist_in (LCons x xs) x"
| "llist_in xs y \<Longrightarrow> llist_in (LCons x xs) y"

abbreviation "lset xs \<equiv> {x. llist_in xs x}"

function lfilter\<^sub>r\<^sub>e\<^sub>c :: "(nat \<Rightarrow> bool) \<Rightarrow> llist \<Rightarrow> (llist + ((nat \<Rightarrow> bool) \<times> llist)) \<Sigma>\<Sigma>0 F \<Sigma>\<Sigma>0" where
  "lfilter\<^sub>r\<^sub>e\<^sub>c P xs =
      (if \<forall>x \<in> lset xs. \<not> P x then GUARD0 (Inl ())
      else if P (head xs) then GUARD0 (Inr (head xs, CONT0 (P, tail xs)))
      else lfilter\<^sub>r\<^sub>e\<^sub>c P (tail xs))"
by pat_completeness auto
termination
proof (relation "measure (\<lambda>(P, xs). LEAST n. P (head ((tail ^^ n) xs)))", rule wf_measure, clarsimp)
  fix P xs x
  assume "llist_in xs x" "P x" "\<not> P (head xs)"
  from this(1,2) obtain a where "P (head ((tail ^^ a) xs))"
    by (atomize_elim, induct xs x rule: llist_in.induct) (auto simp: J.dtor_ctor funpow_Suc_right
      simp del: funpow.simps(2) intro: exI[of _ 0] exI[of _ "Suc i" for i])
  moreover
  with \<open>\<not> P (head xs)\<close>
    have "(LEAST n. P (head ((tail ^^ n) xs))) = Suc (LEAST n. P (head ((tail ^^ Suc n) xs)))"
    by (intro Least_Suc) auto
  then show "(LEAST n. P (head ((tail ^^ n) (tail xs)))) < (LEAST n. P (head ((tail ^^ n) xs)))"
    by (simp add: funpow_swap1[of tail])
qed

definition lfilter :: "(nat \<Rightarrow> bool) \<Rightarrow> llist \<Rightarrow> llist" where
  "lfilter P xs = corecUU0 (split lfilter\<^sub>r\<^sub>e\<^sub>c) (P, xs)"

lemma lfilter_code:
  "lfilter P xs =
     (if \<forall>x \<in> lset xs. \<not> P x then LNil
      else if P (head xs) then LCons (head xs) (lfilter P (tail xs))
      else lfilter P (tail xs))"
  unfolding lfilter_def
  by (subst corecUU0, unfold split, subst lfilter\<^sub>r\<^sub>e\<^sub>c.simps)
    (simp add: map_pre_J_def BNF_Comp.id_bnf_comp_def
    eval0_\<oo>\<pp>0 eval0_leaf0' o_eq_dest[OF Abs_\<Sigma>0_natural] corecUU0
    imp_conjL[symmetric] imp_conjR conj_commute del: not_all)

text \<open>Here is an alternative definition using partial\_function.\<close>

partial_function (tailrec) lfilter2\<^sub>r\<^sub>e\<^sub>c ::
  "(nat \<Rightarrow> bool) \<Rightarrow> llist \<Rightarrow> (llist + ((nat \<Rightarrow> bool) \<times> llist)) \<Sigma>\<Sigma>0 F \<Sigma>\<Sigma>0" where
  "lfilter2\<^sub>r\<^sub>e\<^sub>c P xs =
      (if \<forall>x \<in> lset xs. \<not> P x then GUARD0 (Inl ())
      else if P (head xs) then GUARD0 (Inr (head xs, CONT0 (P, tail xs)))
      else lfilter2\<^sub>r\<^sub>e\<^sub>c P (tail xs))"

definition lfilter2 :: "(nat \<Rightarrow> bool) \<Rightarrow> llist \<Rightarrow> llist" where
  "lfilter2 P xs = corecUU0 (split lfilter2\<^sub>r\<^sub>e\<^sub>c) (P, xs)"

lemma lfilter2_code:
  "lfilter2 P xs =
     (if \<forall>x \<in> lset xs. \<not> P x then LNil
      else if P (head xs) then LCons (head xs) (lfilter2 P (tail xs))
      else lfilter2 P (tail xs))"
  unfolding lfilter2_def
  by (subst corecUU0, unfold split, subst lfilter2\<^sub>r\<^sub>e\<^sub>c.simps)
    (simp add: map_pre_J_def BNF_Comp.id_bnf_comp_def
    eval0_\<oo>\<pp>0 eval0_leaf0' o_eq_dest[OF Abs_\<Sigma>0_natural] corecUU0
    imp_conjL[symmetric] imp_conjR conj_commute del: not_all)

end
