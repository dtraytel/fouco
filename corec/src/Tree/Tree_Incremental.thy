header {* Incremental coinduction *}

theory Tree_Incremental
imports
  Main
begin


locale Incremental =
  fixes Retr :: "('a :: complete_lattice) \<Rightarrow> 'a"
  and Cl :: "('a :: complete_lattice) \<Rightarrow> 'a"
  assumes mono_Retr: "mono Retr"
      and mono_Cl: "mono Cl"
      and idem_Cl: "Cl (Cl r) = Cl r"
      and ext_Cl: "r \<le> Cl r"
      and Cl_Retr: "Cl r = r \<Longrightarrow> Cl (inf r (Retr r)) = inf r (Retr r)"
begin

lemma leq_Cl:
assumes "Cl s = s" and "r \<le> s"
shows "Cl r \<le> s"
by (metis assms monoE mono_Cl)

lemma Cl_respectful_Retr:
assumes rs: "r \<le> s" and rrs: "r \<le> Retr s"
shows "Cl r \<le> Retr (Cl s)"
proof-
  let ?ss = "Cl s"
  have "Cl ?ss = ?ss" using idem_Cl .
  from Cl_Retr[OF this] have 1: "Cl (inf ?ss (Retr ?ss)) = inf ?ss (Retr ?ss)" .
  have "r \<le> ?ss" using rs ext_Cl by (metis order_trans)
  moreover have "r \<le> Retr ?ss" using rrs ext_Cl mono_Retr by (metis mono_def order_trans)
  ultimately have "r \<le> inf ?ss (Retr ?ss)" by simp
  from leq_Cl[OF 1 this] show ?thesis by simp
qed

(* Parenthesis: Using that Cl is a closure operator, respectfulness is actually equivalent to Cl_Retr
(the proof does not use Cl_Retr) *)
lemma
assumes respectful: "\<And> r s. \<lbrakk>r \<le> s; r \<le> Retr s\<rbrakk> \<Longrightarrow> Cl r \<le> Retr (Cl s)"
and r: "Cl r = r"
shows "Cl (inf r (Retr r)) = inf r (Retr r)"
proof-
  have 1: "Cl (inf r (Retr r)) \<le> r" by (metis inf_le1 monoE mono_Cl r)
  have "Cl (inf r (Retr r)) \<le> Retr (Cl r)" by (rule respectful) auto
  hence "Cl (inf r (Retr r)) \<le> Retr r" unfolding r .
  with 1 show ?thesis by (metis antisym ext_Cl inf.bounded_iff)
qed
(* end parenthesis *)

(* The theorems from Dreyer, but stated directly with the "up to" G: *)

lemma Cl_sound_Retr: (* Dreyer seems to claim that only monotonicity of Cl suffices  *)
assumes "r \<le> Retr (Cl r)"
shows "r \<le> gfp Retr"
proof-
  have "Cl r \<le> Retr (Cl (Cl r))" apply(rule Cl_respectful_Retr)
  using ext_Cl assms by auto
  hence "Cl r \<le> Retr (Cl r)" unfolding idem_Cl .
  hence "Cl r \<le> gfp Retr" by (metis gfp_upperbound)
  thus ?thesis using ext_Cl by (metis order.trans)
qed

lemma mono_Retr_Cl: "mono (Retr o Cl)"
using mono_Retr mono_Cl unfolding mono_def by (metis comp_apply)

(* Dreyer only proves \<le>, since he does not assume extensiveness;
however, his greatest respectful function is extensive, so he could have proved that for it. *)
lemma gfp_Retr_Cl: "gfp (Retr o Cl) = gfp Retr"
proof(rule order_class.antisym)
  show "gfp (Retr \<circ> Cl) \<le> gfp Retr"
  apply(rule Cl_sound_Retr) using gfp_lemma2[OF mono_Retr_Cl] by simp
next
  show "gfp Retr \<le> gfp (Retr \<circ> Cl)"
  apply(rule gfp_mono) using ext_Cl mono_Retr unfolding mono_def by auto
qed

definition G :: "'a \<Rightarrow> 'a" where "G r \<equiv> gfp (\<lambda> s. Retr (Cl (sup r s)))"

lemma mono_pre_G: "mono (\<lambda> s. Retr (Cl (sup r s)))"
using mono_Retr mono_Cl unfolding mono_def by (metis dual_order.refl sup_mono)

lemma G_unfold: "G r = Retr (Cl (sup r (G r)))"
using gfp_unfold[OF mono_pre_G] unfolding G_def .

lemma G_mono[simp, intro]: "r \<le> s \<Longrightarrow> G r \<le> G s"
unfolding G_def apply(rule gfp_mono) by (metis monoE mono_Cl mono_Retr order_refl sup.mono)

lemma mono_G: "mono G"
using G_mono unfolding mono_def by auto

lemma G_initialize: "gfp Retr = G bot"
unfolding G_def gfp_Retr_Cl[symmetric] o_def by auto

lemma G_accumulate: "r \<le> G s \<longleftrightarrow> r \<le> G (sup s r)"
proof
  assume "r \<le> G s"  thus "r \<le> G (sup s r)"
  by (metis G_mono le_sup_iff sup.orderI sup_absorb2 sup_idem)
next
  assume r: "r \<le> G (sup s r)"
  have 0: "sup s (G (sup s r)) = sup (sup s r) (G (sup s r))"
  using r by (metis sup_absorb2 sup_commute sup_left_commute)
  have "G (sup s r) \<le> G s"
  unfolding G_def apply(rule gfp_upperbound) unfolding G_def[symmetric] 0
  unfolding G_unfold[symmetric] by simp
  thus "r \<le> G s" using r by (metis order.trans)
qed

lemma G_compose:
assumes 11: "s1 \<le> G r1" and 22: "s2 \<le> G r2" and 12: "r1 \<le> sup r s2" and 21: "r2 \<le> sup r s1"
shows "sup s1 s2 \<le> G r"
proof-
  let ?K = "G (sup r (sup s1 s2))"
  have "s1 \<le> G (sup r s2)" by (metis "11" "12" G_mono order.trans)
  also have "... \<le> ?K" by (metis G_mono le_sup_iff sup.orderI sup_idem)
  finally have s1: "s1 \<le> ?K" .
  have "s2 \<le> G (sup r s1)" by (metis "22" "21" G_mono order.trans)
  also have "... \<le> ?K" by (metis G_mono le_sup_iff sup.orderI sup_idem)
  finally have s2: "s2 \<le> ?K" .
  from s1 s2 have "sup s1 s2 \<le> ?K" by (metis sup_least)
  thus ?thesis unfolding G_accumulate[symmetric] .
qed

(* My incremental coinduction system, with their semantics (their suggestion was correct): *)

definition ded (infix "\<turnstile>" 40) where "r \<turnstile> s \<equiv> s \<le> Cl (sup r (G r))"

lemma gfp_le_G: "gfp Retr \<le> G r"
by (metis G_initialize bot.extremum mono_G mono_def)


(* Soundness of my rules (with the names from my paper): *)
theorem Ax:
assumes "s \<le> Cl (sup r (gfp Retr))"
shows "r \<turnstile> s"
using assms gfp_le_G unfolding ded_def
by (metis (hide_lams, mono_tags) eq_iff monoD mono_Cl order.trans sup.mono)

theorem Split:
assumes "\<And> s. s \<in> S \<Longrightarrow> r \<turnstile> s"
shows "r \<turnstile> Sup S"
using assms unfolding ded_def by (metis Sup_least)

(* Note one can prove something slightly more general than the following,
assuming "s \<le> Retr (Cl p)", but does not see useful. *)
theorem Coind:
assumes "s \<le> Retr p" and "sup r s \<turnstile> p"
shows "r \<turnstile> s"
(* p is the interpolant, ideally computable automatically for streams: *)
proof-
  let ?rs = "sup r s"
  have "s \<le> Retr (Cl (sup ?rs (G ?rs)))" using assms unfolding ded_def
    by (metis (full_types) monoD mono_Retr order_trans)
  hence "s \<le> G r" apply(subst G_accumulate) unfolding G_unfold[symmetric] .
  thus ?thesis unfolding ded_def
    by (metis ext_Cl order.trans sup.bounded_iff)
qed

theorem soundness_ded:
assumes "gfp Retr \<turnstile> s"
shows "s \<le> gfp Retr"
using assms unfolding ded_def
by (metis Cl_respectful_Retr Cl_sound_Retr G_unfold dual_order.antisym dual_order.refl
          ext_Cl gfp_le_G le_supI2 sup_least)


(* Simplification of Ax for the case where "gfp Retr" does not bring anything new
to Cl; e.g., as for codatatypes, where "gfp Retr" is equality and Cl is the congruence closure
(hence contains equality):*)

theorem Ax': assumes "s \<le> Cl r"  shows "r \<turnstile> s"
apply(rule Ax) using assms by (metis (full_types) le_sup_iff monoD mono_Cl sup_absorb2 sup_ge1)


end (* context Incremental *)



end