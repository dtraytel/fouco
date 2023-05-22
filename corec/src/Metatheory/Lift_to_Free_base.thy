header {* Copy of lift_to_free, but for the initial distributive law  *}

theory Lift_to_Free_base
imports Distributive_Law_base
begin


subsection{* The lifting *}

(* Our aim is lift ll to an (S,S,T)-distributive law dd_base compatible with the monadic structure. *)

(* In order to be able to define dd_base, we need a larger codomain type: *)
definition ddd_base :: "('a \<times> 'a F) \<Sigma>\<Sigma>_base \<Rightarrow> 'a \<Sigma>\<Sigma>_base \<times> 'a \<Sigma>\<Sigma>_base F" where
"ddd_base = ext_base <\<oo>\<pp>_base o \<Sigma>_base_map fst, F_map flat_base o \<Lambda>_base> (leaf_base ** F_map leaf_base)"

definition dd_base :: "('a \<times> 'a F) \<Sigma>\<Sigma>_base \<Rightarrow> 'a \<Sigma>\<Sigma>_base F" where
"dd_base = snd o ddd_base"

lemma ddd_base_transfer[transfer_rule]:
  "(\<Sigma>\<Sigma>_base_rel (rel_prod R (F_rel R)) ===> rel_prod (\<Sigma>\<Sigma>_base_rel R) (F_rel (\<Sigma>\<Sigma>_base_rel R))) ddd_base ddd_base"
  unfolding ddd_base_def ext_base_alt by transfer_prover

lemma dd_base_transfer[transfer_rule]:
  "(\<Sigma>\<Sigma>_base_rel (rel_prod R (F_rel R)) ===> F_rel (\<Sigma>\<Sigma>_base_rel R)) dd_base dd_base"
  unfolding dd_base_def by transfer_prover

lemma F_rel_\<Sigma>\<Sigma>_base_rel: "\<Sigma>\<Sigma>_base_rel (rel_prod R (F_rel R)) x y \<Longrightarrow> F_rel (\<Sigma>\<Sigma>_base_rel R) (dd_base x) (dd_base y)"
  by (erule rel_funD[OF dd_base_transfer])

(* We verify the facts for dd_base: *)
theorem dd_base_leaf_base: "dd_base o leaf_base = F_map leaf_base o snd"
unfolding dd_base_def ddd_base_def by auto

lemma ddd_base_natural: "ddd_base o \<Sigma>\<Sigma>_base_map (f ** F_map f) = (\<Sigma>\<Sigma>_base_map f ** F_map (\<Sigma>\<Sigma>_base_map f)) o ddd_base"
  using ddd_base_transfer[of "BNF_Def.Grp UNIV f"]
  unfolding F_rel_Grp prod.rel_Grp \<Sigma>\<Sigma>_base.rel_Grp
  unfolding Grp_def rel_fun_def by auto

theorem dd_base_natural: "dd_base o \<Sigma>\<Sigma>_base_map (f ** F_map f) = F_map (\<Sigma>\<Sigma>_base_map f) o dd_base"
  using dd_base_transfer[of "BNF_Def.Grp UNIV f"]
  unfolding F_rel_Grp prod.rel_Grp \<Sigma>\<Sigma>_base.rel_Grp
  unfolding Grp_def rel_fun_def by auto

lemma \<Lambda>_base_dd_base: "\<Lambda>_base = dd_base o \<oo>\<pp>_base o \<Sigma>_base_map leaf_base"
  unfolding dd_base_def ddd_base_def o_assoc[symmetric] \<Sigma>_base.map_comp0[symmetric] ext_base_commute
  unfolding o_assoc snd_convol ext_base_comp_leaf_base
  unfolding o_assoc[symmetric] \<Lambda>_base_natural
  unfolding o_assoc F_map_comp[symmetric] leaf_base_flat_base F_map_id id_o
  ..

lemma fst_ddd_base: "fst o ddd_base = \<Sigma>\<Sigma>_base_map fst"
proof-
  have "fst o ddd_base = ext_base \<oo>\<pp>_base (leaf_base o fst)"
  apply(rule ext_base_unique) unfolding ddd_base_def o_assoc[symmetric] ext_base_comp_leaf_base ext_base_commute
  unfolding o_assoc fst_comp_map_prod fst_convol
  unfolding o_assoc[symmetric] \<Sigma>_base.map_comp0 by(rule refl, rule refl)
  also have "... = \<Sigma>\<Sigma>_base_map fst"
  apply(rule sym, rule ext_base_unique)
  unfolding leaf_base_natural \<oo>\<pp>_base_natural by(rule refl, rule refl)
  finally show ?thesis .
qed

lemma ddd_base_flat_base: "(flat_base ** F_map flat_base) \<circ> ddd_base \<circ> \<Sigma>\<Sigma>_base_map ddd_base = ddd_base o flat_base" (is "?L = ?R")
proof-
  have "?L = ext_base <\<oo>\<pp>_base o \<Sigma>_base_map fst, F_map flat_base o \<Lambda>_base> ddd_base"
  proof(rule ext_base_unique)
    show "(flat_base ** F_map flat_base) \<circ> ddd_base \<circ> \<Sigma>\<Sigma>_base_map ddd_base \<circ> leaf_base = ddd_base"
    unfolding ddd_base_def unfolding o_assoc[symmetric] leaf_base_natural
    unfolding o_assoc
    apply(subst o_assoc[symmetric]) unfolding ext_base_comp_leaf_base
    unfolding map_prod.comp F_map_comp[symmetric] flat_base_leaf_base F_map_id map_prod.id id_o ..
  next
    have 1: "<flat_base \<circ> (\<oo>\<pp>_base \<circ> \<Sigma>_base_map fst) , F_map flat_base \<circ> (F_map flat_base \<circ> \<Lambda>_base)>  =
             <\<oo>\<pp>_base \<circ> \<Sigma>_base_map fst , F_map flat_base \<circ> \<Lambda>_base> \<circ> \<Sigma>_base_map (flat_base ** F_map flat_base)"
    unfolding o_assoc unfolding flat_base_commute[symmetric]
    apply(rule fst_snd_cong) unfolding o_assoc fst_convol snd_convol
    unfolding o_assoc[symmetric] \<Sigma>_base.map_comp0[symmetric] fst_comp_map_prod snd_comp_map_prod
    unfolding \<Lambda>_base_natural unfolding o_assoc F_map_comp[symmetric] flat_base_assoc
    by(rule refl, rule refl)
    show "(flat_base ** F_map flat_base) \<circ> ddd_base \<circ> \<Sigma>\<Sigma>_base_map ddd_base \<circ> \<oo>\<pp>_base =
          <\<oo>\<pp>_base \<circ> \<Sigma>_base_map fst , F_map flat_base \<circ> \<Lambda>_base> \<circ> \<Sigma>_base_map (flat_base ** F_map flat_base \<circ> ddd_base \<circ> \<Sigma>\<Sigma>_base_map ddd_base)"
    unfolding ddd_base_def unfolding o_assoc[symmetric] unfolding \<oo>\<pp>_base_natural[symmetric]
    unfolding o_assoc
    apply(subst o_assoc[symmetric]) unfolding ext_base_commute
    unfolding o_assoc[symmetric] \<Sigma>_base.map_comp0[symmetric]
    unfolding \<Sigma>_base.map_comp0
    unfolding o_assoc unfolding map_prod_o_convol
    unfolding ext_base_\<Sigma>\<Sigma>_base_map[symmetric] 1 ..
  qed
  also have "... = ?R"
  proof(rule sym, rule ext_base_unique)
    show "ddd_base \<circ> flat_base \<circ> leaf_base = ddd_base" unfolding o_assoc[symmetric] flat_base_leaf_base o_id ..
  next
    show "ddd_base \<circ> flat_base \<circ> \<oo>\<pp>_base = <\<oo>\<pp>_base \<circ> \<Sigma>_base_map fst , F_map flat_base \<circ> \<Lambda>_base> \<circ> \<Sigma>_base_map (ddd_base \<circ> flat_base)"
    unfolding ddd_base_def unfolding o_assoc[symmetric] unfolding flat_base_commute[symmetric]
    unfolding o_assoc unfolding ext_base_commute \<Sigma>_base.map_comp0 unfolding o_assoc ..
  qed
  finally show ?thesis .
qed

theorem dd_base_flat_base: "F_map flat_base \<circ> dd_base \<circ> \<Sigma>\<Sigma>_base_map <\<Sigma>\<Sigma>_base_map fst, dd_base> = dd_base o flat_base"
proof-
  have 1: "snd o ((flat_base ** F_map flat_base) \<circ> ddd_base \<circ> \<Sigma>\<Sigma>_base_map ddd_base) = snd o (ddd_base o flat_base)"
  unfolding ddd_base_flat_base ..
  have 2: "ddd_base = <\<Sigma>\<Sigma>_base_map fst , snd \<circ> ddd_base>" apply(rule fst_snd_cong)
  unfolding fst_ddd_base by auto
  show ?thesis unfolding dd_base_def
  unfolding 1[symmetric, unfolded o_assoc snd_comp_map_prod] o_assoc 2[symmetric] ..
qed


(* The next two theorems are not necessary for the development.
They show that the conditions dd_base_leaf_base and dd_base_flat_base imply the
more standard conditions for the distributive law dd_base' = <\<Sigma>\<Sigma>_base_map fst, dd_base>
for the functors \<Sigma>\<Sigma>_base and 'a F' = 'a \<times> 'a F_ In fact, they can be shown
equivalent to these. *)

lemma dd_base_leaf_base2: "<\<Sigma>\<Sigma>_base_map fst, dd_base> o leaf_base = leaf_base ** F_map leaf_base"
apply (rule fst_snd_cong) unfolding o_assoc by (simp_all add: leaf_base_natural dd_base_leaf_base)

lemma ddd_base_leaf_base: "ddd_base \<circ> leaf_base = leaf_base ** F_map leaf_base"
unfolding ddd_base_def ext_base_comp_leaf_base ..

lemma ddd_base_\<oo>\<pp>_base:
"ddd_base \<circ> \<oo>\<pp>_base = <\<oo>\<pp>_base \<circ> \<Sigma>_base_map fst , F_map flat_base \<circ> \<Lambda>_base> \<circ> \<Sigma>_base_map ddd_base"
unfolding ddd_base_def ext_base_commute ..


(* More customization *)

lemma \<Sigma>\<Sigma>_base_rel_induct_pointfree:
assumes leaf: "\<And> x1 x2. R x1 x2 \<Longrightarrow> phi (leaf_base x1) (leaf_base x2)"
and \<oo>\<pp>: "\<And> y1 y2. \<lbrakk>\<Sigma>_base_rel (\<Sigma>\<Sigma>_base_rel R) y1 y2; \<Sigma>_base_rel phi y1 y2\<rbrakk> \<Longrightarrow> phi (\<oo>\<pp>_base y1) (\<oo>\<pp>_base y2)"
shows "\<Sigma>\<Sigma>_base_rel R \<le> phi"
proof-
  have "\<Sigma>\<Sigma>_base_rel R \<le> phi \<sqinter> \<Sigma>\<Sigma>_base_rel R"
  apply(induct rule: \<Sigma>\<Sigma>_base.ctor_rel_induct)
  using assms \<Sigma>\<Sigma>_base.rel_inject[of R] unfolding rel_pre_\<Sigma>\<Sigma>_base_def \<Sigma>\<Sigma>_base.leaf_base_def \<Sigma>\<Sigma>_base.\<oo>\<pp>_base_def
  using inf_greatest[OF \<Sigma>_base.rel_mono[OF inf_le1] \<Sigma>_base.rel_mono[OF inf_le2]]
  unfolding rel_sum_def BNF_Comp.id_bnf_comp_def vimage2p_def by (auto split: sum.splits) blast+
  thus ?thesis by simp
qed

lemma \<Sigma>\<Sigma>_base_rel_induct[case_names leaf \<oo>\<pp>]:
assumes leaf: "\<And> x1 x2. R x1 x2 \<Longrightarrow> phi (leaf_base x1) (leaf_base x2)"
and \<oo>\<pp>: "\<And> y1 y2. \<lbrakk>\<Sigma>_base_rel (\<Sigma>\<Sigma>_base_rel R) y1 y2; \<Sigma>_base_rel phi y1 y2\<rbrakk> \<Longrightarrow> phi (\<oo>\<pp>_base y1) (\<oo>\<pp>_base y2)"
shows "\<Sigma>\<Sigma>_base_rel R t1 t2 \<longrightarrow> phi t1 t2"
using \<Sigma>\<Sigma>_base_rel_induct_pointfree[of R, OF assms] by auto

end