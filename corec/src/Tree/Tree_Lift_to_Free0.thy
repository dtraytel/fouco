header {* Copy of lift_to_free, but for the initial distributive law  *}

theory Tree_Lift_to_Free0
imports Tree_Distributive_Law0
begin


subsection{* The lifting *}

(* Our aim is lift ll to an (S,S,T)-distributive law dd0 compatible with the monadic structure. *)

(* In order to be able to define dd0, we need a larger codomain type: *)
definition ddd0 :: "('a \<times> 'a F) \<Sigma>\<Sigma>0 \<Rightarrow> 'a \<Sigma>\<Sigma>0 \<times> 'a \<Sigma>\<Sigma>0 F" where
"ddd0 = ext0 <\<oo>\<pp>0 o \<Sigma>0_map fst, F_map flat0 o \<Lambda>0> (leaf0 ** F_map leaf0)"

definition dd0 :: "('a \<times> 'a F) \<Sigma>\<Sigma>0 \<Rightarrow> 'a \<Sigma>\<Sigma>0 F" where
"dd0 = snd o ddd0"

lemma ddd0_transfer[transfer_rule]:
  "(\<Sigma>\<Sigma>0_rel (rel_prod R (F_rel R)) ===> rel_prod (\<Sigma>\<Sigma>0_rel R) (F_rel (\<Sigma>\<Sigma>0_rel R))) ddd0 ddd0"
  unfolding ddd0_def ext0_alt by transfer_prover

lemma dd0_transfer[transfer_rule]:
  "(\<Sigma>\<Sigma>0_rel (rel_prod R (F_rel R)) ===> F_rel (\<Sigma>\<Sigma>0_rel R)) dd0 dd0"
  unfolding dd0_def by transfer_prover

lemma F_rel_\<Sigma>\<Sigma>0_rel: "\<Sigma>\<Sigma>0_rel (rel_prod R (F_rel R)) x y \<Longrightarrow> F_rel (\<Sigma>\<Sigma>0_rel R) (dd0 x) (dd0 y)"
  by (erule rel_funD[OF dd0_transfer])

(* We verify the facts for dd0: *)
theorem dd0_leaf0: "dd0 o leaf0 = F_map leaf0 o snd"
unfolding dd0_def ddd0_def by auto

lemma ddd0_natural: "ddd0 o \<Sigma>\<Sigma>0_map (f ** F_map f) = (\<Sigma>\<Sigma>0_map f ** F_map (\<Sigma>\<Sigma>0_map f)) o ddd0"
  using ddd0_transfer[of "BNF_Def.Grp UNIV f"]
  unfolding F_rel_Grp prod.rel_Grp \<Sigma>\<Sigma>0.rel_Grp
  unfolding Grp_def rel_fun_def by auto

theorem dd0_natural: "dd0 o \<Sigma>\<Sigma>0_map (f ** F_map f) = F_map (\<Sigma>\<Sigma>0_map f) o dd0"
  using dd0_transfer[of "BNF_Def.Grp UNIV f"]
  unfolding F_rel_Grp prod.rel_Grp \<Sigma>\<Sigma>0.rel_Grp
  unfolding Grp_def rel_fun_def by auto

lemma \<Lambda>0_dd0: "\<Lambda>0 = dd0 o \<oo>\<pp>0 o \<Sigma>0_map leaf0"
  unfolding dd0_def ddd0_def o_assoc[symmetric] \<Sigma>0.map_comp0[symmetric] ext0_commute
  unfolding o_assoc snd_convol ext0_comp_leaf0
  unfolding o_assoc[symmetric] \<Lambda>0_natural
  unfolding o_assoc F_map_comp[symmetric] leaf0_flat0 F_map_id id_o
  ..

lemma fst_ddd0: "fst o ddd0 = \<Sigma>\<Sigma>0_map fst"
proof-
  have "fst o ddd0 = ext0 \<oo>\<pp>0 (leaf0 o fst)"
  apply(rule ext0_unique) unfolding ddd0_def o_assoc[symmetric] ext0_comp_leaf0 ext0_commute
  unfolding o_assoc fst_comp_map_prod fst_convol
  unfolding o_assoc[symmetric] \<Sigma>0.map_comp0 by(rule refl, rule refl)
  also have "... = \<Sigma>\<Sigma>0_map fst"
  apply(rule sym, rule ext0_unique)
  unfolding leaf0_natural \<oo>\<pp>0_natural by(rule refl, rule refl)
  finally show ?thesis .
qed

lemma ddd0_flat0: "(flat0 ** F_map flat0) \<circ> ddd0 \<circ> \<Sigma>\<Sigma>0_map ddd0 = ddd0 o flat0" (is "?L = ?R")
proof-
  have "?L = ext0 <\<oo>\<pp>0 o \<Sigma>0_map fst, F_map flat0 o \<Lambda>0> ddd0"
  proof(rule ext0_unique)
    show "(flat0 ** F_map flat0) \<circ> ddd0 \<circ> \<Sigma>\<Sigma>0_map ddd0 \<circ> leaf0 = ddd0"
    unfolding ddd0_def unfolding o_assoc[symmetric] leaf0_natural
    unfolding o_assoc
    apply(subst o_assoc[symmetric]) unfolding ext0_comp_leaf0
    unfolding map_prod.comp F_map_comp[symmetric] flat0_leaf0 F_map_id map_prod.id id_o ..
  next
    have 1: "<flat0 \<circ> (\<oo>\<pp>0 \<circ> \<Sigma>0_map fst) , F_map flat0 \<circ> (F_map flat0 \<circ> \<Lambda>0)>  =
             <\<oo>\<pp>0 \<circ> \<Sigma>0_map fst , F_map flat0 \<circ> \<Lambda>0> \<circ> \<Sigma>0_map (flat0 ** F_map flat0)"
    unfolding o_assoc unfolding flat0_commute[symmetric]
    apply(rule fst_snd_cong) unfolding o_assoc fst_convol snd_convol
    unfolding o_assoc[symmetric] \<Sigma>0.map_comp0[symmetric] fst_comp_map_prod snd_comp_map_prod
    unfolding \<Lambda>0_natural unfolding o_assoc F_map_comp[symmetric] flat0_assoc
    by(rule refl, rule refl)
    show "(flat0 ** F_map flat0) \<circ> ddd0 \<circ> \<Sigma>\<Sigma>0_map ddd0 \<circ> \<oo>\<pp>0 =
          <\<oo>\<pp>0 \<circ> \<Sigma>0_map fst , F_map flat0 \<circ> \<Lambda>0> \<circ> \<Sigma>0_map (flat0 ** F_map flat0 \<circ> ddd0 \<circ> \<Sigma>\<Sigma>0_map ddd0)"
    unfolding ddd0_def unfolding o_assoc[symmetric] unfolding \<oo>\<pp>0_natural[symmetric]
    unfolding o_assoc
    apply(subst o_assoc[symmetric]) unfolding ext0_commute
    unfolding o_assoc[symmetric] \<Sigma>0.map_comp0[symmetric]
    unfolding \<Sigma>0.map_comp0
    unfolding o_assoc unfolding map_prod_o_convol
    unfolding ext0_\<Sigma>\<Sigma>0_map[symmetric] 1 ..
  qed
  also have "... = ?R"
  proof(rule sym, rule ext0_unique)
    show "ddd0 \<circ> flat0 \<circ> leaf0 = ddd0" unfolding o_assoc[symmetric] flat0_leaf0 o_id ..
  next
    show "ddd0 \<circ> flat0 \<circ> \<oo>\<pp>0 = <\<oo>\<pp>0 \<circ> \<Sigma>0_map fst , F_map flat0 \<circ> \<Lambda>0> \<circ> \<Sigma>0_map (ddd0 \<circ> flat0)"
    unfolding ddd0_def unfolding o_assoc[symmetric] unfolding flat0_commute[symmetric]
    unfolding o_assoc unfolding ext0_commute \<Sigma>0.map_comp0 unfolding o_assoc ..
  qed
  finally show ?thesis .
qed

theorem dd0_flat0: "F_map flat0 \<circ> dd0 \<circ> \<Sigma>\<Sigma>0_map <\<Sigma>\<Sigma>0_map fst, dd0> = dd0 o flat0"
proof-
  have 1: "snd o ((flat0 ** F_map flat0) \<circ> ddd0 \<circ> \<Sigma>\<Sigma>0_map ddd0) = snd o (ddd0 o flat0)"
  unfolding ddd0_flat0 ..
  have 2: "ddd0 = <\<Sigma>\<Sigma>0_map fst , snd \<circ> ddd0>" apply(rule fst_snd_cong)
  unfolding fst_ddd0 by auto
  show ?thesis unfolding dd0_def
  unfolding 1[symmetric, unfolded o_assoc snd_comp_map_prod] o_assoc 2[symmetric] ..
qed


(* The next two theorems are not necessary for the development.
They show that the conditions dd0_leaf0 and dd0_flat0 imply the
more standard conditions for the distributive law dd0' = <\<Sigma>\<Sigma>0_map fst, dd0>
for the functors \<Sigma>\<Sigma>0 and 'a F' = 'a \<times> 'a F_ In fact, they can be shown
equivalent to these. *)

lemma dd0_leaf02: "<\<Sigma>\<Sigma>0_map fst, dd0> o leaf0 = leaf0 ** F_map leaf0"
apply (rule fst_snd_cong) unfolding o_assoc by (simp_all add: leaf0_natural dd0_leaf0)

lemma ddd0_leaf0: "ddd0 \<circ> leaf0 = leaf0 ** F_map leaf0"
unfolding ddd0_def ext0_comp_leaf0 ..

lemma ddd0_\<oo>\<pp>0:
"ddd0 \<circ> \<oo>\<pp>0 = <\<oo>\<pp>0 \<circ> \<Sigma>0_map fst , F_map flat0 \<circ> \<Lambda>0> \<circ> \<Sigma>0_map ddd0"
unfolding ddd0_def ext0_commute ..


(* More customization *)

lemma \<Sigma>\<Sigma>0_rel_induct_pointfree:
assumes leaf: "\<And> x1 x2. R x1 x2 \<Longrightarrow> phi (leaf0 x1) (leaf0 x2)"
and \<oo>\<pp>: "\<And> y1 y2. \<lbrakk>\<Sigma>0_rel (\<Sigma>\<Sigma>0_rel R) y1 y2; \<Sigma>0_rel phi y1 y2\<rbrakk> \<Longrightarrow> phi (\<oo>\<pp>0 y1) (\<oo>\<pp>0 y2)"
shows "\<Sigma>\<Sigma>0_rel R \<le> phi"
proof-
  have "\<Sigma>\<Sigma>0_rel R \<le> phi \<sqinter> \<Sigma>\<Sigma>0_rel R"
  apply(induct rule: \<Sigma>\<Sigma>0.ctor_rel_induct)
  using assms \<Sigma>\<Sigma>0.rel_inject[of R] unfolding rel_pre_\<Sigma>\<Sigma>0_def \<Sigma>\<Sigma>0.leaf0_def \<Sigma>\<Sigma>0.\<oo>\<pp>0_def
  using inf_greatest[OF \<Sigma>0.rel_mono[OF inf_le1] \<Sigma>0.rel_mono[OF inf_le2]]
  unfolding rel_sum_def BNF_Comp.id_bnf_comp_def vimage2p_def by (auto split: sum.splits) blast+
  thus ?thesis by simp
qed

lemma \<Sigma>\<Sigma>0_rel_induct[case_names leaf \<oo>\<pp>]:
assumes leaf: "\<And> x1 x2. R x1 x2 \<Longrightarrow> phi (leaf0 x1) (leaf0 x2)"
and \<oo>\<pp>: "\<And> y1 y2. \<lbrakk>\<Sigma>0_rel (\<Sigma>\<Sigma>0_rel R) y1 y2; \<Sigma>0_rel phi y1 y2\<rbrakk> \<Longrightarrow> phi (\<oo>\<pp>0 y1) (\<oo>\<pp>0 y2)"
shows "\<Sigma>\<Sigma>0_rel R t1 t2 \<longrightarrow> phi t1 t2"
using \<Sigma>\<Sigma>0_rel_induct_pointfree[of R, OF assms] by auto

end