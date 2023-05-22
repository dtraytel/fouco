header {* Lifting of the distributive law to the free algebra *}


(* This is silimar to Lift_to_Free, but uses \<Lambda>_step, \<Sigma>\<Sigma>_step, dd_step, SpK instead of S, etc. *)

theory Lift_to_Free_step
imports Distributive_Law_step
begin

subsection{* The lifting *}

(* Our aim is lift \<Lambda>_step to an (SpK,SpK,T)-distributive law dd_step compatible with the monadic structure. *)

(* In order to be able to define dd_step, we need a larger codomain type: *)
definition ddd_step :: "('a \<times> 'a F) \<Sigma>\<Sigma>_step \<Rightarrow> 'a \<Sigma>\<Sigma>_step \<times> 'a \<Sigma>\<Sigma>_step F" where
"ddd_step = ext_step <\<oo>\<pp>_step o \<Sigma>_step_map fst, F_map flat_step o \<Lambda>_step> (leaf_step ** F_map leaf_step)"

definition dd_step :: "('a \<times> 'a F) \<Sigma>\<Sigma>_step \<Rightarrow> 'a \<Sigma>\<Sigma>_step F" where
"dd_step = snd o ddd_step"

lemma ddd_step_transfer[transfer_rule]:
  "(\<Sigma>\<Sigma>_step_rel (rel_prod R (F_rel R)) ===> rel_prod (\<Sigma>\<Sigma>_step_rel R) (F_rel (\<Sigma>\<Sigma>_step_rel R))) ddd_step ddd_step"
  unfolding ddd_step_def ext_step_alt by transfer_prover

lemma dd_step_transfer[transfer_rule]:
  "(\<Sigma>\<Sigma>_step_rel (rel_prod R (F_rel R)) ===> F_rel (\<Sigma>\<Sigma>_step_rel R)) dd_step dd_step"
  unfolding dd_step_def by transfer_prover

lemma F_rel_\<Sigma>\<Sigma>_step_rel: "\<Sigma>\<Sigma>_step_rel (rel_prod R (F_rel R)) x y \<Longrightarrow> F_rel (\<Sigma>\<Sigma>_step_rel R) (dd_step x) (dd_step y)"
  by (erule rel_funD[OF dd_step_transfer])

(* We verify the facts for dd_step: *)
theorem dd_step_leaf_step: "dd_step o leaf_step = F_map leaf_step o snd"
unfolding dd_step_def ddd_step_def o_assoc[symmetric] ext_step_comp_leaf_step snd_comp_map_prod ..

lemma ddd_step_natural: "ddd_step o \<Sigma>\<Sigma>_step_map (f ** F_map f) = (\<Sigma>\<Sigma>_step_map f ** F_map (\<Sigma>\<Sigma>_step_map f)) o ddd_step"
  using ddd_step_transfer[of "BNF_Def.Grp UNIV f"]
  unfolding F_rel_Grp prod.rel_Grp \<Sigma>\<Sigma>_step.rel_Grp
  unfolding Grp_def rel_fun_def by auto

theorem dd_step_natural: "dd_step o \<Sigma>\<Sigma>_step_map (f ** F_map f) = F_map (\<Sigma>\<Sigma>_step_map f) o dd_step"
  using dd_step_transfer[of "BNF_Def.Grp UNIV f"]
  unfolding F_rel_Grp prod.rel_Grp \<Sigma>\<Sigma>_step.rel_Grp
  unfolding Grp_def rel_fun_def by auto

lemma \<Lambda>_step_dd_step: "\<Lambda>_step = dd_step o \<oo>\<pp>_step o \<Sigma>_step_map leaf_step"
  unfolding dd_step_def ddd_step_def o_assoc[symmetric] \<Sigma>_step.map_comp0[symmetric] ext_step_commute
  unfolding o_assoc snd_convol ext_step_comp_leaf_step
  unfolding o_assoc[symmetric] \<Lambda>_step_natural
  unfolding o_assoc F_map_comp[symmetric] leaf_step_flat_step F_map_id id_o
  ..

lemma fst_ddd_step: "fst o ddd_step = \<Sigma>\<Sigma>_step_map fst"
proof-
  have "fst o ddd_step = ext_step \<oo>\<pp>_step (leaf_step o fst)"
  apply(rule ext_step_unique) unfolding ddd_step_def o_assoc[symmetric] ext_step_comp_leaf_step ext_step_commute
  unfolding o_assoc fst_comp_map_prod fst_convol
  unfolding o_assoc[symmetric] \<Sigma>_step.map_comp0 by(rule refl, rule refl)
  also have "... = \<Sigma>\<Sigma>_step_map fst"
  apply(rule sym, rule ext_step_unique)
  unfolding leaf_step_natural \<oo>\<pp>_step_natural by(rule refl, rule refl)
  finally show ?thesis .
qed

lemma ddd_step_flat_step: "(flat_step ** F_map flat_step) \<circ> ddd_step \<circ> \<Sigma>\<Sigma>_step_map ddd_step = ddd_step o flat_step" (is "?L = ?R")
proof-
  have "?L = ext_step <\<oo>\<pp>_step o \<Sigma>_step_map fst, F_map flat_step o \<Lambda>_step> ddd_step"
  proof(rule ext_step_unique)
    show "(flat_step ** F_map flat_step) \<circ> ddd_step \<circ> \<Sigma>\<Sigma>_step_map ddd_step \<circ> leaf_step = ddd_step"
    unfolding ddd_step_def unfolding o_assoc[symmetric] leaf_step_natural
    unfolding o_assoc
    apply(subst o_assoc[symmetric]) unfolding ext_step_comp_leaf_step
    unfolding map_prod.comp F_map_comp[symmetric] flat_step_leaf_step F_map_id map_prod.id id_o ..
  next
    have A: "<flat_step \<circ> (\<oo>\<pp>_step \<circ> \<Sigma>_step_map fst) , F_map flat_step \<circ> (F_map flat_step \<circ> \<Lambda>_step)>  =
             <\<oo>\<pp>_step \<circ> \<Sigma>_step_map fst , F_map flat_step \<circ> \<Lambda>_step> \<circ> \<Sigma>_step_map (flat_step ** F_map flat_step)"
    unfolding o_assoc unfolding flat_step_commute[symmetric]
    apply(rule fst_snd_cong) unfolding o_assoc fst_convol snd_convol
    unfolding o_assoc[symmetric] \<Sigma>_step.map_comp0[symmetric] fst_comp_map_prod snd_comp_map_prod
    unfolding \<Lambda>_step_natural unfolding o_assoc F_map_comp[symmetric] flat_step_assoc by(rule refl, rule refl)
    show "(flat_step ** F_map flat_step) \<circ> ddd_step \<circ> \<Sigma>\<Sigma>_step_map ddd_step \<circ> \<oo>\<pp>_step =
          <\<oo>\<pp>_step \<circ> \<Sigma>_step_map fst , F_map flat_step \<circ> \<Lambda>_step> \<circ> \<Sigma>_step_map (flat_step ** F_map flat_step \<circ> ddd_step \<circ> \<Sigma>\<Sigma>_step_map ddd_step)"
    unfolding ddd_step_def unfolding o_assoc[symmetric] unfolding \<oo>\<pp>_step_natural[symmetric]
    unfolding o_assoc
    apply(subst o_assoc[symmetric]) unfolding ext_step_commute
    unfolding o_assoc[symmetric] \<Sigma>_step.map_comp0[symmetric]
    unfolding \<Sigma>_step.map_comp0
    unfolding o_assoc unfolding map_prod_o_convol
    unfolding ext_step_\<Sigma>\<Sigma>_step_map[symmetric] A ..
  qed
  also have "... = ?R"
  proof(rule sym, rule ext_step_unique)
    show "ddd_step \<circ> flat_step \<circ> leaf_step = ddd_step" unfolding o_assoc[symmetric] flat_step_leaf_step o_id ..
  next
    show "ddd_step \<circ> flat_step \<circ> \<oo>\<pp>_step = <\<oo>\<pp>_step \<circ> \<Sigma>_step_map fst , F_map flat_step \<circ> \<Lambda>_step> \<circ> \<Sigma>_step_map (ddd_step \<circ> flat_step)"
    unfolding ddd_step_def unfolding o_assoc[symmetric] unfolding flat_step_commute[symmetric]
    unfolding o_assoc unfolding ext_step_commute \<Sigma>_step.map_comp0 unfolding o_assoc ..
  qed
  finally show ?thesis .
qed

theorem dd_step_flat_step: "F_map flat_step \<circ> dd_step \<circ> \<Sigma>\<Sigma>_step_map <\<Sigma>\<Sigma>_step_map fst, dd_step> = dd_step o flat_step"
proof-
  have A: "snd o ((flat_step ** F_map flat_step) \<circ> ddd_step \<circ> \<Sigma>\<Sigma>_step_map ddd_step) = snd o (ddd_step o flat_step)"
  unfolding ddd_step_flat_step ..
  have B: "ddd_step = <\<Sigma>\<Sigma>_step_map fst , snd \<circ> ddd_step>" apply(rule fst_snd_cong)
  unfolding fst_ddd_step by auto
  show ?thesis unfolding dd_step_def
  unfolding A[symmetric, unfolded o_assoc snd_comp_map_prod] o_assoc B[symmetric] ..
qed

(* The next two theorems are not necessary for the development.
They show that the conditions dd_step_leaf_step and dd_step_flat_step imply the
more standard conditions for the distributive law dd_step' = <\<Sigma>\<Sigma>_step_map fst, dd_step>
for the functors \<Sigma>\<Sigma>_step and 'a F' = 'a \<times> 'a F_ In fact, they can be shown
equivalent to these. *)

lemma dd_step_leaf_step2: "<\<Sigma>\<Sigma>_step_map fst, dd_step> o leaf_step = leaf_step ** F_map leaf_step"
apply (rule fst_snd_cong) unfolding o_assoc by (simp_all add: leaf_step_natural dd_step_leaf_step)

lemma ddd_step_leaf_step: "ddd_step \<circ> leaf_step = leaf_step ** F_map leaf_step"
unfolding ddd_step_def ext_step_comp_leaf_step ..

lemma ddd_step_\<oo>\<pp>_step: "ddd_step \<circ> \<oo>\<pp>_step = <\<oo>\<pp>_step \<circ> \<Sigma>_step_map fst , F_map flat_step \<circ> \<Lambda>_step> \<circ> \<Sigma>_step_map ddd_step"
unfolding ddd_step_def ext_step_commute ..


(* More customization *)

(* TODO Jasmin: Add_step this high-level induction for the relator of datatypes:
(similarly, coinduction for codatatypes): *)
lemma \<Sigma>\<Sigma>_step_rel_induct_pointfree:
assumes leaf_step: "\<And> x1 x2. R x1 x2 \<Longrightarrow> phi (leaf_step x1) (leaf_step x2)"
and \<oo>\<pp>_step: "\<And> y1 y2. \<lbrakk>\<Sigma>_step_rel (\<Sigma>\<Sigma>_step_rel R) y1 y2; \<Sigma>_step_rel phi y1 y2\<rbrakk> \<Longrightarrow> phi (\<oo>\<pp>_step y1) (\<oo>\<pp>_step y2)"
shows "\<Sigma>\<Sigma>_step_rel R \<le> phi"
proof-
  have "\<Sigma>\<Sigma>_step_rel R \<le> phi \<sqinter> \<Sigma>\<Sigma>_step_rel R"
  apply(induct rule: \<Sigma>\<Sigma>_step.ctor_rel_induct)
  using assms \<Sigma>\<Sigma>_step.rel_inject[of R] unfolding rel_pre_\<Sigma>\<Sigma>_step_def \<Sigma>\<Sigma>_step.leaf_step_def \<Sigma>\<Sigma>_step.\<oo>\<pp>_step_def
  using inf_greatest[OF \<Sigma>_step.rel_mono[OF inf_le1] \<Sigma>_step.rel_mono[OF inf_le2]]
  unfolding rel_sum_def BNF_Comp.id_bnf_comp_def vimage2p_def by (auto split: sum.splits) blast+
  thus ?thesis by simp
qed

lemma \<Sigma>\<Sigma>_step_rel_induct[case_names leaf_step \<oo>\<pp>_step]:
assumes leaf_step: "\<And> x1 x2. R x1 x2 \<Longrightarrow> phi (leaf_step x1) (leaf_step x2)"
and \<oo>\<pp>_step: "\<And> y1 y2. \<lbrakk>\<Sigma>_step_rel (\<Sigma>\<Sigma>_step_rel R) y1 y2; \<Sigma>_step_rel phi y1 y2\<rbrakk> \<Longrightarrow> phi (\<oo>\<pp>_step y1) (\<oo>\<pp>_step y2)"
shows "\<Sigma>\<Sigma>_step_rel R t1 t2 \<longrightarrow> phi t1 t2"
using \<Sigma>\<Sigma>_step_rel_induct_pointfree[of R, OF assms] by auto
(* end TODO *)

end