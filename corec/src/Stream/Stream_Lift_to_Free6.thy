header {* Lifting of the distributive law to the free algebra *}


(* This is silimar to Lift_to_Free, but uses \<Lambda>6, \<Sigma>\<Sigma>6, dd6, SpK instead of S, etc. *)

theory Stream_Lift_to_Free6
imports Stream_Distributive_Law6
begin

subsection{* The lifting *}

(* Our aim is lift \<Lambda>6 to an (SpK,SpK,T)-distributive law dd6 compatible with the monadic structure. *)

(* In order to be able to define dd6, we need a larger codomain type: *)
definition ddd6 :: "('a \<times> 'a F) \<Sigma>\<Sigma>6 \<Rightarrow> 'a \<Sigma>\<Sigma>6 \<times> 'a \<Sigma>\<Sigma>6 F" where
"ddd6 = ext6 <\<oo>\<pp>6 o \<Sigma>6_map fst, F_map flat6 o \<Lambda>6> (leaf6 ** F_map leaf6)"

definition dd6 :: "('a \<times> 'a F) \<Sigma>\<Sigma>6 \<Rightarrow> 'a \<Sigma>\<Sigma>6 F" where
"dd6 = snd o ddd6"

lemma ddd6_transfer[transfer_rule]:
  "(\<Sigma>\<Sigma>6_rel (rel_prod R (F_rel R)) ===> rel_prod (\<Sigma>\<Sigma>6_rel R) (F_rel (\<Sigma>\<Sigma>6_rel R))) ddd6 ddd6"
  unfolding ddd6_def ext6_alt by transfer_prover

lemma dd6_transfer[transfer_rule]:
  "(\<Sigma>\<Sigma>6_rel (rel_prod R (F_rel R)) ===> F_rel (\<Sigma>\<Sigma>6_rel R)) dd6 dd6"
  unfolding dd6_def by transfer_prover

lemma F_rel_\<Sigma>\<Sigma>6_rel: "\<Sigma>\<Sigma>6_rel (rel_prod R (F_rel R)) x y \<Longrightarrow> F_rel (\<Sigma>\<Sigma>6_rel R) (dd6 x) (dd6 y)"
  by (erule rel_funD[OF dd6_transfer])

(* We verify the facts for dd6: *)
theorem dd6_leaf6: "dd6 o leaf6 = F_map leaf6 o snd"
unfolding dd6_def ddd6_def o_assoc[symmetric] ext6_comp_leaf6 snd_comp_map_prod ..

lemma ddd6_natural: "ddd6 o \<Sigma>\<Sigma>6_map (f ** F_map f) = (\<Sigma>\<Sigma>6_map f ** F_map (\<Sigma>\<Sigma>6_map f)) o ddd6"
  using ddd6_transfer[of "BNF_Def.Grp UNIV f"]
  unfolding F_rel_Grp prod.rel_Grp \<Sigma>\<Sigma>6.rel_Grp
  unfolding Grp_def rel_fun_def by auto

theorem dd6_natural: "dd6 o \<Sigma>\<Sigma>6_map (f ** F_map f) = F_map (\<Sigma>\<Sigma>6_map f) o dd6"
  using dd6_transfer[of "BNF_Def.Grp UNIV f"]
  unfolding F_rel_Grp prod.rel_Grp \<Sigma>\<Sigma>6.rel_Grp
  unfolding Grp_def rel_fun_def by auto

lemma \<Lambda>6_dd6: "\<Lambda>6 = dd6 o \<oo>\<pp>6 o \<Sigma>6_map leaf6"
  unfolding dd6_def ddd6_def o_assoc[symmetric] \<Sigma>6.map_comp0[symmetric] ext6_commute
  unfolding o_assoc snd_convol ext6_comp_leaf6
  unfolding o_assoc[symmetric] \<Lambda>6_natural
  unfolding o_assoc F_map_comp[symmetric] leaf6_flat6 F_map_id id_o
  ..

lemma fst_ddd6: "fst o ddd6 = \<Sigma>\<Sigma>6_map fst"
proof-
  have "fst o ddd6 = ext6 \<oo>\<pp>6 (leaf6 o fst)"
  apply(rule ext6_unique) unfolding ddd6_def o_assoc[symmetric] ext6_comp_leaf6 ext6_commute
  unfolding o_assoc fst_comp_map_prod fst_convol
  unfolding o_assoc[symmetric] \<Sigma>6.map_comp0 by(rule refl, rule refl)
  also have "... = \<Sigma>\<Sigma>6_map fst"
  apply(rule sym, rule ext6_unique)
  unfolding leaf6_natural \<oo>\<pp>6_natural by(rule refl, rule refl)
  finally show ?thesis .
qed

lemma ddd6_flat6: "(flat6 ** F_map flat6) \<circ> ddd6 \<circ> \<Sigma>\<Sigma>6_map ddd6 = ddd6 o flat6" (is "?L = ?R")
proof-
  have "?L = ext6 <\<oo>\<pp>6 o \<Sigma>6_map fst, F_map flat6 o \<Lambda>6> ddd6"
  proof(rule ext6_unique)
    show "(flat6 ** F_map flat6) \<circ> ddd6 \<circ> \<Sigma>\<Sigma>6_map ddd6 \<circ> leaf6 = ddd6"
    unfolding ddd6_def unfolding o_assoc[symmetric] leaf6_natural
    unfolding o_assoc
    apply(subst o_assoc[symmetric]) unfolding ext6_comp_leaf6
    unfolding map_prod.comp F_map_comp[symmetric] flat6_leaf6 F_map_id map_prod.id id_o ..
  next
    have A: "<flat6 \<circ> (\<oo>\<pp>6 \<circ> \<Sigma>6_map fst) , F_map flat6 \<circ> (F_map flat6 \<circ> \<Lambda>6)>  =
             <\<oo>\<pp>6 \<circ> \<Sigma>6_map fst , F_map flat6 \<circ> \<Lambda>6> \<circ> \<Sigma>6_map (flat6 ** F_map flat6)"
    unfolding o_assoc unfolding flat6_commute[symmetric]
    apply(rule fst_snd_cong) unfolding o_assoc fst_convol snd_convol
    unfolding o_assoc[symmetric] \<Sigma>6.map_comp0[symmetric] fst_comp_map_prod snd_comp_map_prod
    unfolding \<Lambda>6_natural unfolding o_assoc F_map_comp[symmetric] flat6_assoc by(rule refl, rule refl)
    show "(flat6 ** F_map flat6) \<circ> ddd6 \<circ> \<Sigma>\<Sigma>6_map ddd6 \<circ> \<oo>\<pp>6 =
          <\<oo>\<pp>6 \<circ> \<Sigma>6_map fst , F_map flat6 \<circ> \<Lambda>6> \<circ> \<Sigma>6_map (flat6 ** F_map flat6 \<circ> ddd6 \<circ> \<Sigma>\<Sigma>6_map ddd6)"
    unfolding ddd6_def unfolding o_assoc[symmetric] unfolding \<oo>\<pp>6_natural[symmetric]
    unfolding o_assoc
    apply(subst o_assoc[symmetric]) unfolding ext6_commute
    unfolding o_assoc[symmetric] \<Sigma>6.map_comp0[symmetric]
    unfolding \<Sigma>6.map_comp0
    unfolding o_assoc unfolding map_prod_o_convol
    unfolding ext6_\<Sigma>\<Sigma>6_map[symmetric] A ..
  qed
  also have "... = ?R"
  proof(rule sym, rule ext6_unique)
    show "ddd6 \<circ> flat6 \<circ> leaf6 = ddd6" unfolding o_assoc[symmetric] flat6_leaf6 o_id ..
  next
    show "ddd6 \<circ> flat6 \<circ> \<oo>\<pp>6 = <\<oo>\<pp>6 \<circ> \<Sigma>6_map fst , F_map flat6 \<circ> \<Lambda>6> \<circ> \<Sigma>6_map (ddd6 \<circ> flat6)"
    unfolding ddd6_def unfolding o_assoc[symmetric] unfolding flat6_commute[symmetric]
    unfolding o_assoc unfolding ext6_commute \<Sigma>6.map_comp0 unfolding o_assoc ..
  qed
  finally show ?thesis .
qed

theorem dd6_flat6: "F_map flat6 \<circ> dd6 \<circ> \<Sigma>\<Sigma>6_map <\<Sigma>\<Sigma>6_map fst, dd6> = dd6 o flat6"
proof-
  have A: "snd o ((flat6 ** F_map flat6) \<circ> ddd6 \<circ> \<Sigma>\<Sigma>6_map ddd6) = snd o (ddd6 o flat6)"
  unfolding ddd6_flat6 ..
  have B: "ddd6 = <\<Sigma>\<Sigma>6_map fst , snd \<circ> ddd6>" apply(rule fst_snd_cong)
  unfolding fst_ddd6 by auto
  show ?thesis unfolding dd6_def
  unfolding A[symmetric, unfolded o_assoc snd_comp_map_prod] o_assoc B[symmetric] ..
qed

(* The next two theorems are not necessary for the development.
They show that the conditions dd6_leaf6 and dd6_flat6 imply the
more standard conditions for the distributive law dd6' = <\<Sigma>\<Sigma>6_map fst, dd6>
for the functors \<Sigma>\<Sigma>6 and 'a F' = 'a \<times> 'a F_ In fact, they can be shown
equivalent to these. *)

lemma dd6_leaf62: "<\<Sigma>\<Sigma>6_map fst, dd6> o leaf6 = leaf6 ** F_map leaf6"
apply (rule fst_snd_cong) unfolding o_assoc by (simp_all add: leaf6_natural dd6_leaf6)

lemma ddd6_leaf6: "ddd6 \<circ> leaf6 = leaf6 ** F_map leaf6"
unfolding ddd6_def ext6_comp_leaf6 ..

lemma ddd6_\<oo>\<pp>6: "ddd6 \<circ> \<oo>\<pp>6 = <\<oo>\<pp>6 \<circ> \<Sigma>6_map fst , F_map flat6 \<circ> \<Lambda>6> \<circ> \<Sigma>6_map ddd6"
unfolding ddd6_def ext6_commute ..


(* More customization *)

(* TODO Jasmin: Add6 this high-level induction for the relator of datatypes:
(similarly, coinduction for codatatypes): *)
lemma \<Sigma>\<Sigma>6_rel_induct_pointfree:
assumes leaf6: "\<And> x1 x2. R x1 x2 \<Longrightarrow> phi (leaf6 x1) (leaf6 x2)"
and \<oo>\<pp>6: "\<And> y1 y2. \<lbrakk>\<Sigma>6_rel (\<Sigma>\<Sigma>6_rel R) y1 y2; \<Sigma>6_rel phi y1 y2\<rbrakk> \<Longrightarrow> phi (\<oo>\<pp>6 y1) (\<oo>\<pp>6 y2)"
shows "\<Sigma>\<Sigma>6_rel R \<le> phi"
proof-
  have "\<Sigma>\<Sigma>6_rel R \<le> phi \<sqinter> \<Sigma>\<Sigma>6_rel R"
  apply(induct rule: \<Sigma>\<Sigma>6.ctor_rel_induct)
  using assms \<Sigma>\<Sigma>6.rel_inject[of R] unfolding rel_pre_\<Sigma>\<Sigma>6_def \<Sigma>\<Sigma>6.leaf6_def \<Sigma>\<Sigma>6.\<oo>\<pp>6_def
  using inf_greatest[OF \<Sigma>6.rel_mono[OF inf_le1] \<Sigma>6.rel_mono[OF inf_le2]]
  unfolding rel_sum_def BNF_Comp.id_bnf_comp_def vimage2p_def by (auto split: sum.splits) blast+
  thus ?thesis by simp
qed

lemma \<Sigma>\<Sigma>6_rel_induct[case_names leaf6 \<oo>\<pp>6]:
assumes leaf6: "\<And> x1 x2. R x1 x2 \<Longrightarrow> phi (leaf6 x1) (leaf6 x2)"
and \<oo>\<pp>6: "\<And> y1 y2. \<lbrakk>\<Sigma>6_rel (\<Sigma>\<Sigma>6_rel R) y1 y2; \<Sigma>6_rel phi y1 y2\<rbrakk> \<Longrightarrow> phi (\<oo>\<pp>6 y1) (\<oo>\<pp>6 y2)"
shows "\<Sigma>\<Sigma>6_rel R t1 t2 \<longrightarrow> phi t1 t2"
using \<Sigma>\<Sigma>6_rel_induct_pointfree[of R, OF assms] by auto
(* end TODO *)

end