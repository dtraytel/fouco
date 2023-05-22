header {* Lifting of the distributive law to the free algebra *}


(* This is silimar to Lift_to_Free, but uses \<Lambda>8, \<Sigma>\<Sigma>8, dd8, SpK instead of S, etc. *)

theory Stream_Lift_to_Free8
imports Stream_Distributive_Law8
begin

subsection{* The lifting *}

(* Our aim is lift \<Lambda>8 to an (SpK,SpK,T)-distributive law dd8 compatible with the monadic structure. *)

(* In order to be able to define dd8, we need a larger codomain type: *)
definition ddd8 :: "('a \<times> 'a F) \<Sigma>\<Sigma>8 \<Rightarrow> 'a \<Sigma>\<Sigma>8 \<times> 'a \<Sigma>\<Sigma>8 F" where
"ddd8 = ext8 <\<oo>\<pp>8 o \<Sigma>8_map fst, F_map flat8 o \<Lambda>8> (leaf8 ** F_map leaf8)"

definition dd8 :: "('a \<times> 'a F) \<Sigma>\<Sigma>8 \<Rightarrow> 'a \<Sigma>\<Sigma>8 F" where
"dd8 = snd o ddd8"

lemma ddd8_transfer[transfer_rule]:
  "(\<Sigma>\<Sigma>8_rel (rel_prod R (F_rel R)) ===> rel_prod (\<Sigma>\<Sigma>8_rel R) (F_rel (\<Sigma>\<Sigma>8_rel R))) ddd8 ddd8"
  unfolding ddd8_def ext8_alt by transfer_prover

lemma dd8_transfer[transfer_rule]:
  "(\<Sigma>\<Sigma>8_rel (rel_prod R (F_rel R)) ===> F_rel (\<Sigma>\<Sigma>8_rel R)) dd8 dd8"
  unfolding dd8_def by transfer_prover

lemma F_rel_\<Sigma>\<Sigma>8_rel: "\<Sigma>\<Sigma>8_rel (rel_prod R (F_rel R)) x y \<Longrightarrow> F_rel (\<Sigma>\<Sigma>8_rel R) (dd8 x) (dd8 y)"
  by (erule rel_funD[OF dd8_transfer])

(* We verify the facts for dd8: *)
theorem dd8_leaf8: "dd8 o leaf8 = F_map leaf8 o snd"
unfolding dd8_def ddd8_def o_assoc[symmetric] ext8_comp_leaf8 snd_comp_map_prod ..

lemma ddd8_natural: "ddd8 o \<Sigma>\<Sigma>8_map (f ** F_map f) = (\<Sigma>\<Sigma>8_map f ** F_map (\<Sigma>\<Sigma>8_map f)) o ddd8"
  using ddd8_transfer[of "BNF_Def.Grp UNIV f"]
  unfolding F_rel_Grp prod.rel_Grp \<Sigma>\<Sigma>8.rel_Grp
  unfolding Grp_def rel_fun_def by auto

theorem dd8_natural: "dd8 o \<Sigma>\<Sigma>8_map (f ** F_map f) = F_map (\<Sigma>\<Sigma>8_map f) o dd8"
  using dd8_transfer[of "BNF_Def.Grp UNIV f"]
  unfolding F_rel_Grp prod.rel_Grp \<Sigma>\<Sigma>8.rel_Grp
  unfolding Grp_def rel_fun_def by auto

lemma \<Lambda>8_dd8: "\<Lambda>8 = dd8 o \<oo>\<pp>8 o \<Sigma>8_map leaf8"
  unfolding dd8_def ddd8_def o_assoc[symmetric] \<Sigma>8.map_comp0[symmetric] ext8_commute
  unfolding o_assoc snd_convol ext8_comp_leaf8
  unfolding o_assoc[symmetric] \<Lambda>8_natural
  unfolding o_assoc F_map_comp[symmetric] leaf8_flat8 F_map_id id_o
  ..

lemma fst_ddd8: "fst o ddd8 = \<Sigma>\<Sigma>8_map fst"
proof-
  have "fst o ddd8 = ext8 \<oo>\<pp>8 (leaf8 o fst)"
  apply(rule ext8_unique) unfolding ddd8_def o_assoc[symmetric] ext8_comp_leaf8 ext8_commute
  unfolding o_assoc fst_comp_map_prod fst_convol
  unfolding o_assoc[symmetric] \<Sigma>8.map_comp0 by(rule refl, rule refl)
  also have "... = \<Sigma>\<Sigma>8_map fst"
  apply(rule sym, rule ext8_unique)
  unfolding leaf8_natural \<oo>\<pp>8_natural by(rule refl, rule refl)
  finally show ?thesis .
qed

lemma ddd8_flat8: "(flat8 ** F_map flat8) \<circ> ddd8 \<circ> \<Sigma>\<Sigma>8_map ddd8 = ddd8 o flat8" (is "?L = ?R")
proof-
  have "?L = ext8 <\<oo>\<pp>8 o \<Sigma>8_map fst, F_map flat8 o \<Lambda>8> ddd8"
  proof(rule ext8_unique)
    show "(flat8 ** F_map flat8) \<circ> ddd8 \<circ> \<Sigma>\<Sigma>8_map ddd8 \<circ> leaf8 = ddd8"
    unfolding ddd8_def unfolding o_assoc[symmetric] leaf8_natural
    unfolding o_assoc
    apply(subst o_assoc[symmetric]) unfolding ext8_comp_leaf8
    unfolding map_prod.comp F_map_comp[symmetric] flat8_leaf8 F_map_id map_prod.id id_o ..
  next
    have A: "<flat8 \<circ> (\<oo>\<pp>8 \<circ> \<Sigma>8_map fst) , F_map flat8 \<circ> (F_map flat8 \<circ> \<Lambda>8)>  =
             <\<oo>\<pp>8 \<circ> \<Sigma>8_map fst , F_map flat8 \<circ> \<Lambda>8> \<circ> \<Sigma>8_map (flat8 ** F_map flat8)"
    unfolding o_assoc unfolding flat8_commute[symmetric]
    apply(rule fst_snd_cong) unfolding o_assoc fst_convol snd_convol
    unfolding o_assoc[symmetric] \<Sigma>8.map_comp0[symmetric] fst_comp_map_prod snd_comp_map_prod
    unfolding \<Lambda>8_natural unfolding o_assoc F_map_comp[symmetric] flat8_assoc by(rule refl, rule refl)
    show "(flat8 ** F_map flat8) \<circ> ddd8 \<circ> \<Sigma>\<Sigma>8_map ddd8 \<circ> \<oo>\<pp>8 =
          <\<oo>\<pp>8 \<circ> \<Sigma>8_map fst , F_map flat8 \<circ> \<Lambda>8> \<circ> \<Sigma>8_map (flat8 ** F_map flat8 \<circ> ddd8 \<circ> \<Sigma>\<Sigma>8_map ddd8)"
    unfolding ddd8_def unfolding o_assoc[symmetric] unfolding \<oo>\<pp>8_natural[symmetric]
    unfolding o_assoc
    apply(subst o_assoc[symmetric]) unfolding ext8_commute
    unfolding o_assoc[symmetric] \<Sigma>8.map_comp0[symmetric]
    unfolding \<Sigma>8.map_comp0
    unfolding o_assoc unfolding map_prod_o_convol
    unfolding ext8_\<Sigma>\<Sigma>8_map[symmetric] A ..
  qed
  also have "... = ?R"
  proof(rule sym, rule ext8_unique)
    show "ddd8 \<circ> flat8 \<circ> leaf8 = ddd8" unfolding o_assoc[symmetric] flat8_leaf8 o_id ..
  next
    show "ddd8 \<circ> flat8 \<circ> \<oo>\<pp>8 = <\<oo>\<pp>8 \<circ> \<Sigma>8_map fst , F_map flat8 \<circ> \<Lambda>8> \<circ> \<Sigma>8_map (ddd8 \<circ> flat8)"
    unfolding ddd8_def unfolding o_assoc[symmetric] unfolding flat8_commute[symmetric]
    unfolding o_assoc unfolding ext8_commute \<Sigma>8.map_comp0 unfolding o_assoc ..
  qed
  finally show ?thesis .
qed

theorem dd8_flat8: "F_map flat8 \<circ> dd8 \<circ> \<Sigma>\<Sigma>8_map <\<Sigma>\<Sigma>8_map fst, dd8> = dd8 o flat8"
proof-
  have A: "snd o ((flat8 ** F_map flat8) \<circ> ddd8 \<circ> \<Sigma>\<Sigma>8_map ddd8) = snd o (ddd8 o flat8)"
  unfolding ddd8_flat8 ..
  have B: "ddd8 = <\<Sigma>\<Sigma>8_map fst , snd \<circ> ddd8>" apply(rule fst_snd_cong)
  unfolding fst_ddd8 by auto
  show ?thesis unfolding dd8_def
  unfolding A[symmetric, unfolded o_assoc snd_comp_map_prod] o_assoc B[symmetric] ..
qed

(* The next two theorems are not necessary for the development.
They show that the conditions dd8_leaf8 and dd8_flat8 imply the
more standard conditions for the distributive law dd8' = <\<Sigma>\<Sigma>8_map fst, dd8>
for the functors \<Sigma>\<Sigma>8 and 'a F' = 'a \<times> 'a F_ In fact, they can be shown
equivalent to these. *)

lemma dd8_leaf82: "<\<Sigma>\<Sigma>8_map fst, dd8> o leaf8 = leaf8 ** F_map leaf8"
apply (rule fst_snd_cong) unfolding o_assoc by (simp_all add: leaf8_natural dd8_leaf8)

lemma ddd8_leaf8: "ddd8 \<circ> leaf8 = leaf8 ** F_map leaf8"
unfolding ddd8_def ext8_comp_leaf8 ..

lemma ddd8_\<oo>\<pp>8: "ddd8 \<circ> \<oo>\<pp>8 = <\<oo>\<pp>8 \<circ> \<Sigma>8_map fst , F_map flat8 \<circ> \<Lambda>8> \<circ> \<Sigma>8_map ddd8"
unfolding ddd8_def ext8_commute ..


(* More customization *)

(* TODO Jasmin: Add8 this high-level induction for the relator of datatypes:
(similarly, coinduction for codatatypes): *)
lemma \<Sigma>\<Sigma>8_rel_induct_pointfree:
assumes leaf8: "\<And> x1 x2. R x1 x2 \<Longrightarrow> phi (leaf8 x1) (leaf8 x2)"
and \<oo>\<pp>8: "\<And> y1 y2. \<lbrakk>\<Sigma>8_rel (\<Sigma>\<Sigma>8_rel R) y1 y2; \<Sigma>8_rel phi y1 y2\<rbrakk> \<Longrightarrow> phi (\<oo>\<pp>8 y1) (\<oo>\<pp>8 y2)"
shows "\<Sigma>\<Sigma>8_rel R \<le> phi"
proof-
  have "\<Sigma>\<Sigma>8_rel R \<le> phi \<sqinter> \<Sigma>\<Sigma>8_rel R"
  apply(induct rule: \<Sigma>\<Sigma>8.ctor_rel_induct)
  using assms \<Sigma>\<Sigma>8.rel_inject[of R] unfolding rel_pre_\<Sigma>\<Sigma>8_def \<Sigma>\<Sigma>8.leaf8_def \<Sigma>\<Sigma>8.\<oo>\<pp>8_def
  using inf_greatest[OF \<Sigma>8.rel_mono[OF inf_le1] \<Sigma>8.rel_mono[OF inf_le2]]
  unfolding rel_sum_def BNF_Comp.id_bnf_comp_def vimage2p_def by (auto split: sum.splits) blast+
  thus ?thesis by simp
qed

lemma \<Sigma>\<Sigma>8_rel_induct[case_names leaf8 \<oo>\<pp>8]:
assumes leaf8: "\<And> x1 x2. R x1 x2 \<Longrightarrow> phi (leaf8 x1) (leaf8 x2)"
and \<oo>\<pp>8: "\<And> y1 y2. \<lbrakk>\<Sigma>8_rel (\<Sigma>\<Sigma>8_rel R) y1 y2; \<Sigma>8_rel phi y1 y2\<rbrakk> \<Longrightarrow> phi (\<oo>\<pp>8 y1) (\<oo>\<pp>8 y2)"
shows "\<Sigma>\<Sigma>8_rel R t1 t2 \<longrightarrow> phi t1 t2"
using \<Sigma>\<Sigma>8_rel_induct_pointfree[of R, OF assms] by auto
(* end TODO *)

end