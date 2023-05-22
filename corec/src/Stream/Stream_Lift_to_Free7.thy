header {* Lifting of the distributive law to the free algebra *}


(* This is silimar to Lift_to_Free, but uses \<Lambda>7, \<Sigma>\<Sigma>7, dd7, SpK instead of S, etc. *)

theory Stream_Lift_to_Free7
imports Stream_Distributive_Law7
begin

subsection{* The lifting *}

(* Our aim is lift \<Lambda>7 to an (SpK,SpK,T)-distributive law dd7 compatible with the monadic structure. *)

(* In order to be able to define dd7, we need a larger codomain type: *)
definition ddd7 :: "('a \<times> 'a F) \<Sigma>\<Sigma>7 \<Rightarrow> 'a \<Sigma>\<Sigma>7 \<times> 'a \<Sigma>\<Sigma>7 F" where
"ddd7 = ext7 <\<oo>\<pp>7 o \<Sigma>7_map fst, F_map flat7 o \<Lambda>7> (leaf7 ** F_map leaf7)"

definition dd7 :: "('a \<times> 'a F) \<Sigma>\<Sigma>7 \<Rightarrow> 'a \<Sigma>\<Sigma>7 F" where
"dd7 = snd o ddd7"

lemma ddd7_transfer[transfer_rule]:
  "(\<Sigma>\<Sigma>7_rel (rel_prod R (F_rel R)) ===> rel_prod (\<Sigma>\<Sigma>7_rel R) (F_rel (\<Sigma>\<Sigma>7_rel R))) ddd7 ddd7"
  unfolding ddd7_def ext7_alt by transfer_prover

lemma dd7_transfer[transfer_rule]:
  "(\<Sigma>\<Sigma>7_rel (rel_prod R (F_rel R)) ===> F_rel (\<Sigma>\<Sigma>7_rel R)) dd7 dd7"
  unfolding dd7_def by transfer_prover

lemma F_rel_\<Sigma>\<Sigma>7_rel: "\<Sigma>\<Sigma>7_rel (rel_prod R (F_rel R)) x y \<Longrightarrow> F_rel (\<Sigma>\<Sigma>7_rel R) (dd7 x) (dd7 y)"
  by (erule rel_funD[OF dd7_transfer])

(* We verify the facts for dd7: *)
theorem dd7_leaf7: "dd7 o leaf7 = F_map leaf7 o snd"
unfolding dd7_def ddd7_def o_assoc[symmetric] ext7_comp_leaf7 snd_comp_map_prod ..

lemma ddd7_natural: "ddd7 o \<Sigma>\<Sigma>7_map (f ** F_map f) = (\<Sigma>\<Sigma>7_map f ** F_map (\<Sigma>\<Sigma>7_map f)) o ddd7"
  using ddd7_transfer[of "BNF_Def.Grp UNIV f"]
  unfolding F_rel_Grp prod.rel_Grp \<Sigma>\<Sigma>7.rel_Grp
  unfolding Grp_def rel_fun_def by auto

theorem dd7_natural: "dd7 o \<Sigma>\<Sigma>7_map (f ** F_map f) = F_map (\<Sigma>\<Sigma>7_map f) o dd7"
  using dd7_transfer[of "BNF_Def.Grp UNIV f"]
  unfolding F_rel_Grp prod.rel_Grp \<Sigma>\<Sigma>7.rel_Grp
  unfolding Grp_def rel_fun_def by auto

lemma \<Lambda>7_dd7: "\<Lambda>7 = dd7 o \<oo>\<pp>7 o \<Sigma>7_map leaf7"
  unfolding dd7_def ddd7_def o_assoc[symmetric] \<Sigma>7.map_comp0[symmetric] ext7_commute
  unfolding o_assoc snd_convol ext7_comp_leaf7
  unfolding o_assoc[symmetric] \<Lambda>7_natural
  unfolding o_assoc F_map_comp[symmetric] leaf7_flat7 F_map_id id_o
  ..

lemma fst_ddd7: "fst o ddd7 = \<Sigma>\<Sigma>7_map fst"
proof-
  have "fst o ddd7 = ext7 \<oo>\<pp>7 (leaf7 o fst)"
  apply(rule ext7_unique) unfolding ddd7_def o_assoc[symmetric] ext7_comp_leaf7 ext7_commute
  unfolding o_assoc fst_comp_map_prod fst_convol
  unfolding o_assoc[symmetric] \<Sigma>7.map_comp0 by(rule refl, rule refl)
  also have "... = \<Sigma>\<Sigma>7_map fst"
  apply(rule sym, rule ext7_unique)
  unfolding leaf7_natural \<oo>\<pp>7_natural by(rule refl, rule refl)
  finally show ?thesis .
qed

lemma ddd7_flat7: "(flat7 ** F_map flat7) \<circ> ddd7 \<circ> \<Sigma>\<Sigma>7_map ddd7 = ddd7 o flat7" (is "?L = ?R")
proof-
  have "?L = ext7 <\<oo>\<pp>7 o \<Sigma>7_map fst, F_map flat7 o \<Lambda>7> ddd7"
  proof(rule ext7_unique)
    show "(flat7 ** F_map flat7) \<circ> ddd7 \<circ> \<Sigma>\<Sigma>7_map ddd7 \<circ> leaf7 = ddd7"
    unfolding ddd7_def unfolding o_assoc[symmetric] leaf7_natural
    unfolding o_assoc
    apply(subst o_assoc[symmetric]) unfolding ext7_comp_leaf7
    unfolding map_prod.comp F_map_comp[symmetric] flat7_leaf7 F_map_id map_prod.id id_o ..
  next
    have A: "<flat7 \<circ> (\<oo>\<pp>7 \<circ> \<Sigma>7_map fst) , F_map flat7 \<circ> (F_map flat7 \<circ> \<Lambda>7)>  =
             <\<oo>\<pp>7 \<circ> \<Sigma>7_map fst , F_map flat7 \<circ> \<Lambda>7> \<circ> \<Sigma>7_map (flat7 ** F_map flat7)"
    unfolding o_assoc unfolding flat7_commute[symmetric]
    apply(rule fst_snd_cong) unfolding o_assoc fst_convol snd_convol
    unfolding o_assoc[symmetric] \<Sigma>7.map_comp0[symmetric] fst_comp_map_prod snd_comp_map_prod
    unfolding \<Lambda>7_natural unfolding o_assoc F_map_comp[symmetric] flat7_assoc by(rule refl, rule refl)
    show "(flat7 ** F_map flat7) \<circ> ddd7 \<circ> \<Sigma>\<Sigma>7_map ddd7 \<circ> \<oo>\<pp>7 =
          <\<oo>\<pp>7 \<circ> \<Sigma>7_map fst , F_map flat7 \<circ> \<Lambda>7> \<circ> \<Sigma>7_map (flat7 ** F_map flat7 \<circ> ddd7 \<circ> \<Sigma>\<Sigma>7_map ddd7)"
    unfolding ddd7_def unfolding o_assoc[symmetric] unfolding \<oo>\<pp>7_natural[symmetric]
    unfolding o_assoc
    apply(subst o_assoc[symmetric]) unfolding ext7_commute
    unfolding o_assoc[symmetric] \<Sigma>7.map_comp0[symmetric]
    unfolding \<Sigma>7.map_comp0
    unfolding o_assoc unfolding map_prod_o_convol
    unfolding ext7_\<Sigma>\<Sigma>7_map[symmetric] A ..
  qed
  also have "... = ?R"
  proof(rule sym, rule ext7_unique)
    show "ddd7 \<circ> flat7 \<circ> leaf7 = ddd7" unfolding o_assoc[symmetric] flat7_leaf7 o_id ..
  next
    show "ddd7 \<circ> flat7 \<circ> \<oo>\<pp>7 = <\<oo>\<pp>7 \<circ> \<Sigma>7_map fst , F_map flat7 \<circ> \<Lambda>7> \<circ> \<Sigma>7_map (ddd7 \<circ> flat7)"
    unfolding ddd7_def unfolding o_assoc[symmetric] unfolding flat7_commute[symmetric]
    unfolding o_assoc unfolding ext7_commute \<Sigma>7.map_comp0 unfolding o_assoc ..
  qed
  finally show ?thesis .
qed

theorem dd7_flat7: "F_map flat7 \<circ> dd7 \<circ> \<Sigma>\<Sigma>7_map <\<Sigma>\<Sigma>7_map fst, dd7> = dd7 o flat7"
proof-
  have A: "snd o ((flat7 ** F_map flat7) \<circ> ddd7 \<circ> \<Sigma>\<Sigma>7_map ddd7) = snd o (ddd7 o flat7)"
  unfolding ddd7_flat7 ..
  have B: "ddd7 = <\<Sigma>\<Sigma>7_map fst , snd \<circ> ddd7>" apply(rule fst_snd_cong)
  unfolding fst_ddd7 by auto
  show ?thesis unfolding dd7_def
  unfolding A[symmetric, unfolded o_assoc snd_comp_map_prod] o_assoc B[symmetric] ..
qed

(* The next two theorems are not necessary for the development.
They show that the conditions dd7_leaf7 and dd7_flat7 imply the
more standard conditions for the distributive law dd7' = <\<Sigma>\<Sigma>7_map fst, dd7>
for the functors \<Sigma>\<Sigma>7 and 'a F' = 'a \<times> 'a F_ In fact, they can be shown
equivalent to these. *)

lemma dd7_leaf72: "<\<Sigma>\<Sigma>7_map fst, dd7> o leaf7 = leaf7 ** F_map leaf7"
apply (rule fst_snd_cong) unfolding o_assoc by (simp_all add: leaf7_natural dd7_leaf7)

lemma ddd7_leaf7: "ddd7 \<circ> leaf7 = leaf7 ** F_map leaf7"
unfolding ddd7_def ext7_comp_leaf7 ..

lemma ddd7_\<oo>\<pp>7: "ddd7 \<circ> \<oo>\<pp>7 = <\<oo>\<pp>7 \<circ> \<Sigma>7_map fst , F_map flat7 \<circ> \<Lambda>7> \<circ> \<Sigma>7_map ddd7"
unfolding ddd7_def ext7_commute ..


(* More customization *)

(* TODO Jasmin: Add7 this high-level induction for the relator of datatypes:
(similarly, coinduction for codatatypes): *)
lemma \<Sigma>\<Sigma>7_rel_induct_pointfree:
assumes leaf7: "\<And> x1 x2. R x1 x2 \<Longrightarrow> phi (leaf7 x1) (leaf7 x2)"
and \<oo>\<pp>7: "\<And> y1 y2. \<lbrakk>\<Sigma>7_rel (\<Sigma>\<Sigma>7_rel R) y1 y2; \<Sigma>7_rel phi y1 y2\<rbrakk> \<Longrightarrow> phi (\<oo>\<pp>7 y1) (\<oo>\<pp>7 y2)"
shows "\<Sigma>\<Sigma>7_rel R \<le> phi"
proof-
  have "\<Sigma>\<Sigma>7_rel R \<le> phi \<sqinter> \<Sigma>\<Sigma>7_rel R"
  apply(induct rule: \<Sigma>\<Sigma>7.ctor_rel_induct)
  using assms \<Sigma>\<Sigma>7.rel_inject[of R] unfolding rel_pre_\<Sigma>\<Sigma>7_def \<Sigma>\<Sigma>7.leaf7_def \<Sigma>\<Sigma>7.\<oo>\<pp>7_def
  using inf_greatest[OF \<Sigma>7.rel_mono[OF inf_le1] \<Sigma>7.rel_mono[OF inf_le2]]
  unfolding rel_sum_def BNF_Comp.id_bnf_comp_def vimage2p_def by (auto split: sum.splits) blast+
  thus ?thesis by simp
qed

lemma \<Sigma>\<Sigma>7_rel_induct[case_names leaf7 \<oo>\<pp>7]:
assumes leaf7: "\<And> x1 x2. R x1 x2 \<Longrightarrow> phi (leaf7 x1) (leaf7 x2)"
and \<oo>\<pp>7: "\<And> y1 y2. \<lbrakk>\<Sigma>7_rel (\<Sigma>\<Sigma>7_rel R) y1 y2; \<Sigma>7_rel phi y1 y2\<rbrakk> \<Longrightarrow> phi (\<oo>\<pp>7 y1) (\<oo>\<pp>7 y2)"
shows "\<Sigma>\<Sigma>7_rel R t1 t2 \<longrightarrow> phi t1 t2"
using \<Sigma>\<Sigma>7_rel_induct_pointfree[of R, OF assms] by auto
(* end TODO *)

end