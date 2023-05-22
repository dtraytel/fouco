header {* Lifting of the distributive law to the free algebra *}


(* This is silimar to Lift_to_Free, but uses \<Lambda>1, \<Sigma>\<Sigma>1, dd1, SpK instead of S, etc. *)

theory Binary_Tree_Lift_to_Free1
imports Binary_Tree_Distributive_Law1
begin

subsection{* The lifting *}

(* Our aim is lift \<Lambda>1 to an (SpK,SpK,T)-distributive law dd1 compatible with the monadic structure. *)

(* In order to be able to define dd1, we need a larger codomain type: *)
definition ddd1 :: "('a \<times> 'a F) \<Sigma>\<Sigma>1 \<Rightarrow> 'a \<Sigma>\<Sigma>1 \<times> 'a \<Sigma>\<Sigma>1 F" where
"ddd1 = ext1 <\<oo>\<pp>1 o \<Sigma>1_map fst, F_map flat1 o \<Lambda>1> (leaf1 ** F_map leaf1)"

definition dd1 :: "('a \<times> 'a F) \<Sigma>\<Sigma>1 \<Rightarrow> 'a \<Sigma>\<Sigma>1 F" where
"dd1 = snd o ddd1"

lemma ddd1_transfer[transfer_rule]:
  "(\<Sigma>\<Sigma>1_rel (rel_prod R (F_rel R)) ===> rel_prod (\<Sigma>\<Sigma>1_rel R) (F_rel (\<Sigma>\<Sigma>1_rel R))) ddd1 ddd1"
  unfolding ddd1_def ext1_alt by transfer_prover

lemma dd1_transfer[transfer_rule]:
  "(\<Sigma>\<Sigma>1_rel (rel_prod R (F_rel R)) ===> F_rel (\<Sigma>\<Sigma>1_rel R)) dd1 dd1"
  unfolding dd1_def by transfer_prover

lemma F_rel_\<Sigma>\<Sigma>1_rel: "\<Sigma>\<Sigma>1_rel (rel_prod R (F_rel R)) x y \<Longrightarrow> F_rel (\<Sigma>\<Sigma>1_rel R) (dd1 x) (dd1 y)"
  by (erule rel_funD[OF dd1_transfer])

(* We verify the facts for dd1: *)
theorem dd1_leaf1: "dd1 o leaf1 = F_map leaf1 o snd"
unfolding dd1_def ddd1_def o_assoc[symmetric] ext1_comp_leaf1 snd_comp_map_prod ..

lemma ddd1_natural: "ddd1 o \<Sigma>\<Sigma>1_map (f ** F_map f) = (\<Sigma>\<Sigma>1_map f ** F_map (\<Sigma>\<Sigma>1_map f)) o ddd1"
  using ddd1_transfer[of "BNF_Def.Grp UNIV f"]
  unfolding F_rel_Grp prod.rel_Grp \<Sigma>\<Sigma>1.rel_Grp
  unfolding Grp_def rel_fun_def by auto

theorem dd1_natural: "dd1 o \<Sigma>\<Sigma>1_map (f ** F_map f) = F_map (\<Sigma>\<Sigma>1_map f) o dd1"
  using dd1_transfer[of "BNF_Def.Grp UNIV f"]
  unfolding F_rel_Grp prod.rel_Grp \<Sigma>\<Sigma>1.rel_Grp
  unfolding Grp_def rel_fun_def by auto

lemma \<Lambda>1_dd1: "\<Lambda>1 = dd1 o \<oo>\<pp>1 o \<Sigma>1_map leaf1"
  unfolding dd1_def ddd1_def o_assoc[symmetric] \<Sigma>1.map_comp0[symmetric] ext1_commute
  unfolding o_assoc snd_convol ext1_comp_leaf1
  unfolding o_assoc[symmetric] \<Lambda>1_natural
  unfolding o_assoc F_map_comp[symmetric] leaf1_flat1 F_map_id id_o
  ..

lemma fst_ddd1: "fst o ddd1 = \<Sigma>\<Sigma>1_map fst"
proof-
  have "fst o ddd1 = ext1 \<oo>\<pp>1 (leaf1 o fst)"
  apply(rule ext1_unique) unfolding ddd1_def o_assoc[symmetric] ext1_comp_leaf1 ext1_commute
  unfolding o_assoc fst_comp_map_prod fst_convol
  unfolding o_assoc[symmetric] \<Sigma>1.map_comp0 by(rule refl, rule refl)
  also have "... = \<Sigma>\<Sigma>1_map fst"
  apply(rule sym, rule ext1_unique)
  unfolding leaf1_natural \<oo>\<pp>1_natural by(rule refl, rule refl)
  finally show ?thesis .
qed

lemma ddd1_flat1: "(flat1 ** F_map flat1) \<circ> ddd1 \<circ> \<Sigma>\<Sigma>1_map ddd1 = ddd1 o flat1" (is "?L = ?R")
proof-
  have "?L = ext1 <\<oo>\<pp>1 o \<Sigma>1_map fst, F_map flat1 o \<Lambda>1> ddd1"
  proof(rule ext1_unique)
    show "(flat1 ** F_map flat1) \<circ> ddd1 \<circ> \<Sigma>\<Sigma>1_map ddd1 \<circ> leaf1 = ddd1"
    unfolding ddd1_def unfolding o_assoc[symmetric] leaf1_natural
    unfolding o_assoc
    apply(subst o_assoc[symmetric]) unfolding ext1_comp_leaf1
    unfolding map_prod.comp F_map_comp[symmetric] flat1_leaf1 F_map_id map_prod.id id_o ..
  next
    have A: "<flat1 \<circ> (\<oo>\<pp>1 \<circ> \<Sigma>1_map fst) , F_map flat1 \<circ> (F_map flat1 \<circ> \<Lambda>1)>  =
             <\<oo>\<pp>1 \<circ> \<Sigma>1_map fst , F_map flat1 \<circ> \<Lambda>1> \<circ> \<Sigma>1_map (flat1 ** F_map flat1)"
    unfolding o_assoc unfolding flat1_commute[symmetric]
    apply(rule fst_snd_cong) unfolding o_assoc fst_convol snd_convol
    unfolding o_assoc[symmetric] \<Sigma>1.map_comp0[symmetric] fst_comp_map_prod snd_comp_map_prod
    unfolding \<Lambda>1_natural unfolding o_assoc F_map_comp[symmetric] flat1_assoc by(rule refl, rule refl)
    show "(flat1 ** F_map flat1) \<circ> ddd1 \<circ> \<Sigma>\<Sigma>1_map ddd1 \<circ> \<oo>\<pp>1 =
          <\<oo>\<pp>1 \<circ> \<Sigma>1_map fst , F_map flat1 \<circ> \<Lambda>1> \<circ> \<Sigma>1_map (flat1 ** F_map flat1 \<circ> ddd1 \<circ> \<Sigma>\<Sigma>1_map ddd1)"
    unfolding ddd1_def unfolding o_assoc[symmetric] unfolding \<oo>\<pp>1_natural[symmetric]
    unfolding o_assoc
    apply(subst o_assoc[symmetric]) unfolding ext1_commute
    unfolding o_assoc[symmetric] \<Sigma>1.map_comp0[symmetric]
    unfolding \<Sigma>1.map_comp0
    unfolding o_assoc unfolding map_prod_o_convol
    unfolding ext1_\<Sigma>\<Sigma>1_map[symmetric] A ..
  qed
  also have "... = ?R"
  proof(rule sym, rule ext1_unique)
    show "ddd1 \<circ> flat1 \<circ> leaf1 = ddd1" unfolding o_assoc[symmetric] flat1_leaf1 o_id ..
  next
    show "ddd1 \<circ> flat1 \<circ> \<oo>\<pp>1 = <\<oo>\<pp>1 \<circ> \<Sigma>1_map fst , F_map flat1 \<circ> \<Lambda>1> \<circ> \<Sigma>1_map (ddd1 \<circ> flat1)"
    unfolding ddd1_def unfolding o_assoc[symmetric] unfolding flat1_commute[symmetric]
    unfolding o_assoc unfolding ext1_commute \<Sigma>1.map_comp0 unfolding o_assoc ..
  qed
  finally show ?thesis .
qed

theorem dd1_flat1: "F_map flat1 \<circ> dd1 \<circ> \<Sigma>\<Sigma>1_map <\<Sigma>\<Sigma>1_map fst, dd1> = dd1 o flat1"
proof-
  have A: "snd o ((flat1 ** F_map flat1) \<circ> ddd1 \<circ> \<Sigma>\<Sigma>1_map ddd1) = snd o (ddd1 o flat1)"
  unfolding ddd1_flat1 ..
  have B: "ddd1 = <\<Sigma>\<Sigma>1_map fst , snd \<circ> ddd1>" apply(rule fst_snd_cong)
  unfolding fst_ddd1 by auto
  show ?thesis unfolding dd1_def
  unfolding A[symmetric, unfolded o_assoc snd_comp_map_prod] o_assoc B[symmetric] ..
qed

(* The next two theorems are not necessary for the development.
They show that the conditions dd1_leaf1 and dd1_flat1 imply the
more standard conditions for the distributive law dd1' = <\<Sigma>\<Sigma>1_map fst, dd1>
for the functors \<Sigma>\<Sigma>1 and 'a F' = 'a \<times> 'a F_ In fact, they can be shown
equivalent to these. *)

lemma dd1_leaf12: "<\<Sigma>\<Sigma>1_map fst, dd1> o leaf1 = leaf1 ** F_map leaf1"
apply (rule fst_snd_cong) unfolding o_assoc by (simp_all add: leaf1_natural dd1_leaf1)

lemma ddd1_leaf1: "ddd1 \<circ> leaf1 = leaf1 ** F_map leaf1"
unfolding ddd1_def ext1_comp_leaf1 ..

lemma ddd1_\<oo>\<pp>1: "ddd1 \<circ> \<oo>\<pp>1 = <\<oo>\<pp>1 \<circ> \<Sigma>1_map fst , F_map flat1 \<circ> \<Lambda>1> \<circ> \<Sigma>1_map ddd1"
unfolding ddd1_def ext1_commute ..


(* More customization *)

(* TODO Jasmin: Add1 this high-level induction for the relator of datatypes:
(similarly, coinduction for codatatypes): *)
lemma \<Sigma>\<Sigma>1_rel_induct_pointfree:
assumes leaf1: "\<And> x1 x2. R x1 x2 \<Longrightarrow> phi (leaf1 x1) (leaf1 x2)"
and \<oo>\<pp>1: "\<And> y1 y2. \<lbrakk>\<Sigma>1_rel (\<Sigma>\<Sigma>1_rel R) y1 y2; \<Sigma>1_rel phi y1 y2\<rbrakk> \<Longrightarrow> phi (\<oo>\<pp>1 y1) (\<oo>\<pp>1 y2)"
shows "\<Sigma>\<Sigma>1_rel R \<le> phi"
proof-
  have "\<Sigma>\<Sigma>1_rel R \<le> phi \<sqinter> \<Sigma>\<Sigma>1_rel R"
  apply(induct rule: \<Sigma>\<Sigma>1.ctor_rel_induct)
  using assms \<Sigma>\<Sigma>1.rel_inject[of R] unfolding rel_pre_\<Sigma>\<Sigma>1_def \<Sigma>\<Sigma>1.leaf1_def \<Sigma>\<Sigma>1.\<oo>\<pp>1_def
  using inf_greatest[OF \<Sigma>1.rel_mono[OF inf_le1] \<Sigma>1.rel_mono[OF inf_le2]]
  unfolding rel_sum_def BNF_Comp.id_bnf_comp_def vimage2p_def by (auto split: sum.splits) blast+
  thus ?thesis by simp
qed

lemma \<Sigma>\<Sigma>1_rel_induct[case_names leaf1 \<oo>\<pp>1]:
assumes leaf1: "\<And> x1 x2. R x1 x2 \<Longrightarrow> phi (leaf1 x1) (leaf1 x2)"
and \<oo>\<pp>1: "\<And> y1 y2. \<lbrakk>\<Sigma>1_rel (\<Sigma>\<Sigma>1_rel R) y1 y2; \<Sigma>1_rel phi y1 y2\<rbrakk> \<Longrightarrow> phi (\<oo>\<pp>1 y1) (\<oo>\<pp>1 y2)"
shows "\<Sigma>\<Sigma>1_rel R t1 t2 \<longrightarrow> phi t1 t2"
using \<Sigma>\<Sigma>1_rel_induct_pointfree[of R, OF assms] by auto
(* end TODO *)

end