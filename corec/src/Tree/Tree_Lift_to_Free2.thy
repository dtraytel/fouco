header {* Lifting of the distributive law to the free algebra *}


(* This is silimar to Lift_to_Free, but uses \<Lambda>2, \<Sigma>\<Sigma>2, dd2, SpK instead of S, etc. *)

theory Tree_Lift_to_Free2
imports Tree_Distributive_Law2
begin

subsection{* The lifting *}

(* Our aim is lift \<Lambda>2 to an (SpK,SpK,T)-distributive law dd2 compatible with the monadic structure. *)

(* In order to be able to define dd2, we need a larger codomain type: *)
definition ddd2 :: "('a \<times> 'a F) \<Sigma>\<Sigma>2 \<Rightarrow> 'a \<Sigma>\<Sigma>2 \<times> 'a \<Sigma>\<Sigma>2 F" where
"ddd2 = ext2 <\<oo>\<pp>2 o \<Sigma>2_map fst, F_map flat2 o \<Lambda>2> (leaf2 ** F_map leaf2)"

definition dd2 :: "('a \<times> 'a F) \<Sigma>\<Sigma>2 \<Rightarrow> 'a \<Sigma>\<Sigma>2 F" where
"dd2 = snd o ddd2"

lemma ddd2_transfer[transfer_rule]:
  "(\<Sigma>\<Sigma>2_rel (rel_prod R (F_rel R)) ===> rel_prod (\<Sigma>\<Sigma>2_rel R) (F_rel (\<Sigma>\<Sigma>2_rel R))) ddd2 ddd2"
  unfolding ddd2_def ext2_alt by transfer_prover

lemma dd2_transfer[transfer_rule]:
  "(\<Sigma>\<Sigma>2_rel (rel_prod R (F_rel R)) ===> F_rel (\<Sigma>\<Sigma>2_rel R)) dd2 dd2"
  unfolding dd2_def by transfer_prover

lemma F_rel_\<Sigma>\<Sigma>2_rel: "\<Sigma>\<Sigma>2_rel (rel_prod R (F_rel R)) x y \<Longrightarrow> F_rel (\<Sigma>\<Sigma>2_rel R) (dd2 x) (dd2 y)"
  by (erule rel_funD[OF dd2_transfer])

(* We verify the facts for dd2: *)
theorem dd2_leaf2: "dd2 o leaf2 = F_map leaf2 o snd"
unfolding dd2_def ddd2_def o_assoc[symmetric] ext2_comp_leaf2 snd_comp_map_prod ..

lemma ddd2_natural: "ddd2 o \<Sigma>\<Sigma>2_map (f ** F_map f) = (\<Sigma>\<Sigma>2_map f ** F_map (\<Sigma>\<Sigma>2_map f)) o ddd2"
  using ddd2_transfer[of "BNF_Def.Grp UNIV f"]
  unfolding F_rel_Grp prod.rel_Grp \<Sigma>\<Sigma>2.rel_Grp
  unfolding Grp_def rel_fun_def by auto

theorem dd2_natural: "dd2 o \<Sigma>\<Sigma>2_map (f ** F_map f) = F_map (\<Sigma>\<Sigma>2_map f) o dd2"
  using dd2_transfer[of "BNF_Def.Grp UNIV f"]
  unfolding F_rel_Grp prod.rel_Grp \<Sigma>\<Sigma>2.rel_Grp
  unfolding Grp_def rel_fun_def by auto

lemma \<Lambda>2_dd2: "\<Lambda>2 = dd2 o \<oo>\<pp>2 o \<Sigma>2_map leaf2"
  unfolding dd2_def ddd2_def o_assoc[symmetric] \<Sigma>2.map_comp0[symmetric] ext2_commute
  unfolding o_assoc snd_convol ext2_comp_leaf2
  unfolding o_assoc[symmetric] \<Lambda>2_natural
  unfolding o_assoc F_map_comp[symmetric] leaf2_flat2 F_map_id id_o
  ..

lemma fst_ddd2: "fst o ddd2 = \<Sigma>\<Sigma>2_map fst"
proof-
  have "fst o ddd2 = ext2 \<oo>\<pp>2 (leaf2 o fst)"
  apply(rule ext2_unique) unfolding ddd2_def o_assoc[symmetric] ext2_comp_leaf2 ext2_commute
  unfolding o_assoc fst_comp_map_prod fst_convol
  unfolding o_assoc[symmetric] \<Sigma>2.map_comp0 by(rule refl, rule refl)
  also have "... = \<Sigma>\<Sigma>2_map fst"
  apply(rule sym, rule ext2_unique)
  unfolding leaf2_natural \<oo>\<pp>2_natural by(rule refl, rule refl)
  finally show ?thesis .
qed

lemma ddd2_flat2: "(flat2 ** F_map flat2) \<circ> ddd2 \<circ> \<Sigma>\<Sigma>2_map ddd2 = ddd2 o flat2" (is "?L = ?R")
proof-
  have "?L = ext2 <\<oo>\<pp>2 o \<Sigma>2_map fst, F_map flat2 o \<Lambda>2> ddd2"
  proof(rule ext2_unique)
    show "(flat2 ** F_map flat2) \<circ> ddd2 \<circ> \<Sigma>\<Sigma>2_map ddd2 \<circ> leaf2 = ddd2"
    unfolding ddd2_def unfolding o_assoc[symmetric] leaf2_natural
    unfolding o_assoc
    apply(subst o_assoc[symmetric]) unfolding ext2_comp_leaf2
    unfolding map_prod.comp F_map_comp[symmetric] flat2_leaf2 F_map_id map_prod.id id_o ..
  next
    have A: "<flat2 \<circ> (\<oo>\<pp>2 \<circ> \<Sigma>2_map fst) , F_map flat2 \<circ> (F_map flat2 \<circ> \<Lambda>2)>  =
             <\<oo>\<pp>2 \<circ> \<Sigma>2_map fst , F_map flat2 \<circ> \<Lambda>2> \<circ> \<Sigma>2_map (flat2 ** F_map flat2)"
    unfolding o_assoc unfolding flat2_commute[symmetric]
    apply(rule fst_snd_cong) unfolding o_assoc fst_convol snd_convol
    unfolding o_assoc[symmetric] \<Sigma>2.map_comp0[symmetric] fst_comp_map_prod snd_comp_map_prod
    unfolding \<Lambda>2_natural unfolding o_assoc F_map_comp[symmetric] flat2_assoc by(rule refl, rule refl)
    show "(flat2 ** F_map flat2) \<circ> ddd2 \<circ> \<Sigma>\<Sigma>2_map ddd2 \<circ> \<oo>\<pp>2 =
          <\<oo>\<pp>2 \<circ> \<Sigma>2_map fst , F_map flat2 \<circ> \<Lambda>2> \<circ> \<Sigma>2_map (flat2 ** F_map flat2 \<circ> ddd2 \<circ> \<Sigma>\<Sigma>2_map ddd2)"
    unfolding ddd2_def unfolding o_assoc[symmetric] unfolding \<oo>\<pp>2_natural[symmetric]
    unfolding o_assoc
    apply(subst o_assoc[symmetric]) unfolding ext2_commute
    unfolding o_assoc[symmetric] \<Sigma>2.map_comp0[symmetric]
    unfolding \<Sigma>2.map_comp0
    unfolding o_assoc unfolding map_prod_o_convol
    unfolding ext2_\<Sigma>\<Sigma>2_map[symmetric] A ..
  qed
  also have "... = ?R"
  proof(rule sym, rule ext2_unique)
    show "ddd2 \<circ> flat2 \<circ> leaf2 = ddd2" unfolding o_assoc[symmetric] flat2_leaf2 o_id ..
  next
    show "ddd2 \<circ> flat2 \<circ> \<oo>\<pp>2 = <\<oo>\<pp>2 \<circ> \<Sigma>2_map fst , F_map flat2 \<circ> \<Lambda>2> \<circ> \<Sigma>2_map (ddd2 \<circ> flat2)"
    unfolding ddd2_def unfolding o_assoc[symmetric] unfolding flat2_commute[symmetric]
    unfolding o_assoc unfolding ext2_commute \<Sigma>2.map_comp0 unfolding o_assoc ..
  qed
  finally show ?thesis .
qed

theorem dd2_flat2: "F_map flat2 \<circ> dd2 \<circ> \<Sigma>\<Sigma>2_map <\<Sigma>\<Sigma>2_map fst, dd2> = dd2 o flat2"
proof-
  have A: "snd o ((flat2 ** F_map flat2) \<circ> ddd2 \<circ> \<Sigma>\<Sigma>2_map ddd2) = snd o (ddd2 o flat2)"
  unfolding ddd2_flat2 ..
  have B: "ddd2 = <\<Sigma>\<Sigma>2_map fst , snd \<circ> ddd2>" apply(rule fst_snd_cong)
  unfolding fst_ddd2 by auto
  show ?thesis unfolding dd2_def
  unfolding A[symmetric, unfolded o_assoc snd_comp_map_prod] o_assoc B[symmetric] ..
qed

(* The next two theorems are not necessary for the development.
They show that the conditions dd2_leaf2 and dd2_flat2 imply the
more standard conditions for the distributive law dd2' = <\<Sigma>\<Sigma>2_map fst, dd2>
for the functors \<Sigma>\<Sigma>2 and 'a F' = 'a \<times> 'a F_ In fact, they can be shown
equivalent to these. *)

lemma dd2_leaf22: "<\<Sigma>\<Sigma>2_map fst, dd2> o leaf2 = leaf2 ** F_map leaf2"
apply (rule fst_snd_cong) unfolding o_assoc by (simp_all add: leaf2_natural dd2_leaf2)

lemma ddd2_leaf2: "ddd2 \<circ> leaf2 = leaf2 ** F_map leaf2"
unfolding ddd2_def ext2_comp_leaf2 ..

lemma ddd2_\<oo>\<pp>2: "ddd2 \<circ> \<oo>\<pp>2 = <\<oo>\<pp>2 \<circ> \<Sigma>2_map fst , F_map flat2 \<circ> \<Lambda>2> \<circ> \<Sigma>2_map ddd2"
unfolding ddd2_def ext2_commute ..


(* More customization *)

(* TODO Jasmin: Add2 this high-level induction for the relator of datatypes:
(similarly, coinduction for codatatypes): *)
lemma \<Sigma>\<Sigma>2_rel_induct_pointfree:
assumes leaf2: "\<And> x1 x2. R x1 x2 \<Longrightarrow> phi (leaf2 x1) (leaf2 x2)"
and \<oo>\<pp>2: "\<And> y1 y2. \<lbrakk>\<Sigma>2_rel (\<Sigma>\<Sigma>2_rel R) y1 y2; \<Sigma>2_rel phi y1 y2\<rbrakk> \<Longrightarrow> phi (\<oo>\<pp>2 y1) (\<oo>\<pp>2 y2)"
shows "\<Sigma>\<Sigma>2_rel R \<le> phi"
proof-
  have "\<Sigma>\<Sigma>2_rel R \<le> phi \<sqinter> \<Sigma>\<Sigma>2_rel R"
  apply(induct rule: \<Sigma>\<Sigma>2.ctor_rel_induct)
  using assms \<Sigma>\<Sigma>2.rel_inject[of R] unfolding rel_pre_\<Sigma>\<Sigma>2_def \<Sigma>\<Sigma>2.leaf2_def \<Sigma>\<Sigma>2.\<oo>\<pp>2_def
  using inf_greatest[OF \<Sigma>2.rel_mono[OF inf_le1] \<Sigma>2.rel_mono[OF inf_le2]]
  unfolding rel_sum_def BNF_Comp.id_bnf_comp_def vimage2p_def by (auto split: sum.splits) blast+
  thus ?thesis by simp
qed

lemma \<Sigma>\<Sigma>2_rel_induct[case_names leaf2 \<oo>\<pp>2]:
assumes leaf2: "\<And> x1 x2. R x1 x2 \<Longrightarrow> phi (leaf2 x1) (leaf2 x2)"
and \<oo>\<pp>2: "\<And> y1 y2. \<lbrakk>\<Sigma>2_rel (\<Sigma>\<Sigma>2_rel R) y1 y2; \<Sigma>2_rel phi y1 y2\<rbrakk> \<Longrightarrow> phi (\<oo>\<pp>2 y1) (\<oo>\<pp>2 y2)"
shows "\<Sigma>\<Sigma>2_rel R t1 t2 \<longrightarrow> phi t1 t2"
using \<Sigma>\<Sigma>2_rel_induct_pointfree[of R, OF assms] by auto
(* end TODO *)

end