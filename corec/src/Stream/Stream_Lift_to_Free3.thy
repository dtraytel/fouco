header {* Lifting of the distributive law to the free algebra *}


(* This is silimar to Lift_to_Free, but uses \<Lambda>3, \<Sigma>\<Sigma>3, dd3, SpK instead of S, etc. *)

theory Stream_Lift_to_Free3
imports Stream_Distributive_Law3
begin

subsection{* The lifting *}

(* Our aim is lift \<Lambda>3 to an (SpK,SpK,T)-distributive law dd3 compatible with the monadic structure. *)

(* In order to be able to define dd3, we need a larger codomain type: *)
definition ddd3 :: "('a \<times> 'a F) \<Sigma>\<Sigma>3 \<Rightarrow> 'a \<Sigma>\<Sigma>3 \<times> 'a \<Sigma>\<Sigma>3 F" where
"ddd3 = ext3 <\<oo>\<pp>3 o \<Sigma>3_map fst, F_map flat3 o \<Lambda>3> (leaf3 ** F_map leaf3)"

definition dd3 :: "('a \<times> 'a F) \<Sigma>\<Sigma>3 \<Rightarrow> 'a \<Sigma>\<Sigma>3 F" where
"dd3 = snd o ddd3"

lemma ddd3_transfer[transfer_rule]:
  "(\<Sigma>\<Sigma>3_rel (rel_prod R (F_rel R)) ===> rel_prod (\<Sigma>\<Sigma>3_rel R) (F_rel (\<Sigma>\<Sigma>3_rel R))) ddd3 ddd3"
  unfolding ddd3_def ext3_alt by transfer_prover

lemma dd3_transfer[transfer_rule]:
  "(\<Sigma>\<Sigma>3_rel (rel_prod R (F_rel R)) ===> F_rel (\<Sigma>\<Sigma>3_rel R)) dd3 dd3"
  unfolding dd3_def by transfer_prover

lemma F_rel_\<Sigma>\<Sigma>3_rel: "\<Sigma>\<Sigma>3_rel (rel_prod R (F_rel R)) x y \<Longrightarrow> F_rel (\<Sigma>\<Sigma>3_rel R) (dd3 x) (dd3 y)"
  by (erule rel_funD[OF dd3_transfer])

(* We verify the facts for dd3: *)
theorem dd3_leaf3: "dd3 o leaf3 = F_map leaf3 o snd"
unfolding dd3_def ddd3_def o_assoc[symmetric] ext3_comp_leaf3 snd_comp_map_prod ..

lemma ddd3_natural: "ddd3 o \<Sigma>\<Sigma>3_map (f ** F_map f) = (\<Sigma>\<Sigma>3_map f ** F_map (\<Sigma>\<Sigma>3_map f)) o ddd3"
  using ddd3_transfer[of "BNF_Def.Grp UNIV f"]
  unfolding F_rel_Grp prod.rel_Grp \<Sigma>\<Sigma>3.rel_Grp
  unfolding Grp_def rel_fun_def by auto

theorem dd3_natural: "dd3 o \<Sigma>\<Sigma>3_map (f ** F_map f) = F_map (\<Sigma>\<Sigma>3_map f) o dd3"
  using dd3_transfer[of "BNF_Def.Grp UNIV f"]
  unfolding F_rel_Grp prod.rel_Grp \<Sigma>\<Sigma>3.rel_Grp
  unfolding Grp_def rel_fun_def by auto

lemma \<Lambda>3_dd3: "\<Lambda>3 = dd3 o \<oo>\<pp>3 o \<Sigma>3_map leaf3"
  unfolding dd3_def ddd3_def o_assoc[symmetric] \<Sigma>3.map_comp0[symmetric] ext3_commute
  unfolding o_assoc snd_convol ext3_comp_leaf3
  unfolding o_assoc[symmetric] \<Lambda>3_natural
  unfolding o_assoc F_map_comp[symmetric] leaf3_flat3 F_map_id id_o
  ..

lemma fst_ddd3: "fst o ddd3 = \<Sigma>\<Sigma>3_map fst"
proof-
  have "fst o ddd3 = ext3 \<oo>\<pp>3 (leaf3 o fst)"
  apply(rule ext3_unique) unfolding ddd3_def o_assoc[symmetric] ext3_comp_leaf3 ext3_commute
  unfolding o_assoc fst_comp_map_prod fst_convol
  unfolding o_assoc[symmetric] \<Sigma>3.map_comp0 by(rule refl, rule refl)
  also have "... = \<Sigma>\<Sigma>3_map fst"
  apply(rule sym, rule ext3_unique)
  unfolding leaf3_natural \<oo>\<pp>3_natural by(rule refl, rule refl)
  finally show ?thesis .
qed

lemma ddd3_flat3: "(flat3 ** F_map flat3) \<circ> ddd3 \<circ> \<Sigma>\<Sigma>3_map ddd3 = ddd3 o flat3" (is "?L = ?R")
proof-
  have "?L = ext3 <\<oo>\<pp>3 o \<Sigma>3_map fst, F_map flat3 o \<Lambda>3> ddd3"
  proof(rule ext3_unique)
    show "(flat3 ** F_map flat3) \<circ> ddd3 \<circ> \<Sigma>\<Sigma>3_map ddd3 \<circ> leaf3 = ddd3"
    unfolding ddd3_def unfolding o_assoc[symmetric] leaf3_natural
    unfolding o_assoc
    apply(subst o_assoc[symmetric]) unfolding ext3_comp_leaf3
    unfolding map_prod.comp F_map_comp[symmetric] flat3_leaf3 F_map_id map_prod.id id_o ..
  next
    have A: "<flat3 \<circ> (\<oo>\<pp>3 \<circ> \<Sigma>3_map fst) , F_map flat3 \<circ> (F_map flat3 \<circ> \<Lambda>3)>  =
             <\<oo>\<pp>3 \<circ> \<Sigma>3_map fst , F_map flat3 \<circ> \<Lambda>3> \<circ> \<Sigma>3_map (flat3 ** F_map flat3)"
    unfolding o_assoc unfolding flat3_commute[symmetric]
    apply(rule fst_snd_cong) unfolding o_assoc fst_convol snd_convol
    unfolding o_assoc[symmetric] \<Sigma>3.map_comp0[symmetric] fst_comp_map_prod snd_comp_map_prod
    unfolding \<Lambda>3_natural unfolding o_assoc F_map_comp[symmetric] flat3_assoc by(rule refl, rule refl)
    show "(flat3 ** F_map flat3) \<circ> ddd3 \<circ> \<Sigma>\<Sigma>3_map ddd3 \<circ> \<oo>\<pp>3 =
          <\<oo>\<pp>3 \<circ> \<Sigma>3_map fst , F_map flat3 \<circ> \<Lambda>3> \<circ> \<Sigma>3_map (flat3 ** F_map flat3 \<circ> ddd3 \<circ> \<Sigma>\<Sigma>3_map ddd3)"
    unfolding ddd3_def unfolding o_assoc[symmetric] unfolding \<oo>\<pp>3_natural[symmetric]
    unfolding o_assoc
    apply(subst o_assoc[symmetric]) unfolding ext3_commute
    unfolding o_assoc[symmetric] \<Sigma>3.map_comp0[symmetric]
    unfolding \<Sigma>3.map_comp0
    unfolding o_assoc unfolding map_prod_o_convol
    unfolding ext3_\<Sigma>\<Sigma>3_map[symmetric] A ..
  qed
  also have "... = ?R"
  proof(rule sym, rule ext3_unique)
    show "ddd3 \<circ> flat3 \<circ> leaf3 = ddd3" unfolding o_assoc[symmetric] flat3_leaf3 o_id ..
  next
    show "ddd3 \<circ> flat3 \<circ> \<oo>\<pp>3 = <\<oo>\<pp>3 \<circ> \<Sigma>3_map fst , F_map flat3 \<circ> \<Lambda>3> \<circ> \<Sigma>3_map (ddd3 \<circ> flat3)"
    unfolding ddd3_def unfolding o_assoc[symmetric] unfolding flat3_commute[symmetric]
    unfolding o_assoc unfolding ext3_commute \<Sigma>3.map_comp0 unfolding o_assoc ..
  qed
  finally show ?thesis .
qed

theorem dd3_flat3: "F_map flat3 \<circ> dd3 \<circ> \<Sigma>\<Sigma>3_map <\<Sigma>\<Sigma>3_map fst, dd3> = dd3 o flat3"
proof-
  have A: "snd o ((flat3 ** F_map flat3) \<circ> ddd3 \<circ> \<Sigma>\<Sigma>3_map ddd3) = snd o (ddd3 o flat3)"
  unfolding ddd3_flat3 ..
  have B: "ddd3 = <\<Sigma>\<Sigma>3_map fst , snd \<circ> ddd3>" apply(rule fst_snd_cong)
  unfolding fst_ddd3 by auto
  show ?thesis unfolding dd3_def
  unfolding A[symmetric, unfolded o_assoc snd_comp_map_prod] o_assoc B[symmetric] ..
qed

(* The next two theorems are not necessary for the development.
They show that the conditions dd3_leaf3 and dd3_flat3 imply the
more standard conditions for the distributive law dd3' = <\<Sigma>\<Sigma>3_map fst, dd3>
for the functors \<Sigma>\<Sigma>3 and 'a F' = 'a \<times> 'a F_ In fact, they can be shown
equivalent to these. *)

lemma dd3_leaf32: "<\<Sigma>\<Sigma>3_map fst, dd3> o leaf3 = leaf3 ** F_map leaf3"
apply (rule fst_snd_cong) unfolding o_assoc by (simp_all add: leaf3_natural dd3_leaf3)

lemma ddd3_leaf3: "ddd3 \<circ> leaf3 = leaf3 ** F_map leaf3"
unfolding ddd3_def ext3_comp_leaf3 ..

lemma ddd3_\<oo>\<pp>3: "ddd3 \<circ> \<oo>\<pp>3 = <\<oo>\<pp>3 \<circ> \<Sigma>3_map fst , F_map flat3 \<circ> \<Lambda>3> \<circ> \<Sigma>3_map ddd3"
unfolding ddd3_def ext3_commute ..


(* More customization *)

(* TODO Jasmin: Add3 this high-level induction for the relator of datatypes:
(similarly, coinduction for codatatypes): *)
lemma \<Sigma>\<Sigma>3_rel_induct_pointfree:
assumes leaf3: "\<And> x1 x2. R x1 x2 \<Longrightarrow> phi (leaf3 x1) (leaf3 x2)"
and \<oo>\<pp>3: "\<And> y1 y2. \<lbrakk>\<Sigma>3_rel (\<Sigma>\<Sigma>3_rel R) y1 y2; \<Sigma>3_rel phi y1 y2\<rbrakk> \<Longrightarrow> phi (\<oo>\<pp>3 y1) (\<oo>\<pp>3 y2)"
shows "\<Sigma>\<Sigma>3_rel R \<le> phi"
proof-
  have "\<Sigma>\<Sigma>3_rel R \<le> phi \<sqinter> \<Sigma>\<Sigma>3_rel R"
  apply(induct rule: \<Sigma>\<Sigma>3.ctor_rel_induct)
  using assms \<Sigma>\<Sigma>3.rel_inject[of R] unfolding rel_pre_\<Sigma>\<Sigma>3_def \<Sigma>\<Sigma>3.leaf3_def \<Sigma>\<Sigma>3.\<oo>\<pp>3_def
  using inf_greatest[OF \<Sigma>3.rel_mono[OF inf_le1] \<Sigma>3.rel_mono[OF inf_le2]]
  unfolding rel_sum_def BNF_Comp.id_bnf_comp_def vimage2p_def by (auto split: sum.splits) blast+
  thus ?thesis by simp
qed

lemma \<Sigma>\<Sigma>3_rel_induct[case_names leaf3 \<oo>\<pp>3]:
assumes leaf3: "\<And> x1 x2. R x1 x2 \<Longrightarrow> phi (leaf3 x1) (leaf3 x2)"
and \<oo>\<pp>3: "\<And> y1 y2. \<lbrakk>\<Sigma>3_rel (\<Sigma>\<Sigma>3_rel R) y1 y2; \<Sigma>3_rel phi y1 y2\<rbrakk> \<Longrightarrow> phi (\<oo>\<pp>3 y1) (\<oo>\<pp>3 y2)"
shows "\<Sigma>\<Sigma>3_rel R t1 t2 \<longrightarrow> phi t1 t2"
using \<Sigma>\<Sigma>3_rel_induct_pointfree[of R, OF assms] by auto
(* end TODO *)

end