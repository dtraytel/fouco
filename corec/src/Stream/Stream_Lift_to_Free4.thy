header {* Lifting of the distributive law to the free algebra *}


(* This is silimar to Lift_to_Free, but uses \<Lambda>4, \<Sigma>\<Sigma>4, dd4, SpK instead of S, etc. *)

theory Stream_Lift_to_Free4
imports Stream_Distributive_Law4
begin

subsection{* The lifting *}

(* Our aim is lift \<Lambda>4 to an (SpK,SpK,T)-distributive law dd4 compatible with the monadic structure. *)

(* In order to be able to define dd4, we need a larger codomain type: *)
definition ddd4 :: "('a \<times> 'a F) \<Sigma>\<Sigma>4 \<Rightarrow> 'a \<Sigma>\<Sigma>4 \<times> 'a \<Sigma>\<Sigma>4 F" where
"ddd4 = ext4 <\<oo>\<pp>4 o \<Sigma>4_map fst, F_map flat4 o \<Lambda>4> (leaf4 ** F_map leaf4)"

definition dd4 :: "('a \<times> 'a F) \<Sigma>\<Sigma>4 \<Rightarrow> 'a \<Sigma>\<Sigma>4 F" where
"dd4 = snd o ddd4"

lemma ddd4_transfer[transfer_rule]:
  "(\<Sigma>\<Sigma>4_rel (rel_prod R (F_rel R)) ===> rel_prod (\<Sigma>\<Sigma>4_rel R) (F_rel (\<Sigma>\<Sigma>4_rel R))) ddd4 ddd4"
  unfolding ddd4_def ext4_alt by transfer_prover

lemma dd4_transfer[transfer_rule]:
  "(\<Sigma>\<Sigma>4_rel (rel_prod R (F_rel R)) ===> F_rel (\<Sigma>\<Sigma>4_rel R)) dd4 dd4"
  unfolding dd4_def by transfer_prover

lemma F_rel_\<Sigma>\<Sigma>4_rel: "\<Sigma>\<Sigma>4_rel (rel_prod R (F_rel R)) x y \<Longrightarrow> F_rel (\<Sigma>\<Sigma>4_rel R) (dd4 x) (dd4 y)"
  by (erule rel_funD[OF dd4_transfer])

(* We verify the facts for dd4: *)
theorem dd4_leaf4: "dd4 o leaf4 = F_map leaf4 o snd"
unfolding dd4_def ddd4_def o_assoc[symmetric] ext4_comp_leaf4 snd_comp_map_prod ..

lemma ddd4_natural: "ddd4 o \<Sigma>\<Sigma>4_map (f ** F_map f) = (\<Sigma>\<Sigma>4_map f ** F_map (\<Sigma>\<Sigma>4_map f)) o ddd4"
  using ddd4_transfer[of "BNF_Def.Grp UNIV f"]
  unfolding F_rel_Grp prod.rel_Grp \<Sigma>\<Sigma>4.rel_Grp
  unfolding Grp_def rel_fun_def by auto

theorem dd4_natural: "dd4 o \<Sigma>\<Sigma>4_map (f ** F_map f) = F_map (\<Sigma>\<Sigma>4_map f) o dd4"
  using dd4_transfer[of "BNF_Def.Grp UNIV f"]
  unfolding F_rel_Grp prod.rel_Grp \<Sigma>\<Sigma>4.rel_Grp
  unfolding Grp_def rel_fun_def by auto

lemma \<Lambda>4_dd4: "\<Lambda>4 = dd4 o \<oo>\<pp>4 o \<Sigma>4_map leaf4"
  unfolding dd4_def ddd4_def o_assoc[symmetric] \<Sigma>4.map_comp0[symmetric] ext4_commute
  unfolding o_assoc snd_convol ext4_comp_leaf4
  unfolding o_assoc[symmetric] \<Lambda>4_natural
  unfolding o_assoc F_map_comp[symmetric] leaf4_flat4 F_map_id id_o
  ..

lemma fst_ddd4: "fst o ddd4 = \<Sigma>\<Sigma>4_map fst"
proof-
  have "fst o ddd4 = ext4 \<oo>\<pp>4 (leaf4 o fst)"
  apply(rule ext4_unique) unfolding ddd4_def o_assoc[symmetric] ext4_comp_leaf4 ext4_commute
  unfolding o_assoc fst_comp_map_prod fst_convol
  unfolding o_assoc[symmetric] \<Sigma>4.map_comp0 by(rule refl, rule refl)
  also have "... = \<Sigma>\<Sigma>4_map fst"
  apply(rule sym, rule ext4_unique)
  unfolding leaf4_natural \<oo>\<pp>4_natural by(rule refl, rule refl)
  finally show ?thesis .
qed

lemma ddd4_flat4: "(flat4 ** F_map flat4) \<circ> ddd4 \<circ> \<Sigma>\<Sigma>4_map ddd4 = ddd4 o flat4" (is "?L = ?R")
proof-
  have "?L = ext4 <\<oo>\<pp>4 o \<Sigma>4_map fst, F_map flat4 o \<Lambda>4> ddd4"
  proof(rule ext4_unique)
    show "(flat4 ** F_map flat4) \<circ> ddd4 \<circ> \<Sigma>\<Sigma>4_map ddd4 \<circ> leaf4 = ddd4"
    unfolding ddd4_def unfolding o_assoc[symmetric] leaf4_natural
    unfolding o_assoc
    apply(subst o_assoc[symmetric]) unfolding ext4_comp_leaf4
    unfolding map_prod.comp F_map_comp[symmetric] flat4_leaf4 F_map_id map_prod.id id_o ..
  next
    have A: "<flat4 \<circ> (\<oo>\<pp>4 \<circ> \<Sigma>4_map fst) , F_map flat4 \<circ> (F_map flat4 \<circ> \<Lambda>4)>  =
             <\<oo>\<pp>4 \<circ> \<Sigma>4_map fst , F_map flat4 \<circ> \<Lambda>4> \<circ> \<Sigma>4_map (flat4 ** F_map flat4)"
    unfolding o_assoc unfolding flat4_commute[symmetric]
    apply(rule fst_snd_cong) unfolding o_assoc fst_convol snd_convol
    unfolding o_assoc[symmetric] \<Sigma>4.map_comp0[symmetric] fst_comp_map_prod snd_comp_map_prod
    unfolding \<Lambda>4_natural unfolding o_assoc F_map_comp[symmetric] flat4_assoc by(rule refl, rule refl)
    show "(flat4 ** F_map flat4) \<circ> ddd4 \<circ> \<Sigma>\<Sigma>4_map ddd4 \<circ> \<oo>\<pp>4 =
          <\<oo>\<pp>4 \<circ> \<Sigma>4_map fst , F_map flat4 \<circ> \<Lambda>4> \<circ> \<Sigma>4_map (flat4 ** F_map flat4 \<circ> ddd4 \<circ> \<Sigma>\<Sigma>4_map ddd4)"
    unfolding ddd4_def unfolding o_assoc[symmetric] unfolding \<oo>\<pp>4_natural[symmetric]
    unfolding o_assoc
    apply(subst o_assoc[symmetric]) unfolding ext4_commute
    unfolding o_assoc[symmetric] \<Sigma>4.map_comp0[symmetric]
    unfolding \<Sigma>4.map_comp0
    unfolding o_assoc unfolding map_prod_o_convol
    unfolding ext4_\<Sigma>\<Sigma>4_map[symmetric] A ..
  qed
  also have "... = ?R"
  proof(rule sym, rule ext4_unique)
    show "ddd4 \<circ> flat4 \<circ> leaf4 = ddd4" unfolding o_assoc[symmetric] flat4_leaf4 o_id ..
  next
    show "ddd4 \<circ> flat4 \<circ> \<oo>\<pp>4 = <\<oo>\<pp>4 \<circ> \<Sigma>4_map fst , F_map flat4 \<circ> \<Lambda>4> \<circ> \<Sigma>4_map (ddd4 \<circ> flat4)"
    unfolding ddd4_def unfolding o_assoc[symmetric] unfolding flat4_commute[symmetric]
    unfolding o_assoc unfolding ext4_commute \<Sigma>4.map_comp0 unfolding o_assoc ..
  qed
  finally show ?thesis .
qed

theorem dd4_flat4: "F_map flat4 \<circ> dd4 \<circ> \<Sigma>\<Sigma>4_map <\<Sigma>\<Sigma>4_map fst, dd4> = dd4 o flat4"
proof-
  have A: "snd o ((flat4 ** F_map flat4) \<circ> ddd4 \<circ> \<Sigma>\<Sigma>4_map ddd4) = snd o (ddd4 o flat4)"
  unfolding ddd4_flat4 ..
  have B: "ddd4 = <\<Sigma>\<Sigma>4_map fst , snd \<circ> ddd4>" apply(rule fst_snd_cong)
  unfolding fst_ddd4 by auto
  show ?thesis unfolding dd4_def
  unfolding A[symmetric, unfolded o_assoc snd_comp_map_prod] o_assoc B[symmetric] ..
qed

(* The next two theorems are not necessary for the development.
They show that the conditions dd4_leaf4 and dd4_flat4 imply the
more standard conditions for the distributive law dd4' = <\<Sigma>\<Sigma>4_map fst, dd4>
for the functors \<Sigma>\<Sigma>4 and 'a F' = 'a \<times> 'a F_ In fact, they can be shown
equivalent to these. *)

lemma dd4_leaf42: "<\<Sigma>\<Sigma>4_map fst, dd4> o leaf4 = leaf4 ** F_map leaf4"
apply (rule fst_snd_cong) unfolding o_assoc by (simp_all add: leaf4_natural dd4_leaf4)

lemma ddd4_leaf4: "ddd4 \<circ> leaf4 = leaf4 ** F_map leaf4"
unfolding ddd4_def ext4_comp_leaf4 ..

lemma ddd4_\<oo>\<pp>4: "ddd4 \<circ> \<oo>\<pp>4 = <\<oo>\<pp>4 \<circ> \<Sigma>4_map fst , F_map flat4 \<circ> \<Lambda>4> \<circ> \<Sigma>4_map ddd4"
unfolding ddd4_def ext4_commute ..


(* More customization *)

(* TODO Jasmin: Add4 this high-level induction for the relator of datatypes:
(similarly, coinduction for codatatypes): *)
lemma \<Sigma>\<Sigma>4_rel_induct_pointfree:
assumes leaf4: "\<And> x1 x2. R x1 x2 \<Longrightarrow> phi (leaf4 x1) (leaf4 x2)"
and \<oo>\<pp>4: "\<And> y1 y2. \<lbrakk>\<Sigma>4_rel (\<Sigma>\<Sigma>4_rel R) y1 y2; \<Sigma>4_rel phi y1 y2\<rbrakk> \<Longrightarrow> phi (\<oo>\<pp>4 y1) (\<oo>\<pp>4 y2)"
shows "\<Sigma>\<Sigma>4_rel R \<le> phi"
proof-
  have "\<Sigma>\<Sigma>4_rel R \<le> phi \<sqinter> \<Sigma>\<Sigma>4_rel R"
  apply(induct rule: \<Sigma>\<Sigma>4.ctor_rel_induct)
  using assms \<Sigma>\<Sigma>4.rel_inject[of R] unfolding rel_pre_\<Sigma>\<Sigma>4_def \<Sigma>\<Sigma>4.leaf4_def \<Sigma>\<Sigma>4.\<oo>\<pp>4_def
  using inf_greatest[OF \<Sigma>4.rel_mono[OF inf_le1] \<Sigma>4.rel_mono[OF inf_le2]]
  unfolding rel_sum_def BNF_Comp.id_bnf_comp_def vimage2p_def by (auto split: sum.splits) blast+
  thus ?thesis by simp
qed

lemma \<Sigma>\<Sigma>4_rel_induct[case_names leaf4 \<oo>\<pp>4]:
assumes leaf4: "\<And> x1 x2. R x1 x2 \<Longrightarrow> phi (leaf4 x1) (leaf4 x2)"
and \<oo>\<pp>4: "\<And> y1 y2. \<lbrakk>\<Sigma>4_rel (\<Sigma>\<Sigma>4_rel R) y1 y2; \<Sigma>4_rel phi y1 y2\<rbrakk> \<Longrightarrow> phi (\<oo>\<pp>4 y1) (\<oo>\<pp>4 y2)"
shows "\<Sigma>\<Sigma>4_rel R t1 t2 \<longrightarrow> phi t1 t2"
using \<Sigma>\<Sigma>4_rel_induct_pointfree[of R, OF assms] by auto
(* end TODO *)

end