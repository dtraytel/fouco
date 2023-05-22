header {* Lifting of the distributive law to the free algebra *}


(* This is silimar to Lift_to_Free, but uses \<Lambda>9, \<Sigma>\<Sigma>9, dd9, SpK instead of S, etc. *)

theory Stream_Lift_to_Free9
imports Stream_Distributive_Law9
begin

subsection{* The lifting *}

(* Our aim is lift \<Lambda>9 to an (SpK,SpK,T)-distributive law dd9 compatible with the monadic structure. *)

(* In order to be able to define dd9, we need a larger codomain type: *)
definition ddd9 :: "('a \<times> 'a F) \<Sigma>\<Sigma>9 \<Rightarrow> 'a \<Sigma>\<Sigma>9 \<times> 'a \<Sigma>\<Sigma>9 F" where
"ddd9 = ext9 <\<oo>\<pp>9 o \<Sigma>9_map fst, F_map flat9 o \<Lambda>9> (leaf9 ** F_map leaf9)"

definition dd9 :: "('a \<times> 'a F) \<Sigma>\<Sigma>9 \<Rightarrow> 'a \<Sigma>\<Sigma>9 F" where
"dd9 = snd o ddd9"

lemma ddd9_transfer[transfer_rule]:
  "(\<Sigma>\<Sigma>9_rel (rel_prod R (F_rel R)) ===> rel_prod (\<Sigma>\<Sigma>9_rel R) (F_rel (\<Sigma>\<Sigma>9_rel R))) ddd9 ddd9"
  unfolding ddd9_def ext9_alt by transfer_prover

lemma dd9_transfer[transfer_rule]:
  "(\<Sigma>\<Sigma>9_rel (rel_prod R (F_rel R)) ===> F_rel (\<Sigma>\<Sigma>9_rel R)) dd9 dd9"
  unfolding dd9_def by transfer_prover

lemma F_rel_\<Sigma>\<Sigma>9_rel: "\<Sigma>\<Sigma>9_rel (rel_prod R (F_rel R)) x y \<Longrightarrow> F_rel (\<Sigma>\<Sigma>9_rel R) (dd9 x) (dd9 y)"
  by (erule rel_funD[OF dd9_transfer])

(* We verify the facts for dd9: *)
theorem dd9_leaf9: "dd9 o leaf9 = F_map leaf9 o snd"
unfolding dd9_def ddd9_def o_assoc[symmetric] ext9_comp_leaf9 snd_comp_map_prod ..

lemma ddd9_natural: "ddd9 o \<Sigma>\<Sigma>9_map (f ** F_map f) = (\<Sigma>\<Sigma>9_map f ** F_map (\<Sigma>\<Sigma>9_map f)) o ddd9"
  using ddd9_transfer[of "BNF_Def.Grp UNIV f"]
  unfolding F_rel_Grp prod.rel_Grp \<Sigma>\<Sigma>9.rel_Grp
  unfolding Grp_def rel_fun_def by auto

theorem dd9_natural: "dd9 o \<Sigma>\<Sigma>9_map (f ** F_map f) = F_map (\<Sigma>\<Sigma>9_map f) o dd9"
  using dd9_transfer[of "BNF_Def.Grp UNIV f"]
  unfolding F_rel_Grp prod.rel_Grp \<Sigma>\<Sigma>9.rel_Grp
  unfolding Grp_def rel_fun_def by auto

lemma \<Lambda>9_dd9: "\<Lambda>9 = dd9 o \<oo>\<pp>9 o \<Sigma>9_map leaf9"
  unfolding dd9_def ddd9_def o_assoc[symmetric] \<Sigma>9.map_comp0[symmetric] ext9_commute
  unfolding o_assoc snd_convol ext9_comp_leaf9
  unfolding o_assoc[symmetric] \<Lambda>9_natural
  unfolding o_assoc F_map_comp[symmetric] leaf9_flat9 F_map_id id_o
  ..

lemma fst_ddd9: "fst o ddd9 = \<Sigma>\<Sigma>9_map fst"
proof-
  have "fst o ddd9 = ext9 \<oo>\<pp>9 (leaf9 o fst)"
  apply(rule ext9_unique) unfolding ddd9_def o_assoc[symmetric] ext9_comp_leaf9 ext9_commute
  unfolding o_assoc fst_comp_map_prod fst_convol
  unfolding o_assoc[symmetric] \<Sigma>9.map_comp0 by(rule refl, rule refl)
  also have "... = \<Sigma>\<Sigma>9_map fst"
  apply(rule sym, rule ext9_unique)
  unfolding leaf9_natural \<oo>\<pp>9_natural by(rule refl, rule refl)
  finally show ?thesis .
qed

lemma ddd9_flat9: "(flat9 ** F_map flat9) \<circ> ddd9 \<circ> \<Sigma>\<Sigma>9_map ddd9 = ddd9 o flat9" (is "?L = ?R")
proof-
  have "?L = ext9 <\<oo>\<pp>9 o \<Sigma>9_map fst, F_map flat9 o \<Lambda>9> ddd9"
  proof(rule ext9_unique)
    show "(flat9 ** F_map flat9) \<circ> ddd9 \<circ> \<Sigma>\<Sigma>9_map ddd9 \<circ> leaf9 = ddd9"
    unfolding ddd9_def unfolding o_assoc[symmetric] leaf9_natural
    unfolding o_assoc
    apply(subst o_assoc[symmetric]) unfolding ext9_comp_leaf9
    unfolding map_prod.comp F_map_comp[symmetric] flat9_leaf9 F_map_id map_prod.id id_o ..
  next
    have A: "<flat9 \<circ> (\<oo>\<pp>9 \<circ> \<Sigma>9_map fst) , F_map flat9 \<circ> (F_map flat9 \<circ> \<Lambda>9)>  =
             <\<oo>\<pp>9 \<circ> \<Sigma>9_map fst , F_map flat9 \<circ> \<Lambda>9> \<circ> \<Sigma>9_map (flat9 ** F_map flat9)"
    unfolding o_assoc unfolding flat9_commute[symmetric]
    apply(rule fst_snd_cong) unfolding o_assoc fst_convol snd_convol
    unfolding o_assoc[symmetric] \<Sigma>9.map_comp0[symmetric] fst_comp_map_prod snd_comp_map_prod
    unfolding \<Lambda>9_natural unfolding o_assoc F_map_comp[symmetric] flat9_assoc by(rule refl, rule refl)
    show "(flat9 ** F_map flat9) \<circ> ddd9 \<circ> \<Sigma>\<Sigma>9_map ddd9 \<circ> \<oo>\<pp>9 =
          <\<oo>\<pp>9 \<circ> \<Sigma>9_map fst , F_map flat9 \<circ> \<Lambda>9> \<circ> \<Sigma>9_map (flat9 ** F_map flat9 \<circ> ddd9 \<circ> \<Sigma>\<Sigma>9_map ddd9)"
    unfolding ddd9_def unfolding o_assoc[symmetric] unfolding \<oo>\<pp>9_natural[symmetric]
    unfolding o_assoc
    apply(subst o_assoc[symmetric]) unfolding ext9_commute
    unfolding o_assoc[symmetric] \<Sigma>9.map_comp0[symmetric]
    unfolding \<Sigma>9.map_comp0
    unfolding o_assoc unfolding map_prod_o_convol
    unfolding ext9_\<Sigma>\<Sigma>9_map[symmetric] A ..
  qed
  also have "... = ?R"
  proof(rule sym, rule ext9_unique)
    show "ddd9 \<circ> flat9 \<circ> leaf9 = ddd9" unfolding o_assoc[symmetric] flat9_leaf9 o_id ..
  next
    show "ddd9 \<circ> flat9 \<circ> \<oo>\<pp>9 = <\<oo>\<pp>9 \<circ> \<Sigma>9_map fst , F_map flat9 \<circ> \<Lambda>9> \<circ> \<Sigma>9_map (ddd9 \<circ> flat9)"
    unfolding ddd9_def unfolding o_assoc[symmetric] unfolding flat9_commute[symmetric]
    unfolding o_assoc unfolding ext9_commute \<Sigma>9.map_comp0 unfolding o_assoc ..
  qed
  finally show ?thesis .
qed

theorem dd9_flat9: "F_map flat9 \<circ> dd9 \<circ> \<Sigma>\<Sigma>9_map <\<Sigma>\<Sigma>9_map fst, dd9> = dd9 o flat9"
proof-
  have A: "snd o ((flat9 ** F_map flat9) \<circ> ddd9 \<circ> \<Sigma>\<Sigma>9_map ddd9) = snd o (ddd9 o flat9)"
  unfolding ddd9_flat9 ..
  have B: "ddd9 = <\<Sigma>\<Sigma>9_map fst , snd \<circ> ddd9>" apply(rule fst_snd_cong)
  unfolding fst_ddd9 by auto
  show ?thesis unfolding dd9_def
  unfolding A[symmetric, unfolded o_assoc snd_comp_map_prod] o_assoc B[symmetric] ..
qed

(* The next two theorems are not necessary for the development.
They show that the conditions dd9_leaf9 and dd9_flat9 imply the
more standard conditions for the distributive law dd9' = <\<Sigma>\<Sigma>9_map fst, dd9>
for the functors \<Sigma>\<Sigma>9 and 'a F' = 'a \<times> 'a F_ In fact, they can be shown
equivalent to these. *)

lemma dd9_leaf92: "<\<Sigma>\<Sigma>9_map fst, dd9> o leaf9 = leaf9 ** F_map leaf9"
apply (rule fst_snd_cong) unfolding o_assoc by (simp_all add: leaf9_natural dd9_leaf9)

lemma ddd9_leaf9: "ddd9 \<circ> leaf9 = leaf9 ** F_map leaf9"
unfolding ddd9_def ext9_comp_leaf9 ..

lemma ddd9_\<oo>\<pp>9: "ddd9 \<circ> \<oo>\<pp>9 = <\<oo>\<pp>9 \<circ> \<Sigma>9_map fst , F_map flat9 \<circ> \<Lambda>9> \<circ> \<Sigma>9_map ddd9"
unfolding ddd9_def ext9_commute ..


(* More customization *)

(* TODO Jasmin: Add9 this high-level induction for the relator of datatypes:
(similarly, coinduction for codatatypes): *)
lemma \<Sigma>\<Sigma>9_rel_induct_pointfree:
assumes leaf9: "\<And> x1 x2. R x1 x2 \<Longrightarrow> phi (leaf9 x1) (leaf9 x2)"
and \<oo>\<pp>9: "\<And> y1 y2. \<lbrakk>\<Sigma>9_rel (\<Sigma>\<Sigma>9_rel R) y1 y2; \<Sigma>9_rel phi y1 y2\<rbrakk> \<Longrightarrow> phi (\<oo>\<pp>9 y1) (\<oo>\<pp>9 y2)"
shows "\<Sigma>\<Sigma>9_rel R \<le> phi"
proof-
  have "\<Sigma>\<Sigma>9_rel R \<le> phi \<sqinter> \<Sigma>\<Sigma>9_rel R"
  apply(induct rule: \<Sigma>\<Sigma>9.ctor_rel_induct)
  using assms \<Sigma>\<Sigma>9.rel_inject[of R] unfolding rel_pre_\<Sigma>\<Sigma>9_def \<Sigma>\<Sigma>9.leaf9_def \<Sigma>\<Sigma>9.\<oo>\<pp>9_def
  using inf_greatest[OF \<Sigma>9.rel_mono[OF inf_le1] \<Sigma>9.rel_mono[OF inf_le2]]
  unfolding rel_sum_def BNF_Comp.id_bnf_comp_def vimage2p_def by (auto split: sum.splits) blast+
  thus ?thesis by simp
qed

lemma \<Sigma>\<Sigma>9_rel_induct[case_names leaf9 \<oo>\<pp>9]:
assumes leaf9: "\<And> x1 x2. R x1 x2 \<Longrightarrow> phi (leaf9 x1) (leaf9 x2)"
and \<oo>\<pp>9: "\<And> y1 y2. \<lbrakk>\<Sigma>9_rel (\<Sigma>\<Sigma>9_rel R) y1 y2; \<Sigma>9_rel phi y1 y2\<rbrakk> \<Longrightarrow> phi (\<oo>\<pp>9 y1) (\<oo>\<pp>9 y2)"
shows "\<Sigma>\<Sigma>9_rel R t1 t2 \<longrightarrow> phi t1 t2"
using \<Sigma>\<Sigma>9_rel_induct_pointfree[of R, OF assms] by auto
(* end TODO *)

end