header {* Lifting of the distributive law to the free algebra *}


(* This is silimar to Lift_to_Free, but uses \<Lambda>5, \<Sigma>\<Sigma>5, dd5, SpK instead of S, etc. *)

theory Stream_Lift_to_Free5
imports Stream_Distributive_Law5
begin

subsection{* The lifting *}

(* Our aim is lift \<Lambda>5 to an (SpK,SpK,T)-distributive law dd5 compatible with the monadic structure. *)

(* In order to be able to define dd5, we need a larger codomain type: *)
definition ddd5 :: "('a \<times> 'a F) \<Sigma>\<Sigma>5 \<Rightarrow> 'a \<Sigma>\<Sigma>5 \<times> 'a \<Sigma>\<Sigma>5 F" where
"ddd5 = ext5 <\<oo>\<pp>5 o \<Sigma>5_map fst, F_map flat5 o \<Lambda>5> (leaf5 ** F_map leaf5)"

definition dd5 :: "('a \<times> 'a F) \<Sigma>\<Sigma>5 \<Rightarrow> 'a \<Sigma>\<Sigma>5 F" where
"dd5 = snd o ddd5"

lemma ddd5_transfer[transfer_rule]:
  "(\<Sigma>\<Sigma>5_rel (rel_prod R (F_rel R)) ===> rel_prod (\<Sigma>\<Sigma>5_rel R) (F_rel (\<Sigma>\<Sigma>5_rel R))) ddd5 ddd5"
  unfolding ddd5_def ext5_alt by transfer_prover

lemma dd5_transfer[transfer_rule]:
  "(\<Sigma>\<Sigma>5_rel (rel_prod R (F_rel R)) ===> F_rel (\<Sigma>\<Sigma>5_rel R)) dd5 dd5"
  unfolding dd5_def by transfer_prover

lemma F_rel_\<Sigma>\<Sigma>5_rel: "\<Sigma>\<Sigma>5_rel (rel_prod R (F_rel R)) x y \<Longrightarrow> F_rel (\<Sigma>\<Sigma>5_rel R) (dd5 x) (dd5 y)"
  by (erule rel_funD[OF dd5_transfer])

(* We verify the facts for dd5: *)
theorem dd5_leaf5: "dd5 o leaf5 = F_map leaf5 o snd"
unfolding dd5_def ddd5_def o_assoc[symmetric] ext5_comp_leaf5 snd_comp_map_prod ..

lemma ddd5_natural: "ddd5 o \<Sigma>\<Sigma>5_map (f ** F_map f) = (\<Sigma>\<Sigma>5_map f ** F_map (\<Sigma>\<Sigma>5_map f)) o ddd5"
  using ddd5_transfer[of "BNF_Def.Grp UNIV f"]
  unfolding F_rel_Grp prod.rel_Grp \<Sigma>\<Sigma>5.rel_Grp
  unfolding Grp_def rel_fun_def by auto

theorem dd5_natural: "dd5 o \<Sigma>\<Sigma>5_map (f ** F_map f) = F_map (\<Sigma>\<Sigma>5_map f) o dd5"
  using dd5_transfer[of "BNF_Def.Grp UNIV f"]
  unfolding F_rel_Grp prod.rel_Grp \<Sigma>\<Sigma>5.rel_Grp
  unfolding Grp_def rel_fun_def by auto

lemma \<Lambda>5_dd5: "\<Lambda>5 = dd5 o \<oo>\<pp>5 o \<Sigma>5_map leaf5"
  unfolding dd5_def ddd5_def o_assoc[symmetric] \<Sigma>5.map_comp0[symmetric] ext5_commute
  unfolding o_assoc snd_convol ext5_comp_leaf5
  unfolding o_assoc[symmetric] \<Lambda>5_natural
  unfolding o_assoc F_map_comp[symmetric] leaf5_flat5 F_map_id id_o
  ..

lemma fst_ddd5: "fst o ddd5 = \<Sigma>\<Sigma>5_map fst"
proof-
  have "fst o ddd5 = ext5 \<oo>\<pp>5 (leaf5 o fst)"
  apply(rule ext5_unique) unfolding ddd5_def o_assoc[symmetric] ext5_comp_leaf5 ext5_commute
  unfolding o_assoc fst_comp_map_prod fst_convol
  unfolding o_assoc[symmetric] \<Sigma>5.map_comp0 by(rule refl, rule refl)
  also have "... = \<Sigma>\<Sigma>5_map fst"
  apply(rule sym, rule ext5_unique)
  unfolding leaf5_natural \<oo>\<pp>5_natural by(rule refl, rule refl)
  finally show ?thesis .
qed

lemma ddd5_flat5: "(flat5 ** F_map flat5) \<circ> ddd5 \<circ> \<Sigma>\<Sigma>5_map ddd5 = ddd5 o flat5" (is "?L = ?R")
proof-
  have "?L = ext5 <\<oo>\<pp>5 o \<Sigma>5_map fst, F_map flat5 o \<Lambda>5> ddd5"
  proof(rule ext5_unique)
    show "(flat5 ** F_map flat5) \<circ> ddd5 \<circ> \<Sigma>\<Sigma>5_map ddd5 \<circ> leaf5 = ddd5"
    unfolding ddd5_def unfolding o_assoc[symmetric] leaf5_natural
    unfolding o_assoc
    apply(subst o_assoc[symmetric]) unfolding ext5_comp_leaf5
    unfolding map_prod.comp F_map_comp[symmetric] flat5_leaf5 F_map_id map_prod.id id_o ..
  next
    have A: "<flat5 \<circ> (\<oo>\<pp>5 \<circ> \<Sigma>5_map fst) , F_map flat5 \<circ> (F_map flat5 \<circ> \<Lambda>5)>  =
             <\<oo>\<pp>5 \<circ> \<Sigma>5_map fst , F_map flat5 \<circ> \<Lambda>5> \<circ> \<Sigma>5_map (flat5 ** F_map flat5)"
    unfolding o_assoc unfolding flat5_commute[symmetric]
    apply(rule fst_snd_cong) unfolding o_assoc fst_convol snd_convol
    unfolding o_assoc[symmetric] \<Sigma>5.map_comp0[symmetric] fst_comp_map_prod snd_comp_map_prod
    unfolding \<Lambda>5_natural unfolding o_assoc F_map_comp[symmetric] flat5_assoc by(rule refl, rule refl)
    show "(flat5 ** F_map flat5) \<circ> ddd5 \<circ> \<Sigma>\<Sigma>5_map ddd5 \<circ> \<oo>\<pp>5 =
          <\<oo>\<pp>5 \<circ> \<Sigma>5_map fst , F_map flat5 \<circ> \<Lambda>5> \<circ> \<Sigma>5_map (flat5 ** F_map flat5 \<circ> ddd5 \<circ> \<Sigma>\<Sigma>5_map ddd5)"
    unfolding ddd5_def unfolding o_assoc[symmetric] unfolding \<oo>\<pp>5_natural[symmetric]
    unfolding o_assoc
    apply(subst o_assoc[symmetric]) unfolding ext5_commute
    unfolding o_assoc[symmetric] \<Sigma>5.map_comp0[symmetric]
    unfolding \<Sigma>5.map_comp0
    unfolding o_assoc unfolding map_prod_o_convol
    unfolding ext5_\<Sigma>\<Sigma>5_map[symmetric] A ..
  qed
  also have "... = ?R"
  proof(rule sym, rule ext5_unique)
    show "ddd5 \<circ> flat5 \<circ> leaf5 = ddd5" unfolding o_assoc[symmetric] flat5_leaf5 o_id ..
  next
    show "ddd5 \<circ> flat5 \<circ> \<oo>\<pp>5 = <\<oo>\<pp>5 \<circ> \<Sigma>5_map fst , F_map flat5 \<circ> \<Lambda>5> \<circ> \<Sigma>5_map (ddd5 \<circ> flat5)"
    unfolding ddd5_def unfolding o_assoc[symmetric] unfolding flat5_commute[symmetric]
    unfolding o_assoc unfolding ext5_commute \<Sigma>5.map_comp0 unfolding o_assoc ..
  qed
  finally show ?thesis .
qed

theorem dd5_flat5: "F_map flat5 \<circ> dd5 \<circ> \<Sigma>\<Sigma>5_map <\<Sigma>\<Sigma>5_map fst, dd5> = dd5 o flat5"
proof-
  have A: "snd o ((flat5 ** F_map flat5) \<circ> ddd5 \<circ> \<Sigma>\<Sigma>5_map ddd5) = snd o (ddd5 o flat5)"
  unfolding ddd5_flat5 ..
  have B: "ddd5 = <\<Sigma>\<Sigma>5_map fst , snd \<circ> ddd5>" apply(rule fst_snd_cong)
  unfolding fst_ddd5 by auto
  show ?thesis unfolding dd5_def
  unfolding A[symmetric, unfolded o_assoc snd_comp_map_prod] o_assoc B[symmetric] ..
qed

(* The next two theorems are not necessary for the development.
They show that the conditions dd5_leaf5 and dd5_flat5 imply the
more standard conditions for the distributive law dd5' = <\<Sigma>\<Sigma>5_map fst, dd5>
for the functors \<Sigma>\<Sigma>5 and 'a F' = 'a \<times> 'a F_ In fact, they can be shown
equivalent to these. *)

lemma dd5_leaf52: "<\<Sigma>\<Sigma>5_map fst, dd5> o leaf5 = leaf5 ** F_map leaf5"
apply (rule fst_snd_cong) unfolding o_assoc by (simp_all add: leaf5_natural dd5_leaf5)

lemma ddd5_leaf5: "ddd5 \<circ> leaf5 = leaf5 ** F_map leaf5"
unfolding ddd5_def ext5_comp_leaf5 ..

lemma ddd5_\<oo>\<pp>5: "ddd5 \<circ> \<oo>\<pp>5 = <\<oo>\<pp>5 \<circ> \<Sigma>5_map fst , F_map flat5 \<circ> \<Lambda>5> \<circ> \<Sigma>5_map ddd5"
unfolding ddd5_def ext5_commute ..


(* More customization *)

(* TODO Jasmin: Add5 this high-level induction for the relator of datatypes:
(similarly, coinduction for codatatypes): *)
lemma \<Sigma>\<Sigma>5_rel_induct_pointfree:
assumes leaf5: "\<And> x1 x2. R x1 x2 \<Longrightarrow> phi (leaf5 x1) (leaf5 x2)"
and \<oo>\<pp>5: "\<And> y1 y2. \<lbrakk>\<Sigma>5_rel (\<Sigma>\<Sigma>5_rel R) y1 y2; \<Sigma>5_rel phi y1 y2\<rbrakk> \<Longrightarrow> phi (\<oo>\<pp>5 y1) (\<oo>\<pp>5 y2)"
shows "\<Sigma>\<Sigma>5_rel R \<le> phi"
proof-
  have "\<Sigma>\<Sigma>5_rel R \<le> phi \<sqinter> \<Sigma>\<Sigma>5_rel R"
  apply(induct rule: \<Sigma>\<Sigma>5.ctor_rel_induct)
  using assms \<Sigma>\<Sigma>5.rel_inject[of R] unfolding rel_pre_\<Sigma>\<Sigma>5_def \<Sigma>\<Sigma>5.leaf5_def \<Sigma>\<Sigma>5.\<oo>\<pp>5_def
  using inf_greatest[OF \<Sigma>5.rel_mono[OF inf_le1] \<Sigma>5.rel_mono[OF inf_le2]]
  unfolding rel_sum_def BNF_Comp.id_bnf_comp_def vimage2p_def by (auto split: sum.splits) blast+
  thus ?thesis by simp
qed

lemma \<Sigma>\<Sigma>5_rel_induct[case_names leaf5 \<oo>\<pp>5]:
assumes leaf5: "\<And> x1 x2. R x1 x2 \<Longrightarrow> phi (leaf5 x1) (leaf5 x2)"
and \<oo>\<pp>5: "\<And> y1 y2. \<lbrakk>\<Sigma>5_rel (\<Sigma>\<Sigma>5_rel R) y1 y2; \<Sigma>5_rel phi y1 y2\<rbrakk> \<Longrightarrow> phi (\<oo>\<pp>5 y1) (\<oo>\<pp>5 y2)"
shows "\<Sigma>\<Sigma>5_rel R t1 t2 \<longrightarrow> phi t1 t2"
using \<Sigma>\<Sigma>5_rel_induct_pointfree[of R, OF assms] by auto
(* end TODO *)

end