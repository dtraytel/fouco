header{* The initial free algebra for bootstrapping, for a copy of the behavior BNF *}

theory Binary_Tree_FreeAlg0
imports Binary_Tree_Behavior_BNF
begin

(* Initially, the signature functor and the behavior functor coincide: \<Sigma>0 = (a copy of) F
This corresponds to corecursion with any > 0 number of guards. *)

typedef 'a \<Sigma>0 = "UNIV :: 'a F set" by (rule UNIV_witness)

setup_lifting type_definition_\<Sigma>0

lift_definition \<Sigma>0_map :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Sigma>0 \<Rightarrow> 'b \<Sigma>0" is F_map .
lift_definition \<Sigma>0_set :: "'a \<Sigma>0 \<Rightarrow> 'a set" is F_set .
lift_definition \<Sigma>0_rel :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a \<Sigma>0 \<Rightarrow> 'b \<Sigma>0 \<Rightarrow> bool" is F_rel .

typedef \<Sigma>0_bd_type = "UNIV :: bd_type_F set" by (rule UNIV_witness)
definition "\<Sigma>0_bd = dir_image F_bd Abs_\<Sigma>0_bd_type"

bnf "'a \<Sigma>0"
  map: \<Sigma>0_map
  sets: \<Sigma>0_set
  bd: \<Sigma>0_bd
  rel: \<Sigma>0_rel
unfolding \<Sigma>0_bd_def
apply -
apply transfer apply (rule pre_J.map_id0)
apply transfer apply (rule pre_J.map_comp0)
apply transfer apply (erule pre_J.map_cong0)
apply transfer apply (rule pre_J.set_map0)
apply (rule card_order_dir_image[OF bijI pre_J.bd_card_order])
apply (metis inj_on_def Abs_\<Sigma>0_bd_type_inverse[OF UNIV_I])
apply (metis surj_def Abs_\<Sigma>0_bd_type_cases)
apply (rule conjunct1[OF Cinfinite_cong[OF dir_image[OF _ pre_J.bd_Card_order] pre_J.bd_Cinfinite]])
apply (metis Abs_\<Sigma>0_bd_type_inverse[OF UNIV_I])
apply (unfold \<Sigma>0_set_def map_fun_def id_o) [1] apply (subst o_apply)
apply (rule ordLeq_ordIso_trans[OF pre_J.set_bd dir_image[OF _ pre_J.bd_Card_order]])
apply (metis Abs_\<Sigma>0_bd_type_inverse[OF UNIV_I])
apply (rule predicate2I) apply transfer apply (subst pre_J.rel_compp) apply assumption
apply transfer' apply (rule pre_J.rel_compp_Grp)
done

declare \<Sigma>0.map_transfer[transfer_rule]

lemma Rep_\<Sigma>0_transfer[transfer_rule]: "(\<Sigma>0_rel R ===> F_rel R) Rep_\<Sigma>0 Rep_\<Sigma>0"
  unfolding rel_fun_def by transfer blast

lemma Abs_\<Sigma>0_transfer[transfer_rule]: "(F_rel R ===> \<Sigma>0_rel R) Abs_\<Sigma>0 Abs_\<Sigma>0"
  unfolding rel_fun_def by transfer blast

theorem Rep_\<Sigma>0_natural: "F_map f o Rep_\<Sigma>0 = Rep_\<Sigma>0 o \<Sigma>0_map f"
  using Rep_\<Sigma>0_transfer[of "BNF_Def.Grp UNIV f"]
  unfolding \<Sigma>0.rel_Grp F_rel_Grp
  unfolding Grp_def rel_fun_def by auto

theorem Abs_\<Sigma>0_natural: "\<Sigma>0_map f o Abs_\<Sigma>0 = Abs_\<Sigma>0 o F_map f"
  using Abs_\<Sigma>0_transfer[of "BNF_Def.Grp UNIV f"]
  unfolding \<Sigma>0.rel_Grp F_rel_Grp
  unfolding Grp_def rel_fun_def by auto

lemma Rep_\<Sigma>0_o_Abs_\<Sigma>0: "Rep_\<Sigma>0 o Abs_\<Sigma>0 = id"
  apply (rule ext)
  apply (rule box_equals[OF _ o_apply[symmetric] id_apply[symmetric]])
  apply (rule Abs_\<Sigma>0_inverse[OF UNIV_I])
  done

lemma \<Sigma>0_rel_\<Sigma>0_map_\<Sigma>0_map:
  "\<Sigma>0_rel R (\<Sigma>0_map f x) (\<Sigma>0_map g y) = \<Sigma>0_rel (BNF_Def.vimage2p f g R) x y"
  unfolding \<Sigma>0.rel_Grp vimage2p_Grp \<Sigma>0.rel_compp \<Sigma>0.rel_conversep
  unfolding relcompp.simps Grp_def by blast

(* \<Sigma>\<Sigma>0 is a copy of FreeAlg, but imports Behavior_BNF instead of Signature_BNF,
menaing that it uses a specific \<Sigma>0 which is a copy of F, instead of S.  *)

subsection{* Definitions and basic setup *}

(* 'x \<Sigma>\<Sigma>0 consist of \<Sigma>0-terms with variables in 'x: *)
datatype_new (\<Sigma>\<Sigma>0_set: 'x) \<Sigma>\<Sigma>0 =
  \<oo>\<pp>0 "'x \<Sigma>\<Sigma>0 \<Sigma>0" | leaf0 "'x"
  for map: \<Sigma>\<Sigma>0_map rel: \<Sigma>\<Sigma>0_rel

declare \<Sigma>\<Sigma>0.ctor_fold_transfer
 [unfolded rel_pre_\<Sigma>\<Sigma>0_def id_apply BNF_Comp.id_bnf_comp_def vimage2p_def, transfer_rule]

lemma \<oo>\<pp>0_transfer[transfer_rule]: "(\<Sigma>0_rel (\<Sigma>\<Sigma>0_rel R) ===> \<Sigma>\<Sigma>0_rel R) \<oo>\<pp>0 \<oo>\<pp>0"
  by (rule rel_funI) (erule iffD2[OF \<Sigma>\<Sigma>0.rel_inject(1)])

lemma leaf0_transfer[transfer_rule]: "(R ===> \<Sigma>\<Sigma>0_rel R) leaf0 leaf0"
  by (rule rel_funI) (erule iffD2[OF \<Sigma>\<Sigma>0.rel_inject(2)])

(* The \<Sigma>\<Sigma>0 free extension, for an algebra s, of an intepretation i of the
variables into the algebra carrier:  *)
abbreviation "ext0 s \<equiv> rec_\<Sigma>\<Sigma>0 (s o \<Sigma>0_map snd)"
lemmas ext0_\<oo>\<pp>0 = \<Sigma>\<Sigma>0.rec(1)[of "s o \<Sigma>0_map snd" for s,
  unfolded o_apply \<Sigma>0.map_comp snd_convol[unfolded convol_def]]
lemmas ext0_leaf0 = \<Sigma>\<Sigma>0.rec(2)[of "s o \<Sigma>0_map snd" for s,
  unfolded o_apply \<Sigma>0.map_comp snd_convol[unfolded convol_def]]
lemmas leaf0_inj = \<Sigma>\<Sigma>0.inject(2)
lemmas \<oo>\<pp>0_inj = \<Sigma>\<Sigma>0.inject(1)

lemma ext0_alt: "ext0 s f = ctor_fold_\<Sigma>\<Sigma>0 (case_sum s f)"
  apply (rule \<Sigma>\<Sigma>0.ctor_fold_unique)
  apply (rule ext)
  apply (rename_tac x)
  apply (case_tac x)
  apply (auto simp only: rec_\<Sigma>\<Sigma>0_def \<Sigma>\<Sigma>0.ctor_rec fun_eq_iff o_apply BNF_Comp.id_bnf_comp_def
    id_def[symmetric] o_id map_pre_\<Sigma>\<Sigma>0_def id_apply map_sum.simps sum.inject sum.distinct
    \<Sigma>0.map_comp snd_convol split: sum.splits)
  done

(* The term algebra: *)

lemma \<oo>\<pp>0_def_pointfree: "\<oo>\<pp>0 = ctor_\<Sigma>\<Sigma>0 o Inl"
unfolding \<oo>\<pp>0_def BNF_Comp.id_bnf_comp_def comp_def ..

(* Monadic structure *)
lemma leaf0_def_pointfree: "leaf0 = ctor_\<Sigma>\<Sigma>0 o Inr"
unfolding leaf0_def BNF_Comp.id_bnf_comp_def comp_def ..

definition flat0 :: "('x \<Sigma>\<Sigma>0) \<Sigma>\<Sigma>0 \<Rightarrow> 'x \<Sigma>\<Sigma>0" where
  flat0_def: "flat0 \<equiv> ext0 \<oo>\<pp>0 id"

lemma flat0_transfer[transfer_rule]: "(\<Sigma>\<Sigma>0_rel (\<Sigma>\<Sigma>0_rel R) ===> \<Sigma>\<Sigma>0_rel R) flat0 flat0"
  unfolding flat0_def ext0_alt by transfer_prover

(* facts about \<Sigma>\<Sigma>0: *)
lemma ctor_fold_\<Sigma>\<Sigma>0_pointfree:
"ctor_fold_\<Sigma>\<Sigma>0 s o ctor_\<Sigma>\<Sigma>0 = s o (map_pre_\<Sigma>\<Sigma>0 id (ctor_fold_\<Sigma>\<Sigma>0 s))"
unfolding comp_def \<Sigma>\<Sigma>0.ctor_fold ..

lemma \<Sigma>\<Sigma>0_map_ctor_\<Sigma>\<Sigma>0:
"\<Sigma>\<Sigma>0_map f o ctor_\<Sigma>\<Sigma>0 = ctor_\<Sigma>\<Sigma>0 o map_sum (\<Sigma>0_map (\<Sigma>\<Sigma>0_map f)) f"
unfolding comp_def fun_eq_iff \<Sigma>\<Sigma>0.ctor_map map_pre_\<Sigma>\<Sigma>0_def BNF_Comp.id_bnf_comp_def id_apply by simp

lemma dtor_\<Sigma>\<Sigma>0_\<Sigma>\<Sigma>0_map:
"dtor_\<Sigma>\<Sigma>0 o \<Sigma>\<Sigma>0_map f = map_sum (\<Sigma>0_map (\<Sigma>\<Sigma>0_map f)) f o dtor_\<Sigma>\<Sigma>0"
using \<Sigma>\<Sigma>0_map_ctor_\<Sigma>\<Sigma>0[of f] \<Sigma>\<Sigma>0.dtor_ctor \<Sigma>\<Sigma>0.ctor_dtor unfolding comp_def fun_eq_iff by metis

lemma dtor_\<Sigma>\<Sigma>0_ctor_\<Sigma>\<Sigma>0: "dtor_\<Sigma>\<Sigma>0 \<circ> ctor_\<Sigma>\<Sigma>0 = id"
unfolding comp_def \<Sigma>\<Sigma>0.dtor_ctor id_def ..

lemma ctor_\<Sigma>\<Sigma>0_dtor_\<Sigma>\<Sigma>0: "ctor_\<Sigma>\<Sigma>0 \<circ> dtor_\<Sigma>\<Sigma>0 = id"
unfolding comp_def \<Sigma>\<Sigma>0.ctor_dtor id_def ..

lemma \<Sigma>\<Sigma>0_rel_inf: "\<Sigma>\<Sigma>0_rel (R \<sqinter> S) \<le> \<Sigma>\<Sigma>0_rel R \<sqinter> \<Sigma>\<Sigma>0_rel S"
  apply (rule inf_greatest)
  apply (rule \<Sigma>\<Sigma>0.rel_mono[OF inf_sup_ord(1)])
  apply (rule \<Sigma>\<Sigma>0.rel_mono[OF inf_sup_ord(2)])
  done

lemma \<Sigma>\<Sigma>0_rel_Grp_\<Sigma>\<Sigma>0_map: "\<Sigma>\<Sigma>0_rel (BNF_Def.Grp UNIV f) x y \<longleftrightarrow> \<Sigma>\<Sigma>0_map f x = y"
  unfolding \<Sigma>\<Sigma>0.rel_Grp by (auto simp: Grp_def)

lemma \<Sigma>\<Sigma>0_rel_\<Sigma>\<Sigma>0_map_\<Sigma>\<Sigma>0_map: "\<Sigma>\<Sigma>0_rel R (\<Sigma>\<Sigma>0_map f x) (\<Sigma>\<Sigma>0_map g y) =
  \<Sigma>\<Sigma>0_rel (BNF_Def.vimage2p f g R) x y"
  unfolding \<Sigma>\<Sigma>0.rel_Grp vimage2p_Grp apply (auto simp: \<Sigma>\<Sigma>0.rel_compp \<Sigma>\<Sigma>0.rel_conversep relcompp.simps)
  apply (intro exI conjI)
  apply (rule iffD2[OF \<Sigma>\<Sigma>0_rel_Grp_\<Sigma>\<Sigma>0_map refl])
  apply assumption
  apply (rule iffD2[OF \<Sigma>\<Sigma>0_rel_Grp_\<Sigma>\<Sigma>0_map refl])
  unfolding \<Sigma>\<Sigma>0_rel_Grp_\<Sigma>\<Sigma>0_map
  apply simp
  done

subsection{* @{term \<Sigma>0} extension theorems *}

theorem ext0_commute:
"ext0 s i o \<oo>\<pp>0 = s o \<Sigma>0_map (ext0 s i)"
unfolding ext0_alt \<oo>\<pp>0_def_pointfree o_assoc ctor_fold_\<Sigma>\<Sigma>0_pointfree map_pre_\<Sigma>\<Sigma>0_def
  case_sum_o_map_sum case_sum_o_inj(1) BNF_Comp.id_bnf_comp_def id_def[symmetric] o_id ..

theorem ext0_comp_leaf0:
"ext0 s i o leaf0 = i"
unfolding ext0_alt leaf0_def_pointfree o_assoc ctor_fold_\<Sigma>\<Sigma>0_pointfree map_pre_\<Sigma>\<Sigma>0_def
  case_sum_o_map_sum case_sum_o_inj(2) id_apply BNF_Comp.id_bnf_comp_def id_def[symmetric] o_id ..

theorem ext0_unique:
assumes leaf0: "f o leaf0 = i" and com: "f o \<oo>\<pp>0 = s o \<Sigma>0_map f"
shows "f = ext0 s i"
unfolding ext0_alt
apply (rule \<Sigma>\<Sigma>0.ctor_fold_unique)
apply (rule sum_comp_cases)
unfolding map_pre_\<Sigma>\<Sigma>0_def case_sum_o_map_sum id_apply o_id case_sum_o_inj
  leaf0[unfolded leaf0_def_pointfree o_assoc] com[unfolded \<oo>\<pp>0_def_pointfree o_assoc]
  BNF_Comp.id_bnf_comp_def id_def[symmetric] id_o
by (rule refl)+


(* We have shown that the functions
ext0 s and \<lambda> f. f o leaf0 form flattually inverse bijections
between functions i :: 'x \<Rightarrow> 'a (where 'a is the carrier of the algebra s)
and algebra morphisms f : ('x \<Sigma>\<Sigma>0, \<oo>\<pp>0) \<rightarrow> ('a, s)
*)


subsection{* Customizing @{term \<Sigma>\<Sigma>0} *}

subsection{* Injectiveness, naturality, adjunction *}

theorem leaf0_natural: "\<Sigma>\<Sigma>0_map f o leaf0 = leaf0 o f"
  using leaf0_transfer[of "BNF_Def.Grp UNIV f"]
  unfolding \<Sigma>\<Sigma>0.rel_Grp
  unfolding Grp_def rel_fun_def by auto

lemma \<oo>\<pp>0_natural: "\<oo>\<pp>0 o \<Sigma>0_map (\<Sigma>\<Sigma>0_map f) = \<Sigma>\<Sigma>0_map f o \<oo>\<pp>0"
  using \<oo>\<pp>0_transfer[of "BNF_Def.Grp UNIV f"]
  unfolding \<Sigma>0.rel_Grp \<Sigma>\<Sigma>0.rel_Grp
  unfolding Grp_def rel_fun_def by auto

lemma \<Sigma>\<Sigma>0_map_def2: "\<Sigma>\<Sigma>0_map i = ext0 \<oo>\<pp>0 (leaf0 o i)"
by (rule ext0_unique[OF leaf0_natural \<oo>\<pp>0_natural[symmetric]])

lemma ext0_\<oo>\<pp>0_leaf0: "ext0 \<oo>\<pp>0 leaf0 = id"
apply (rule ext0_unique[symmetric]) unfolding \<Sigma>0.map_id0 o_id id_o by (rule refl)+

lemma ext0_\<Sigma>\<Sigma>0_map:
"ext0 s (j o f) = ext0 s j o \<Sigma>\<Sigma>0_map f"
proof (rule ext0_unique[symmetric])
  show "ext0 s j \<circ> \<Sigma>\<Sigma>0_map f \<circ> leaf0 = j \<circ> f"
  unfolding o_assoc[symmetric] leaf0_natural
  unfolding o_assoc ext0_comp_leaf0 ..
next
  show "ext0 s j \<circ> \<Sigma>\<Sigma>0_map f \<circ> \<oo>\<pp>0 = s \<circ> \<Sigma>0_map (ext0 s j \<circ> \<Sigma>\<Sigma>0_map f)"
  unfolding o_assoc[symmetric] \<oo>\<pp>0_natural[symmetric]
  unfolding o_assoc ext0_commute
  unfolding o_assoc[symmetric] \<Sigma>0.map_comp0 ..
qed

lemma ext0_\<Sigma>0_map:
assumes "t o \<Sigma>0_map f = f o s"
shows "ext0 t (f o i) = f o ext0 s i"
proof (rule ext0_unique[symmetric])
  show "f \<circ> ext0 s i \<circ> leaf0 = f o i"
  unfolding o_assoc[symmetric] ext0_comp_leaf0 ..
next
  show "f \<circ> ext0 s i \<circ> \<oo>\<pp>0 = t \<circ> \<Sigma>0_map (f \<circ> ext0 s i)"
  unfolding \<Sigma>0.map_comp0 o_assoc assms
  unfolding o_assoc[symmetric] ext0_commute[symmetric] ..
qed


subsection{* Monadic laws *}

lemma flat0_commute: "\<oo>\<pp>0 \<circ> \<Sigma>0_map flat0 = flat0 \<circ> \<oo>\<pp>0"
unfolding flat0_def ext0_commute ..

(* \<Sigma>\<Sigma>0 2 identity laws*)
theorem flat0_leaf0: "flat0 o leaf0 = id"
unfolding flat0_def ext0_comp_leaf0 ..

theorem leaf0_flat0: "flat0 o \<Sigma>\<Sigma>0_map leaf0 = id"
unfolding flat0_def ext0_\<Sigma>\<Sigma>0_map[symmetric] id_o ext0_\<oo>\<pp>0_leaf0 ..

theorem flat0_natural: "flat0 o \<Sigma>\<Sigma>0_map (\<Sigma>\<Sigma>0_map i) = \<Sigma>\<Sigma>0_map i o flat0"
  using flat0_transfer[of "BNF_Def.Grp UNIV i"]
  unfolding \<Sigma>\<Sigma>0.rel_Grp
  unfolding Grp_def rel_fun_def by auto

(* Associativity *)
theorem flat0_assoc: "flat0 o \<Sigma>\<Sigma>0_map flat0 = flat0 o flat0"
unfolding flat0_def unfolding ext0_\<Sigma>\<Sigma>0_map[symmetric] id_o
proof(rule ext0_unique[symmetric], unfold flat0_def[symmetric])
  show "flat0 \<circ> flat0 \<circ> leaf0 = flat0"
  unfolding o_assoc[symmetric] flat0_leaf0 by simp
next
  show "flat0 \<circ> flat0 \<circ> \<oo>\<pp>0 = \<oo>\<pp>0 \<circ> \<Sigma>0_map (flat0 \<circ> flat0)"
  unfolding flat0_def unfolding o_assoc[symmetric] ext0_commute
  unfolding flat0_def[symmetric]
  unfolding \<Sigma>0.map_comp0 o_assoc unfolding flat0_commute ..
qed

end
