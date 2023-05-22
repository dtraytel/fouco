header{* The initial free algebra for bootstrapping, for a copy of the behavior BNF *}

theory FreeAlg_base
imports Behavior_BNF
begin

(* Initially, the signature functor and the behavior functor coincide: \<Sigma>_base = (a copy of) F
This corresponds to corecursion with any > 0 number of guards. *)

typedef 'a \<Sigma>_base = "UNIV :: 'a F set" by (rule UNIV_witness)

setup_lifting type_definition_\<Sigma>_base

lift_definition \<Sigma>_base_map :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Sigma>_base \<Rightarrow> 'b \<Sigma>_base" is F_map .
lift_definition \<Sigma>_base_set :: "'a \<Sigma>_base \<Rightarrow> 'a set" is F_set .
lift_definition \<Sigma>_base_rel :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a \<Sigma>_base \<Rightarrow> 'b \<Sigma>_base \<Rightarrow> bool" is F_rel .

typedef \<Sigma>_base_bd_type = "UNIV :: bd_type_F set" by (rule UNIV_witness)
definition "\<Sigma>_base_bd = dir_image F_bd Abs_\<Sigma>_base_bd_type"

bnf "'a \<Sigma>_base"
  map: \<Sigma>_base_map
  sets: \<Sigma>_base_set
  bd: \<Sigma>_base_bd
  rel: \<Sigma>_base_rel
unfolding \<Sigma>_base_bd_def
apply -
apply transfer apply (rule pre_J.map_id0)
apply transfer apply (rule pre_J.map_comp0)
apply transfer apply (erule pre_J.map_cong0)
apply transfer apply (rule pre_J.set_map0)
apply (rule card_order_dir_image[OF bijI pre_J.bd_card_order])
apply (metis inj_on_def Abs_\<Sigma>_base_bd_type_inverse[OF UNIV_I])
apply (metis surj_def Abs_\<Sigma>_base_bd_type_cases)
apply (rule conjunct1[OF Cinfinite_cong[OF dir_image[OF _ pre_J.bd_Card_order] pre_J.bd_Cinfinite]])
apply (metis Abs_\<Sigma>_base_bd_type_inverse[OF UNIV_I])
apply (unfold \<Sigma>_base_set_def map_fun_def id_o) [1] apply (subst o_apply)
apply (rule ordLeq_ordIso_trans[OF pre_J.set_bd dir_image[OF _ pre_J.bd_Card_order]])
apply (metis Abs_\<Sigma>_base_bd_type_inverse[OF UNIV_I])
apply (rule predicate2I) apply transfer apply (subst pre_J.rel_compp) apply assumption
apply transfer' apply (rule pre_J.rel_compp_Grp)
done

declare \<Sigma>_base.map_transfer[transfer_rule]

lemma Rep_\<Sigma>_base_transfer[transfer_rule]: "(\<Sigma>_base_rel R ===> F_rel R) Rep_\<Sigma>_base Rep_\<Sigma>_base"
  unfolding rel_fun_def by transfer blast

lemma Abs_\<Sigma>_base_transfer[transfer_rule]: "(F_rel R ===> \<Sigma>_base_rel R) Abs_\<Sigma>_base Abs_\<Sigma>_base"
  unfolding rel_fun_def by transfer blast

theorem Rep_\<Sigma>_base_natural: "F_map f o Rep_\<Sigma>_base = Rep_\<Sigma>_base o \<Sigma>_base_map f"
  using Rep_\<Sigma>_base_transfer[of "BNF_Def.Grp UNIV f"]
  unfolding \<Sigma>_base.rel_Grp F_rel_Grp
  unfolding Grp_def rel_fun_def by auto

theorem Abs_\<Sigma>_base_natural: "\<Sigma>_base_map f o Abs_\<Sigma>_base = Abs_\<Sigma>_base o F_map f"
  using Abs_\<Sigma>_base_transfer[of "BNF_Def.Grp UNIV f"]
  unfolding \<Sigma>_base.rel_Grp F_rel_Grp
  unfolding Grp_def rel_fun_def by auto

lemma Rep_\<Sigma>_base_o_Abs_\<Sigma>_base: "Rep_\<Sigma>_base o Abs_\<Sigma>_base = id"
  apply (rule ext)
  apply (rule box_equals[OF _ o_apply[symmetric] id_apply[symmetric]])
  apply (rule Abs_\<Sigma>_base_inverse[OF UNIV_I])
  done

lemma \<Sigma>_base_rel_\<Sigma>_base_map_\<Sigma>_base_map:
  "\<Sigma>_base_rel R (\<Sigma>_base_map f x) (\<Sigma>_base_map g y) = \<Sigma>_base_rel (BNF_Def.vimage2p f g R) x y"
  unfolding \<Sigma>_base.rel_Grp vimage2p_Grp \<Sigma>_base.rel_compp \<Sigma>_base.rel_conversep
  unfolding relcompp.simps Grp_def by blast

(* \<Sigma>\<Sigma>_base is a copy of FreeAlg, but imports Behavior_BNF instead of Signature_BNF,
menaing that it uses a specific \<Sigma>_base which is a copy of F, instead of S.  *)

subsection{* Definitions and basic setup *}

(* 'x \<Sigma>\<Sigma>_base consist of \<Sigma>_base-terms with variables in 'x: *)
datatype_new (\<Sigma>\<Sigma>_base_set: 'x) \<Sigma>\<Sigma>_base =
  \<oo>\<pp>_base "'x \<Sigma>\<Sigma>_base \<Sigma>_base" | leaf_base "'x"
  for map: \<Sigma>\<Sigma>_base_map rel: \<Sigma>\<Sigma>_base_rel

declare \<Sigma>\<Sigma>_base.ctor_fold_transfer
 [unfolded rel_pre_\<Sigma>\<Sigma>_base_def id_apply BNF_Comp.id_bnf_comp_def vimage2p_def, transfer_rule]

lemma \<oo>\<pp>_base_transfer[transfer_rule]: "(\<Sigma>_base_rel (\<Sigma>\<Sigma>_base_rel R) ===> \<Sigma>\<Sigma>_base_rel R) \<oo>\<pp>_base \<oo>\<pp>_base"
  by (rule rel_funI) (erule iffD2[OF \<Sigma>\<Sigma>_base.rel_inject(1)])

lemma leaf_base_transfer[transfer_rule]: "(R ===> \<Sigma>\<Sigma>_base_rel R) leaf_base leaf_base"
  by (rule rel_funI) (erule iffD2[OF \<Sigma>\<Sigma>_base.rel_inject(2)])

(* The \<Sigma>\<Sigma>_base free extension, for an algebra s, of an intepretation i of the
variables into the algebra carrier:  *)
abbreviation "ext_base s \<equiv> rec_\<Sigma>\<Sigma>_base (s o \<Sigma>_base_map snd)"
lemmas ext_base_\<oo>\<pp>_base = \<Sigma>\<Sigma>_base.rec(1)[of "s o \<Sigma>_base_map snd" for s,
  unfolded o_apply \<Sigma>_base.map_comp snd_convol[unfolded convol_def]]
lemmas ext_base_leaf_base = \<Sigma>\<Sigma>_base.rec(2)[of "s o \<Sigma>_base_map snd" for s,
  unfolded o_apply \<Sigma>_base.map_comp snd_convol[unfolded convol_def]]
lemmas leaf_base_inj = \<Sigma>\<Sigma>_base.inject(2)
lemmas \<oo>\<pp>_base_inj = \<Sigma>\<Sigma>_base.inject(1)

lemma ext_base_alt: "ext_base s f = ctor_fold_\<Sigma>\<Sigma>_base (case_sum s f)"
  apply (rule \<Sigma>\<Sigma>_base.ctor_fold_unique)
  apply (rule ext)
  apply (rename_tac x)
  apply (case_tac x)
  apply (auto simp only: rec_\<Sigma>\<Sigma>_base_def \<Sigma>\<Sigma>_base.ctor_rec fun_eq_iff o_apply BNF_Comp.id_bnf_comp_def
    id_def[symmetric] o_id map_pre_\<Sigma>\<Sigma>_base_def id_apply map_sum.simps sum.inject sum.distinct
    \<Sigma>_base.map_comp snd_convol split: sum.splits)
  done

(* The term algebra: *)

lemma \<oo>\<pp>_base_def_pointfree: "\<oo>\<pp>_base = ctor_\<Sigma>\<Sigma>_base o Inl"
unfolding \<oo>\<pp>_base_def BNF_Comp.id_bnf_comp_def comp_def ..

(* Monadic structure *)
lemma leaf_base_def_pointfree: "leaf_base = ctor_\<Sigma>\<Sigma>_base o Inr"
unfolding leaf_base_def BNF_Comp.id_bnf_comp_def comp_def ..

definition flat_base :: "('x \<Sigma>\<Sigma>_base) \<Sigma>\<Sigma>_base \<Rightarrow> 'x \<Sigma>\<Sigma>_base" where
  flat_base_def: "flat_base \<equiv> ext_base \<oo>\<pp>_base id"

lemma flat_base_transfer[transfer_rule]: "(\<Sigma>\<Sigma>_base_rel (\<Sigma>\<Sigma>_base_rel R) ===> \<Sigma>\<Sigma>_base_rel R) flat_base flat_base"
  unfolding flat_base_def ext_base_alt by transfer_prover

(* facts about \<Sigma>\<Sigma>_base: *)
lemma ctor_fold_\<Sigma>\<Sigma>_base_pointfree:
"ctor_fold_\<Sigma>\<Sigma>_base s o ctor_\<Sigma>\<Sigma>_base = s o (map_pre_\<Sigma>\<Sigma>_base id (ctor_fold_\<Sigma>\<Sigma>_base s))"
unfolding comp_def \<Sigma>\<Sigma>_base.ctor_fold ..

lemma \<Sigma>\<Sigma>_base_map_ctor_\<Sigma>\<Sigma>_base:
"\<Sigma>\<Sigma>_base_map f o ctor_\<Sigma>\<Sigma>_base = ctor_\<Sigma>\<Sigma>_base o map_sum (\<Sigma>_base_map (\<Sigma>\<Sigma>_base_map f)) f"
unfolding comp_def fun_eq_iff \<Sigma>\<Sigma>_base.ctor_map map_pre_\<Sigma>\<Sigma>_base_def BNF_Comp.id_bnf_comp_def id_apply by simp

lemma dtor_\<Sigma>\<Sigma>_base_\<Sigma>\<Sigma>_base_map:
"dtor_\<Sigma>\<Sigma>_base o \<Sigma>\<Sigma>_base_map f = map_sum (\<Sigma>_base_map (\<Sigma>\<Sigma>_base_map f)) f o dtor_\<Sigma>\<Sigma>_base"
using \<Sigma>\<Sigma>_base_map_ctor_\<Sigma>\<Sigma>_base[of f] \<Sigma>\<Sigma>_base.dtor_ctor \<Sigma>\<Sigma>_base.ctor_dtor unfolding comp_def fun_eq_iff by metis

lemma dtor_\<Sigma>\<Sigma>_base_ctor_\<Sigma>\<Sigma>_base: "dtor_\<Sigma>\<Sigma>_base \<circ> ctor_\<Sigma>\<Sigma>_base = id"
unfolding comp_def \<Sigma>\<Sigma>_base.dtor_ctor id_def ..

lemma ctor_\<Sigma>\<Sigma>_base_dtor_\<Sigma>\<Sigma>_base: "ctor_\<Sigma>\<Sigma>_base \<circ> dtor_\<Sigma>\<Sigma>_base = id"
unfolding comp_def \<Sigma>\<Sigma>_base.ctor_dtor id_def ..

lemma \<Sigma>\<Sigma>_base_rel_inf: "\<Sigma>\<Sigma>_base_rel (R \<sqinter> S) \<le> \<Sigma>\<Sigma>_base_rel R \<sqinter> \<Sigma>\<Sigma>_base_rel S"
  apply (rule inf_greatest)
  apply (rule \<Sigma>\<Sigma>_base.rel_mono[OF inf_sup_ord(1)])
  apply (rule \<Sigma>\<Sigma>_base.rel_mono[OF inf_sup_ord(2)])
  done

lemma \<Sigma>\<Sigma>_base_rel_Grp_\<Sigma>\<Sigma>_base_map: "\<Sigma>\<Sigma>_base_rel (BNF_Def.Grp UNIV f) x y \<longleftrightarrow> \<Sigma>\<Sigma>_base_map f x = y"
  unfolding \<Sigma>\<Sigma>_base.rel_Grp by (auto simp: Grp_def)

lemma \<Sigma>\<Sigma>_base_rel_\<Sigma>\<Sigma>_base_map_\<Sigma>\<Sigma>_base_map: "\<Sigma>\<Sigma>_base_rel R (\<Sigma>\<Sigma>_base_map f x) (\<Sigma>\<Sigma>_base_map g y) =
  \<Sigma>\<Sigma>_base_rel (BNF_Def.vimage2p f g R) x y"
  unfolding \<Sigma>\<Sigma>_base.rel_Grp vimage2p_Grp apply (auto simp: \<Sigma>\<Sigma>_base.rel_compp \<Sigma>\<Sigma>_base.rel_conversep relcompp.simps)
  apply (intro exI conjI)
  apply (rule iffD2[OF \<Sigma>\<Sigma>_base_rel_Grp_\<Sigma>\<Sigma>_base_map refl])
  apply assumption
  apply (rule iffD2[OF \<Sigma>\<Sigma>_base_rel_Grp_\<Sigma>\<Sigma>_base_map refl])
  unfolding \<Sigma>\<Sigma>_base_rel_Grp_\<Sigma>\<Sigma>_base_map
  apply simp
  done

subsection{* @{term \<Sigma>_base} extension theorems *}

theorem ext_base_commute:
"ext_base s i o \<oo>\<pp>_base = s o \<Sigma>_base_map (ext_base s i)"
unfolding ext_base_alt \<oo>\<pp>_base_def_pointfree o_assoc ctor_fold_\<Sigma>\<Sigma>_base_pointfree map_pre_\<Sigma>\<Sigma>_base_def
  case_sum_o_map_sum case_sum_o_inj(1) BNF_Comp.id_bnf_comp_def id_def[symmetric] o_id ..

theorem ext_base_comp_leaf_base:
"ext_base s i o leaf_base = i"
unfolding ext_base_alt leaf_base_def_pointfree o_assoc ctor_fold_\<Sigma>\<Sigma>_base_pointfree map_pre_\<Sigma>\<Sigma>_base_def
  case_sum_o_map_sum case_sum_o_inj(2) id_apply BNF_Comp.id_bnf_comp_def id_def[symmetric] o_id ..

theorem ext_base_unique:
assumes leaf_base: "f o leaf_base = i" and com: "f o \<oo>\<pp>_base = s o \<Sigma>_base_map f"
shows "f = ext_base s i"
unfolding ext_base_alt
apply (rule \<Sigma>\<Sigma>_base.ctor_fold_unique)
apply (rule sum_comp_cases)
unfolding map_pre_\<Sigma>\<Sigma>_base_def case_sum_o_map_sum id_apply o_id case_sum_o_inj
  leaf_base[unfolded leaf_base_def_pointfree o_assoc] com[unfolded \<oo>\<pp>_base_def_pointfree o_assoc]
  BNF_Comp.id_bnf_comp_def id_def[symmetric] id_o
by (rule refl)+


(* We have shown that the functions
ext_base s and \<lambda> f. f o leaf_base form flattually inverse bijections
between functions i :: 'x \<Rightarrow> 'a (where 'a is the carrier of the algebra s)
and algebra morphisms f : ('x \<Sigma>\<Sigma>_base, \<oo>\<pp>_base) \<rightarrow> ('a, s)
*)


subsection{* Customizing @{term \<Sigma>\<Sigma>_base} *}

subsection{* Injectiveness, naturality, adjunction *}

theorem leaf_base_natural: "\<Sigma>\<Sigma>_base_map f o leaf_base = leaf_base o f"
  using leaf_base_transfer[of "BNF_Def.Grp UNIV f"]
  unfolding \<Sigma>\<Sigma>_base.rel_Grp
  unfolding Grp_def rel_fun_def by auto

lemma \<oo>\<pp>_base_natural: "\<oo>\<pp>_base o \<Sigma>_base_map (\<Sigma>\<Sigma>_base_map f) = \<Sigma>\<Sigma>_base_map f o \<oo>\<pp>_base"
  using \<oo>\<pp>_base_transfer[of "BNF_Def.Grp UNIV f"]
  unfolding \<Sigma>_base.rel_Grp \<Sigma>\<Sigma>_base.rel_Grp
  unfolding Grp_def rel_fun_def by auto

lemma \<Sigma>\<Sigma>_base_map_def2: "\<Sigma>\<Sigma>_base_map i = ext_base \<oo>\<pp>_base (leaf_base o i)"
by (rule ext_base_unique[OF leaf_base_natural \<oo>\<pp>_base_natural[symmetric]])

lemma ext_base_\<oo>\<pp>_base_leaf_base: "ext_base \<oo>\<pp>_base leaf_base = id"
apply (rule ext_base_unique[symmetric]) unfolding \<Sigma>_base.map_id0 o_id id_o by (rule refl)+

lemma ext_base_\<Sigma>\<Sigma>_base_map:
"ext_base s (j o f) = ext_base s j o \<Sigma>\<Sigma>_base_map f"
proof (rule ext_base_unique[symmetric])
  show "ext_base s j \<circ> \<Sigma>\<Sigma>_base_map f \<circ> leaf_base = j \<circ> f"
  unfolding o_assoc[symmetric] leaf_base_natural
  unfolding o_assoc ext_base_comp_leaf_base ..
next
  show "ext_base s j \<circ> \<Sigma>\<Sigma>_base_map f \<circ> \<oo>\<pp>_base = s \<circ> \<Sigma>_base_map (ext_base s j \<circ> \<Sigma>\<Sigma>_base_map f)"
  unfolding o_assoc[symmetric] \<oo>\<pp>_base_natural[symmetric]
  unfolding o_assoc ext_base_commute
  unfolding o_assoc[symmetric] \<Sigma>_base.map_comp0 ..
qed

lemma ext_base_\<Sigma>_base_map:
assumes "t o \<Sigma>_base_map f = f o s"
shows "ext_base t (f o i) = f o ext_base s i"
proof (rule ext_base_unique[symmetric])
  show "f \<circ> ext_base s i \<circ> leaf_base = f o i"
  unfolding o_assoc[symmetric] ext_base_comp_leaf_base ..
next
  show "f \<circ> ext_base s i \<circ> \<oo>\<pp>_base = t \<circ> \<Sigma>_base_map (f \<circ> ext_base s i)"
  unfolding \<Sigma>_base.map_comp0 o_assoc assms
  unfolding o_assoc[symmetric] ext_base_commute[symmetric] ..
qed


subsection{* Monadic laws *}

lemma flat_base_commute: "\<oo>\<pp>_base \<circ> \<Sigma>_base_map flat_base = flat_base \<circ> \<oo>\<pp>_base"
unfolding flat_base_def ext_base_commute ..

(* \<Sigma>\<Sigma>_base 2 identity laws*)
theorem flat_base_leaf_base: "flat_base o leaf_base = id"
unfolding flat_base_def ext_base_comp_leaf_base ..

theorem leaf_base_flat_base: "flat_base o \<Sigma>\<Sigma>_base_map leaf_base = id"
unfolding flat_base_def ext_base_\<Sigma>\<Sigma>_base_map[symmetric] id_o ext_base_\<oo>\<pp>_base_leaf_base ..

theorem flat_base_natural: "flat_base o \<Sigma>\<Sigma>_base_map (\<Sigma>\<Sigma>_base_map i) = \<Sigma>\<Sigma>_base_map i o flat_base"
  using flat_base_transfer[of "BNF_Def.Grp UNIV i"]
  unfolding \<Sigma>\<Sigma>_base.rel_Grp
  unfolding Grp_def rel_fun_def by auto

(* Associativity *)
theorem flat_base_assoc: "flat_base o \<Sigma>\<Sigma>_base_map flat_base = flat_base o flat_base"
unfolding flat_base_def unfolding ext_base_\<Sigma>\<Sigma>_base_map[symmetric] id_o
proof(rule ext_base_unique[symmetric], unfold flat_base_def[symmetric])
  show "flat_base \<circ> flat_base \<circ> leaf_base = flat_base"
  unfolding o_assoc[symmetric] flat_base_leaf_base by simp
next
  show "flat_base \<circ> flat_base \<circ> \<oo>\<pp>_base = \<oo>\<pp>_base \<circ> \<Sigma>_base_map (flat_base \<circ> flat_base)"
  unfolding flat_base_def unfolding o_assoc[symmetric] ext_base_commute
  unfolding flat_base_def[symmetric]
  unfolding \<Sigma>_base.map_comp0 o_assoc unfolding flat_base_commute ..
qed

end
