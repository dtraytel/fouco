header{* Free algebras for an BNF *}

(* Free algebra constructed for a sum of two BNF's S and K: *)
(* Notations: Identical to FreeAlg, just that constants and types are suffixed by "step" instead of "base": *)

theory Binary_Tree_FreeAlg1
imports Binary_Tree_Input1
begin

declare K1.map_transfer[transfer_rule]

(* The new-operation functor: *)

composition_bnf (open) raw_\<Sigma>1: "'a \<Sigma>0 + 'a K1"
typedef 'a \<Sigma>1 = "UNIV :: ('a \<Sigma>0 + 'a K1) set" by (rule UNIV_witness)

setup_lifting type_definition_\<Sigma>1

lift_definition \<Sigma>1_map :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Sigma>1 \<Rightarrow> 'b \<Sigma>1" is "\<lambda>f. map_sum (\<Sigma>0_map f) (K1_map f)" .
lift_definition \<Sigma>1_set :: "'a \<Sigma>1 \<Rightarrow> 'a set"
  is "\<lambda>x. UNION (Basic_BNFs.setl x) \<Sigma>0_set \<union> UNION (Basic_BNFs.setr x) K1_set" .
lift_definition \<Sigma>1_rel :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a \<Sigma>1 \<Rightarrow> 'b \<Sigma>1 \<Rightarrow> bool"
  is "\<lambda>R. rel_sum (\<Sigma>0_rel R) (K1_rel R)" .
typedef \<Sigma>1_bd_type = "UNIV :: ((\<Sigma>0_bd_type + bd_type_K1) \<times> nat) set" by (rule UNIV_witness)
definition "\<Sigma>1_bd = dir_image ((\<Sigma>0_bd +c bd_K1) *c natLeq) Abs_\<Sigma>1_bd_type"

bnf "'a \<Sigma>1"
  map: \<Sigma>1_map
  sets: \<Sigma>1_set
  bd: \<Sigma>1_bd 
  rel: \<Sigma>1_rel
unfolding \<Sigma>1_bd_def
apply -
apply transfer apply (rule raw_\<Sigma>1.map_id0)
apply transfer apply (rule raw_\<Sigma>1.map_comp0)
apply transfer apply (erule raw_\<Sigma>1.map_cong0)
apply transfer apply (rule raw_\<Sigma>1.set_map0)
apply (rule card_order_dir_image[OF bijI raw_\<Sigma>1.bd_card_order])
apply (metis inj_on_def Abs_\<Sigma>1_bd_type_inverse[OF UNIV_I])
apply (metis surj_def Abs_\<Sigma>1_bd_type_cases)
apply (rule conjunct1[OF Cinfinite_cong[OF dir_image[OF _ raw_\<Sigma>1.bd_Card_order] raw_\<Sigma>1.bd_Cinfinite]])
apply (metis Abs_\<Sigma>1_bd_type_inverse[OF UNIV_I])
apply (unfold \<Sigma>1_set_def map_fun_def id_o) [1] apply (subst o_apply)
apply (rule ordLeq_ordIso_trans[OF raw_\<Sigma>1.set_bd dir_image[OF _ raw_\<Sigma>1.bd_Card_order]])
apply (metis Abs_\<Sigma>1_bd_type_inverse[OF UNIV_I])
apply (rule predicate2I) apply transfer apply (subst raw_\<Sigma>1.rel_compp) apply assumption
apply transfer' apply (rule raw_\<Sigma>1.rel_compp_Grp)
done

declare \<Sigma>1.map_transfer[transfer_rule]

lemma Rep_\<Sigma>1_transfer[transfer_rule]: "(\<Sigma>1_rel R ===> rel_sum (\<Sigma>0_rel R) (K1_rel R)) Rep_\<Sigma>1 Rep_\<Sigma>1"
  unfolding rel_fun_def by transfer blast

lemma Abs_\<Sigma>1_transfer[transfer_rule]: "(rel_sum (\<Sigma>0_rel R) (K1_rel R) ===> \<Sigma>1_rel R) Abs_\<Sigma>1 Abs_\<Sigma>1"
  unfolding rel_fun_def by transfer blast

theorem Rep_\<Sigma>1_natural: "map_sum (\<Sigma>0_map f) (K1_map f) o Rep_\<Sigma>1 = Rep_\<Sigma>1 o \<Sigma>1_map f"
  using Rep_\<Sigma>1_transfer[of "BNF_Def.Grp UNIV f"]
  unfolding \<Sigma>1.rel_Grp raw_\<Sigma>1.rel_Grp
  unfolding Grp_def rel_fun_def by auto

theorem Abs_\<Sigma>1_natural: "\<Sigma>1_map f o Abs_\<Sigma>1 = Abs_\<Sigma>1 o map_sum (\<Sigma>0_map f) (K1_map f)"
  using Abs_\<Sigma>1_transfer[of "BNF_Def.Grp UNIV f"]
  unfolding \<Sigma>1.rel_Grp raw_\<Sigma>1.rel_Grp
  unfolding Grp_def rel_fun_def by auto

lemma Rep_\<Sigma>1_o_Abs_\<Sigma>1: "Rep_\<Sigma>1 o Abs_\<Sigma>1 = id"
  apply (rule ext)
  apply (rule box_equals[OF _ o_apply[symmetric] id_apply[symmetric]])
  apply (rule Abs_\<Sigma>1_inverse[OF UNIV_I])
  done

lemma \<Sigma>1_rel_\<Sigma>1_map_\<Sigma>1_map:
  "\<Sigma>1_rel R (\<Sigma>1_map f x) (\<Sigma>1_map g y) = \<Sigma>1_rel (BNF_Def.vimage2p f g R) x y"
  unfolding \<Sigma>1.rel_Grp vimage2p_Grp \<Sigma>1.rel_compp \<Sigma>1.rel_conversep
  unfolding relcompp.simps Grp_def by simp

subsection{* Definitions and basic setup *}

(* 'x \<Sigma>\<Sigma>1 consist of \<Sigma>1-terms with variables in 'x: *)
datatype_new (\<Sigma>\<Sigma>1_set: 'x) \<Sigma>\<Sigma>1 =
  \<oo>\<pp>1 "'x \<Sigma>\<Sigma>1 \<Sigma>1" | leaf1 "'x"
  for map: \<Sigma>\<Sigma>1_map rel: \<Sigma>\<Sigma>1_rel
declare \<Sigma>\<Sigma>1.ctor_fold_transfer
  [unfolded rel_pre_\<Sigma>\<Sigma>1_def id_apply BNF_Comp.id_bnf_comp_def vimage2p_def, transfer_rule]

lemma \<oo>\<pp>1_transfer[transfer_rule]:
  "(\<Sigma>1_rel (\<Sigma>\<Sigma>1_rel R) ===> \<Sigma>\<Sigma>1_rel R) \<oo>\<pp>1 \<oo>\<pp>1"
  by (rule rel_funI) (erule iffD2[OF \<Sigma>\<Sigma>1.rel_inject(1)])

lemma leaf1_transfer[transfer_rule]: "(R ===> \<Sigma>\<Sigma>1_rel R) leaf1 leaf1"
  by (rule rel_funI) (erule iffD2[OF \<Sigma>\<Sigma>1.rel_inject(2)])

(* The free extension, for an algebra s, of an inteprleaftion i of the
variables into the algebra carrier:  *)
abbreviation "ext1 s \<equiv> rec_\<Sigma>\<Sigma>1 (s o \<Sigma>1_map snd)"
lemmas ext1_\<oo>\<pp>1 = \<Sigma>\<Sigma>1.rec(1)[of "s o \<Sigma>1_map snd" for s,
  unfolded o_apply \<Sigma>1.map_comp snd_convol[unfolded convol_def]]
lemmas ext1_leaf1 = \<Sigma>\<Sigma>1.rec(2)[of "s o \<Sigma>1_map snd" for s,
  unfolded o_apply \<Sigma>1.map_comp snd_convol[unfolded convol_def]]
lemmas leaf1_inj = \<Sigma>\<Sigma>1.inject(2)
lemmas \<oo>\<pp>1_inj = \<Sigma>\<Sigma>1.inject(1)

lemma ext1_alt: "ext1 s f = ctor_fold_\<Sigma>\<Sigma>1 (case_sum s f)"
  apply (rule \<Sigma>\<Sigma>1.ctor_fold_unique)
  apply (rule ext)
  apply (rename_tac x)
  apply (case_tac x)
  apply (auto simp only: rec_\<Sigma>\<Sigma>1_def \<Sigma>\<Sigma>1.ctor_rec fun_eq_iff o_apply BNF_Comp.id_bnf_comp_def
    id_def[symmetric] o_id map_pre_\<Sigma>\<Sigma>1_def id_apply map_sum.simps sum.inject sum.distinct
    \<Sigma>1.map_comp snd_convol split: sum.splits)
  done

(* The term algebra: *)

lemma \<oo>\<pp>1_def_pointfree: "\<oo>\<pp>1 \<equiv> ctor_\<Sigma>\<Sigma>1 o Inl"
unfolding \<oo>\<pp>1_def comp_def BNF_Comp.id_bnf_comp_def .

(* Monadic structure *)
lemma leaf1_def_pointfree: "leaf1 \<equiv> ctor_\<Sigma>\<Sigma>1 o Inr"
unfolding leaf1_def comp_def BNF_Comp.id_bnf_comp_def .

definition flat1 :: "('x \<Sigma>\<Sigma>1) \<Sigma>\<Sigma>1 \<Rightarrow> 'x \<Sigma>\<Sigma>1" where
  flat1_def: "flat1 \<equiv> ext1 \<oo>\<pp>1 id"

lemma flat1_transfer[transfer_rule]: "(\<Sigma>\<Sigma>1_rel (\<Sigma>\<Sigma>1_rel R) ===> \<Sigma>\<Sigma>1_rel R) flat1 flat1"
  unfolding flat1_def ext1_alt by transfer_prover

(* facts about \<Sigma>\<Sigma>1: *)
lemma ctor_fold_\<Sigma>\<Sigma>1_pointfree:
"ctor_fold_\<Sigma>\<Sigma>1 s o ctor_\<Sigma>\<Sigma>1 = s o (map_pre_\<Sigma>\<Sigma>1 id (ctor_fold_\<Sigma>\<Sigma>1 s))"
unfolding comp_def \<Sigma>\<Sigma>1.ctor_fold ..

lemma \<Sigma>\<Sigma>1_map_ctor_\<Sigma>\<Sigma>1:
"\<Sigma>\<Sigma>1_map f o ctor_\<Sigma>\<Sigma>1 = ctor_\<Sigma>\<Sigma>1 o map_sum (\<Sigma>1_map (\<Sigma>\<Sigma>1_map f)) f"
unfolding comp_def
unfolding fun_eq_iff
unfolding \<Sigma>\<Sigma>1.ctor_map
unfolding map_pre_\<Sigma>\<Sigma>1_def  (* careful here and elsewhere: data newdatatype unfolds more *)
unfolding id_apply BNF_Comp.id_bnf_comp_def id_def[symmetric] o_id id_o by simp

lemma dtor_\<Sigma>\<Sigma>1_\<Sigma>\<Sigma>1_map:
"dtor_\<Sigma>\<Sigma>1 o \<Sigma>\<Sigma>1_map f = map_sum (\<Sigma>1_map (\<Sigma>\<Sigma>1_map f)) f o dtor_\<Sigma>\<Sigma>1"
using \<Sigma>\<Sigma>1_map_ctor_\<Sigma>\<Sigma>1[of f] \<Sigma>\<Sigma>1.dtor_ctor \<Sigma>\<Sigma>1.ctor_dtor unfolding comp_def fun_eq_iff by metis

lemma dtor_\<Sigma>\<Sigma>1_ctor_\<Sigma>\<Sigma>1: "dtor_\<Sigma>\<Sigma>1 \<circ> ctor_\<Sigma>\<Sigma>1 = id"
unfolding comp_def \<Sigma>\<Sigma>1.dtor_ctor id_def ..

lemma ctor_\<Sigma>\<Sigma>1_dtor_\<Sigma>\<Sigma>1: "ctor_\<Sigma>\<Sigma>1 \<circ> dtor_\<Sigma>\<Sigma>1 = id"
unfolding comp_def \<Sigma>\<Sigma>1.ctor_dtor id_def ..

lemma \<Sigma>\<Sigma>1_rel_inf: "\<Sigma>\<Sigma>1_rel (R \<sqinter> \<Sigma>0) \<le> \<Sigma>\<Sigma>1_rel R \<sqinter> \<Sigma>\<Sigma>1_rel \<Sigma>0"
  apply (rule inf_greatest)
  apply (rule \<Sigma>\<Sigma>1.rel_mono[OF inf_sup_ord(1)])
  apply (rule \<Sigma>\<Sigma>1.rel_mono[OF inf_sup_ord(2)])
  done

lemma \<Sigma>\<Sigma>1_rel_Grp_\<Sigma>\<Sigma>1_map: "\<Sigma>\<Sigma>1_rel (BNF_Def.Grp UNIV f) x y \<longleftrightarrow> \<Sigma>\<Sigma>1_map f x = y"
  unfolding \<Sigma>\<Sigma>1.rel_Grp by (auto simp: Grp_def)

lemma \<Sigma>\<Sigma>1_rel_\<Sigma>\<Sigma>1_map_\<Sigma>\<Sigma>1_map: "\<Sigma>\<Sigma>1_rel R (\<Sigma>\<Sigma>1_map f x) (\<Sigma>\<Sigma>1_map g y) =
  \<Sigma>\<Sigma>1_rel (BNF_Def.vimage2p f g R) x y"
  unfolding \<Sigma>\<Sigma>1.rel_Grp vimage2p_Grp apply (auto simp: \<Sigma>\<Sigma>1.rel_compp \<Sigma>\<Sigma>1.rel_conversep relcompp.simps)
  apply (intro exI conjI)
  apply (rule iffD2[OF \<Sigma>\<Sigma>1_rel_Grp_\<Sigma>\<Sigma>1_map refl])
  apply assumption
  apply (rule iffD2[OF \<Sigma>\<Sigma>1_rel_Grp_\<Sigma>\<Sigma>1_map refl])
  unfolding \<Sigma>\<Sigma>1_rel_Grp_\<Sigma>\<Sigma>1_map
  apply simp
  done


subsection{* @{term \<Sigma>1} extension theorems *}

theorem ext1_commute:
"ext1 s i o \<oo>\<pp>1 = s o \<Sigma>1_map (ext1 s i)"
unfolding ext1_alt \<oo>\<pp>1_def_pointfree o_assoc ctor_fold_\<Sigma>\<Sigma>1_pointfree map_pre_\<Sigma>\<Sigma>1_def
  case_sum_o_map_sum case_sum_o_inj(1) BNF_Comp.id_bnf_comp_def id_def[symmetric] o_id ..

theorem ext1_comp_leaf1:
"ext1 s i o leaf1 = i"
unfolding ext1_alt leaf1_def_pointfree o_assoc ctor_fold_\<Sigma>\<Sigma>1_pointfree map_pre_\<Sigma>\<Sigma>1_def
  case_sum_o_map_sum case_sum_o_inj(2) id_apply BNF_Comp.id_bnf_comp_def id_def[symmetric] o_id ..

theorem ext1_unique:
assumes leaf1: "f o leaf1 = i" and com: "f o \<oo>\<pp>1 = s o \<Sigma>1_map f"
shows "f = ext1 s i"
unfolding ext1_alt
apply (rule \<Sigma>\<Sigma>1.ctor_fold_unique)
apply (rule sum_comp_cases)
unfolding map_pre_\<Sigma>\<Sigma>1_def case_sum_o_map_sum id_apply o_id case_sum_o_inj
  leaf1[unfolded leaf1_def_pointfree o_assoc] com[unfolded \<oo>\<pp>1_def_pointfree o_assoc]
  BNF_Comp.id_bnf_comp_def id_def[symmetric] id_o
by (rule refl)+

subsection{* Customizing @{term \<Sigma>\<Sigma>1} *}

subsection{* Injectiveness, naturality, adjunction *}

theorem leaf1_natural: "\<Sigma>\<Sigma>1_map f o leaf1 = leaf1 o f"
  using leaf1_transfer[of "BNF_Def.Grp UNIV f"]
  unfolding \<Sigma>\<Sigma>1.rel_Grp
  unfolding Grp_def rel_fun_def by auto

lemma \<oo>\<pp>1_natural: "\<oo>\<pp>1 o \<Sigma>1_map (\<Sigma>\<Sigma>1_map f) = \<Sigma>\<Sigma>1_map f o \<oo>\<pp>1"
  using \<oo>\<pp>1_transfer[of "BNF_Def.Grp UNIV f"]
  unfolding \<Sigma>1.rel_Grp \<Sigma>\<Sigma>1.rel_Grp \<Sigma>1_map_def
  unfolding Grp_def rel_fun_def by auto

lemma \<Sigma>\<Sigma>1_map_def2: "\<Sigma>\<Sigma>1_map i = ext1 \<oo>\<pp>1 (leaf1 o i)"
by (rule ext1_unique[OF leaf1_natural \<oo>\<pp>1_natural[symmetric]])

lemma ext1_\<oo>\<pp>1_leaf1: "ext1 \<oo>\<pp>1 leaf1 = id"
apply (rule ext1_unique[symmetric]) unfolding \<Sigma>1.map_id0 o_id id_o by (rule refl)+

lemma ext1_\<Sigma>\<Sigma>1_map:
"ext1 s (j o f) = ext1 s j o \<Sigma>\<Sigma>1_map f"
proof (rule ext1_unique[symmetric])
  show "ext1 s j \<circ> \<Sigma>\<Sigma>1_map f \<circ> leaf1 = j \<circ> f"
  unfolding o_assoc[symmetric] leaf1_natural
  unfolding o_assoc ext1_comp_leaf1 ..
next
  show "ext1 s j \<circ> \<Sigma>\<Sigma>1_map f \<circ> \<oo>\<pp>1 = s \<circ> \<Sigma>1_map (ext1 s j \<circ> \<Sigma>\<Sigma>1_map f)"
  unfolding o_assoc[symmetric] \<oo>\<pp>1_natural[symmetric]
  unfolding o_assoc ext1_commute
  unfolding o_assoc[symmetric] \<Sigma>1.map_comp0 ..
qed

lemma ext1_\<Sigma>1_map:
assumes "t o \<Sigma>1_map f = f o s"
shows "ext1 t (f o i) = f o ext1 s i"
proof (rule ext1_unique[symmetric])
  show "f \<circ> ext1 s i \<circ> leaf1 = f o i"
  unfolding o_assoc[symmetric] ext1_comp_leaf1 ..
next
  show "f \<circ> ext1 s i \<circ> \<oo>\<pp>1 = t \<circ> \<Sigma>1_map (f \<circ> ext1 s i)"
  unfolding \<Sigma>1.map_comp0 o_assoc assms
  unfolding o_assoc[symmetric] ext1_commute[symmetric] ..
qed


subsection{* Monadic laws *}

lemma flat1_commute: "\<oo>\<pp>1 \<circ> \<Sigma>1_map flat1 = flat1 \<circ> \<oo>\<pp>1"
unfolding flat1_def ext1_commute ..

(* The 2 identity laws*)
theorem flat1_leaf1: "flat1 o leaf1 = id"
unfolding flat1_def ext1_comp_leaf1 ..

theorem leaf1_flat1: "flat1 o \<Sigma>\<Sigma>1_map leaf1 = id"
unfolding flat1_def ext1_\<Sigma>\<Sigma>1_map[symmetric] id_o ext1_\<oo>\<pp>1_leaf1 ..

theorem flat1_natural: "flat1 o \<Sigma>\<Sigma>1_map (\<Sigma>\<Sigma>1_map i) = \<Sigma>\<Sigma>1_map i o flat1"
  using flat1_transfer[of "BNF_Def.Grp UNIV i"]
  unfolding prod.rel_Grp \<Sigma>\<Sigma>1.rel_Grp
  unfolding Grp_def rel_fun_def by auto

(* Associativity *)
theorem flat1_assoc: "flat1 o \<Sigma>\<Sigma>1_map flat1 = flat1 o flat1"
unfolding flat1_def unfolding ext1_\<Sigma>\<Sigma>1_map[symmetric] id_o
proof(rule ext1_unique[symmetric], unfold flat1_def[symmetric])
  show "flat1 \<circ> flat1 \<circ> leaf1 = flat1"
  unfolding o_assoc[symmetric] flat1_leaf1 o_id ..
next
  show "flat1 \<circ> flat1 \<circ> \<oo>\<pp>1 = \<oo>\<pp>1 \<circ> \<Sigma>1_map (flat1 \<circ> flat1)"
  unfolding flat1_def unfolding o_assoc[symmetric] ext1_commute
  unfolding flat1_def[symmetric]
  unfolding \<Sigma>1.map_comp0 o_assoc unfolding flat1_commute ..
qed

definition K1_as_\<Sigma>\<Sigma>1 :: "'a K1 \<Rightarrow> 'a \<Sigma>\<Sigma>1" where
"K1_as_\<Sigma>\<Sigma>1 \<equiv> \<oo>\<pp>1 o \<Sigma>1_map leaf1 o Abs_\<Sigma>1 o Inr"

lemma K1_as_\<Sigma>\<Sigma>1_transfer[transfer_rule]:
  "(K1_rel R ===> \<Sigma>\<Sigma>1_rel R) K1_as_\<Sigma>\<Sigma>1 K1_as_\<Sigma>\<Sigma>1"
  unfolding K1_as_\<Sigma>\<Sigma>1_def by transfer_prover

lemma K1_as_\<Sigma>\<Sigma>1_natural:
"K1_as_\<Sigma>\<Sigma>1 o K1_map f = \<Sigma>\<Sigma>1_map f o K1_as_\<Sigma>\<Sigma>1"
  using K1_as_\<Sigma>\<Sigma>1_transfer[of "BNF_Def.Grp UNIV f"]
  unfolding K1.rel_Grp \<Sigma>\<Sigma>1.rel_Grp
  unfolding Grp_def rel_fun_def by auto

end