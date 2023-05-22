header{* Free algebras for an BNF *}

(* Free algebra constructed for a sum of two BNF's S and K: *)
(* Notations: Identical to FreeAlg, just that constants and types are suffixed by "step" instead of "base": *)

theory Stream_FreeAlg8
imports Stream_Input8
begin

declare K8.map_transfer[transfer_rule]

(* The new-operation functor: *)

composition_bnf (open) raw_\<Sigma>8: "'a \<Sigma>7 + 'a K8"
typedef 'a \<Sigma>8 = "UNIV :: ('a \<Sigma>7 + 'a K8) set" by (rule UNIV_witness)

setup_lifting type_definition_\<Sigma>8

lift_definition \<Sigma>8_map :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Sigma>8 \<Rightarrow> 'b \<Sigma>8" is "\<lambda>f. map_sum (\<Sigma>7_map f) (K8_map f)" .
lift_definition \<Sigma>8_set :: "'a \<Sigma>8 \<Rightarrow> 'a set"
  is "\<lambda>x. UNION (Basic_BNFs.setl x) \<Sigma>7_set \<union> UNION (Basic_BNFs.setr x) K8_set" .
lift_definition \<Sigma>8_rel :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a \<Sigma>8 \<Rightarrow> 'b \<Sigma>8 \<Rightarrow> bool"
  is "\<lambda>R. rel_sum (\<Sigma>7_rel R) (K8_rel R)" .
typedef \<Sigma>8_bd_type = "UNIV :: ((\<Sigma>7_bd_type + bd_type_K8) \<times> nat) set" by (rule UNIV_witness)
definition "\<Sigma>8_bd = dir_image ((\<Sigma>7_bd +c bd_K8) *c natLeq) Abs_\<Sigma>8_bd_type"

bnf "'a \<Sigma>8"
  map: \<Sigma>8_map
  sets: \<Sigma>8_set
  bd: \<Sigma>8_bd 
  rel: \<Sigma>8_rel
unfolding \<Sigma>8_bd_def
apply -
apply transfer apply (rule raw_\<Sigma>8.map_id0)
apply transfer apply (rule raw_\<Sigma>8.map_comp0)
apply transfer apply (erule raw_\<Sigma>8.map_cong0)
apply transfer apply (rule raw_\<Sigma>8.set_map0)
apply (rule card_order_dir_image[OF bijI raw_\<Sigma>8.bd_card_order])
apply (metis inj_on_def Abs_\<Sigma>8_bd_type_inverse[OF UNIV_I])
apply (metis surj_def Abs_\<Sigma>8_bd_type_cases)
apply (rule conjunct1[OF Cinfinite_cong[OF dir_image[OF _ raw_\<Sigma>8.bd_Card_order] raw_\<Sigma>8.bd_Cinfinite]])
apply (metis Abs_\<Sigma>8_bd_type_inverse[OF UNIV_I])
apply (unfold \<Sigma>8_set_def map_fun_def id_o) [1] apply (subst o_apply)
apply (rule ordLeq_ordIso_trans[OF raw_\<Sigma>8.set_bd dir_image[OF _ raw_\<Sigma>8.bd_Card_order]])
apply (metis Abs_\<Sigma>8_bd_type_inverse[OF UNIV_I])
apply (rule predicate2I) apply transfer apply (subst raw_\<Sigma>8.rel_compp) apply assumption
apply transfer' apply (rule raw_\<Sigma>8.rel_compp_Grp)
done

declare \<Sigma>8.map_transfer[transfer_rule]

lemma Rep_\<Sigma>8_transfer[transfer_rule]: "(\<Sigma>8_rel R ===> rel_sum (\<Sigma>7_rel R) (K8_rel R)) Rep_\<Sigma>8 Rep_\<Sigma>8"
  unfolding rel_fun_def by transfer blast

lemma Abs_\<Sigma>8_transfer[transfer_rule]: "(rel_sum (\<Sigma>7_rel R) (K8_rel R) ===> \<Sigma>8_rel R) Abs_\<Sigma>8 Abs_\<Sigma>8"
  unfolding rel_fun_def by transfer blast

theorem Rep_\<Sigma>8_natural: "map_sum (\<Sigma>7_map f) (K8_map f) o Rep_\<Sigma>8 = Rep_\<Sigma>8 o \<Sigma>8_map f"
  using Rep_\<Sigma>8_transfer[of "BNF_Def.Grp UNIV f"]
  unfolding \<Sigma>8.rel_Grp raw_\<Sigma>8.rel_Grp
  unfolding Grp_def rel_fun_def by auto

theorem Abs_\<Sigma>8_natural: "\<Sigma>8_map f o Abs_\<Sigma>8 = Abs_\<Sigma>8 o map_sum (\<Sigma>7_map f) (K8_map f)"
  using Abs_\<Sigma>8_transfer[of "BNF_Def.Grp UNIV f"]
  unfolding \<Sigma>8.rel_Grp raw_\<Sigma>8.rel_Grp
  unfolding Grp_def rel_fun_def by auto

lemma Rep_\<Sigma>8_o_Abs_\<Sigma>8: "Rep_\<Sigma>8 o Abs_\<Sigma>8 = id"
  apply (rule ext)
  apply (rule box_equals[OF _ o_apply[symmetric] id_apply[symmetric]])
  apply (rule Abs_\<Sigma>8_inverse[OF UNIV_I])
  done

lemma \<Sigma>8_rel_\<Sigma>8_map_\<Sigma>8_map:
  "\<Sigma>8_rel R (\<Sigma>8_map f x) (\<Sigma>8_map g y) = \<Sigma>8_rel (BNF_Def.vimage2p f g R) x y"
  unfolding \<Sigma>8.rel_Grp vimage2p_Grp \<Sigma>8.rel_compp \<Sigma>8.rel_conversep
  unfolding relcompp.simps Grp_def by simp

subsection{* Definitions and basic setup *}

(* 'x \<Sigma>\<Sigma>8 consist of \<Sigma>8-terms with variables in 'x: *)
datatype_new (\<Sigma>\<Sigma>8_set: 'x) \<Sigma>\<Sigma>8 =
  \<oo>\<pp>8 "'x \<Sigma>\<Sigma>8 \<Sigma>8" | leaf8 "'x"
  for map: \<Sigma>\<Sigma>8_map rel: \<Sigma>\<Sigma>8_rel
declare \<Sigma>\<Sigma>8.ctor_fold_transfer
  [unfolded rel_pre_\<Sigma>\<Sigma>8_def id_apply BNF_Comp.id_bnf_comp_def vimage2p_def, transfer_rule]

lemma \<oo>\<pp>8_transfer[transfer_rule]:
  "(\<Sigma>8_rel (\<Sigma>\<Sigma>8_rel R) ===> \<Sigma>\<Sigma>8_rel R) \<oo>\<pp>8 \<oo>\<pp>8"
  by (rule rel_funI) (erule iffD2[OF \<Sigma>\<Sigma>8.rel_inject(1)])

lemma leaf8_transfer[transfer_rule]: "(R ===> \<Sigma>\<Sigma>8_rel R) leaf8 leaf8"
  by (rule rel_funI) (erule iffD2[OF \<Sigma>\<Sigma>8.rel_inject(2)])

(* The free extension, for an algebra s, of an inteprleaftion i of the
variables into the algebra carrier:  *)
abbreviation "ext8 s \<equiv> rec_\<Sigma>\<Sigma>8 (s o \<Sigma>8_map snd)"
lemmas ext8_\<oo>\<pp>8 = \<Sigma>\<Sigma>8.rec(1)[of "s o \<Sigma>8_map snd" for s,
  unfolded o_apply \<Sigma>8.map_comp snd_convol[unfolded convol_def]]
lemmas ext8_leaf8 = \<Sigma>\<Sigma>8.rec(2)[of "s o \<Sigma>8_map snd" for s,
  unfolded o_apply \<Sigma>8.map_comp snd_convol[unfolded convol_def]]
lemmas leaf8_inj = \<Sigma>\<Sigma>8.inject(2)
lemmas \<oo>\<pp>8_inj = \<Sigma>\<Sigma>8.inject(1)

lemma ext8_alt: "ext8 s f = ctor_fold_\<Sigma>\<Sigma>8 (case_sum s f)"
  apply (rule \<Sigma>\<Sigma>8.ctor_fold_unique)
  apply (rule ext)
  apply (rename_tac x)
  apply (case_tac x)
  apply (auto simp only: rec_\<Sigma>\<Sigma>8_def \<Sigma>\<Sigma>8.ctor_rec fun_eq_iff o_apply BNF_Comp.id_bnf_comp_def
    id_def[symmetric] o_id map_pre_\<Sigma>\<Sigma>8_def id_apply map_sum.simps sum.inject sum.distinct
    \<Sigma>8.map_comp snd_convol split: sum.splits)
  done

(* The term algebra: *)

lemma \<oo>\<pp>8_def_pointfree: "\<oo>\<pp>8 \<equiv> ctor_\<Sigma>\<Sigma>8 o Inl"
unfolding \<oo>\<pp>8_def comp_def BNF_Comp.id_bnf_comp_def .

(* Monadic structure *)
lemma leaf8_def_pointfree: "leaf8 \<equiv> ctor_\<Sigma>\<Sigma>8 o Inr"
unfolding leaf8_def comp_def BNF_Comp.id_bnf_comp_def .

definition flat8 :: "('x \<Sigma>\<Sigma>8) \<Sigma>\<Sigma>8 \<Rightarrow> 'x \<Sigma>\<Sigma>8" where
  flat8_def: "flat8 \<equiv> ext8 \<oo>\<pp>8 id"

lemma flat8_transfer[transfer_rule]: "(\<Sigma>\<Sigma>8_rel (\<Sigma>\<Sigma>8_rel R) ===> \<Sigma>\<Sigma>8_rel R) flat8 flat8"
  unfolding flat8_def ext8_alt by transfer_prover

(* facts about \<Sigma>\<Sigma>8: *)
lemma ctor_fold_\<Sigma>\<Sigma>8_pointfree:
"ctor_fold_\<Sigma>\<Sigma>8 s o ctor_\<Sigma>\<Sigma>8 = s o (map_pre_\<Sigma>\<Sigma>8 id (ctor_fold_\<Sigma>\<Sigma>8 s))"
unfolding comp_def \<Sigma>\<Sigma>8.ctor_fold ..

lemma \<Sigma>\<Sigma>8_map_ctor_\<Sigma>\<Sigma>8:
"\<Sigma>\<Sigma>8_map f o ctor_\<Sigma>\<Sigma>8 = ctor_\<Sigma>\<Sigma>8 o map_sum (\<Sigma>8_map (\<Sigma>\<Sigma>8_map f)) f"
unfolding comp_def
unfolding fun_eq_iff
unfolding \<Sigma>\<Sigma>8.ctor_map
unfolding map_pre_\<Sigma>\<Sigma>8_def  (* careful here and elsewhere: data newdatatype unfolds more *)
unfolding id_apply BNF_Comp.id_bnf_comp_def id_def[symmetric] o_id id_o by simp

lemma dtor_\<Sigma>\<Sigma>8_\<Sigma>\<Sigma>8_map:
"dtor_\<Sigma>\<Sigma>8 o \<Sigma>\<Sigma>8_map f = map_sum (\<Sigma>8_map (\<Sigma>\<Sigma>8_map f)) f o dtor_\<Sigma>\<Sigma>8"
using \<Sigma>\<Sigma>8_map_ctor_\<Sigma>\<Sigma>8[of f] \<Sigma>\<Sigma>8.dtor_ctor \<Sigma>\<Sigma>8.ctor_dtor unfolding comp_def fun_eq_iff by metis

lemma dtor_\<Sigma>\<Sigma>8_ctor_\<Sigma>\<Sigma>8: "dtor_\<Sigma>\<Sigma>8 \<circ> ctor_\<Sigma>\<Sigma>8 = id"
unfolding comp_def \<Sigma>\<Sigma>8.dtor_ctor id_def ..

lemma ctor_\<Sigma>\<Sigma>8_dtor_\<Sigma>\<Sigma>8: "ctor_\<Sigma>\<Sigma>8 \<circ> dtor_\<Sigma>\<Sigma>8 = id"
unfolding comp_def \<Sigma>\<Sigma>8.ctor_dtor id_def ..

lemma \<Sigma>\<Sigma>8_rel_inf: "\<Sigma>\<Sigma>8_rel (R \<sqinter> \<Sigma>7) \<le> \<Sigma>\<Sigma>8_rel R \<sqinter> \<Sigma>\<Sigma>8_rel \<Sigma>7"
  apply (rule inf_greatest)
  apply (rule \<Sigma>\<Sigma>8.rel_mono[OF inf_sup_ord(1)])
  apply (rule \<Sigma>\<Sigma>8.rel_mono[OF inf_sup_ord(2)])
  done

lemma \<Sigma>\<Sigma>8_rel_Grp_\<Sigma>\<Sigma>8_map: "\<Sigma>\<Sigma>8_rel (BNF_Def.Grp UNIV f) x y \<longleftrightarrow> \<Sigma>\<Sigma>8_map f x = y"
  unfolding \<Sigma>\<Sigma>8.rel_Grp by (auto simp: Grp_def)

lemma \<Sigma>\<Sigma>8_rel_\<Sigma>\<Sigma>8_map_\<Sigma>\<Sigma>8_map: "\<Sigma>\<Sigma>8_rel R (\<Sigma>\<Sigma>8_map f x) (\<Sigma>\<Sigma>8_map g y) =
  \<Sigma>\<Sigma>8_rel (BNF_Def.vimage2p f g R) x y"
  unfolding \<Sigma>\<Sigma>8.rel_Grp vimage2p_Grp apply (auto simp: \<Sigma>\<Sigma>8.rel_compp \<Sigma>\<Sigma>8.rel_conversep relcompp.simps)
  apply (intro exI conjI)
  apply (rule iffD2[OF \<Sigma>\<Sigma>8_rel_Grp_\<Sigma>\<Sigma>8_map refl])
  apply assumption
  apply (rule iffD2[OF \<Sigma>\<Sigma>8_rel_Grp_\<Sigma>\<Sigma>8_map refl])
  unfolding \<Sigma>\<Sigma>8_rel_Grp_\<Sigma>\<Sigma>8_map
  apply simp
  done


subsection{* @{term \<Sigma>8} extension theorems *}

theorem ext8_commute:
"ext8 s i o \<oo>\<pp>8 = s o \<Sigma>8_map (ext8 s i)"
unfolding ext8_alt \<oo>\<pp>8_def_pointfree o_assoc ctor_fold_\<Sigma>\<Sigma>8_pointfree map_pre_\<Sigma>\<Sigma>8_def
  case_sum_o_map_sum case_sum_o_inj(1) BNF_Comp.id_bnf_comp_def id_def[symmetric] o_id ..

theorem ext8_comp_leaf8:
"ext8 s i o leaf8 = i"
unfolding ext8_alt leaf8_def_pointfree o_assoc ctor_fold_\<Sigma>\<Sigma>8_pointfree map_pre_\<Sigma>\<Sigma>8_def
  case_sum_o_map_sum case_sum_o_inj(2) id_apply BNF_Comp.id_bnf_comp_def id_def[symmetric] o_id ..

theorem ext8_unique:
assumes leaf8: "f o leaf8 = i" and com: "f o \<oo>\<pp>8 = s o \<Sigma>8_map f"
shows "f = ext8 s i"
unfolding ext8_alt
apply (rule \<Sigma>\<Sigma>8.ctor_fold_unique)
apply (rule sum_comp_cases)
unfolding map_pre_\<Sigma>\<Sigma>8_def case_sum_o_map_sum id_apply o_id case_sum_o_inj
  leaf8[unfolded leaf8_def_pointfree o_assoc] com[unfolded \<oo>\<pp>8_def_pointfree o_assoc]
  BNF_Comp.id_bnf_comp_def id_def[symmetric] id_o
by (rule refl)+

subsection{* Customizing @{term \<Sigma>\<Sigma>8} *}

subsection{* Injectiveness, naturality, adjunction *}

theorem leaf8_natural: "\<Sigma>\<Sigma>8_map f o leaf8 = leaf8 o f"
  using leaf8_transfer[of "BNF_Def.Grp UNIV f"]
  unfolding \<Sigma>\<Sigma>8.rel_Grp
  unfolding Grp_def rel_fun_def by auto

lemma \<oo>\<pp>8_natural: "\<oo>\<pp>8 o \<Sigma>8_map (\<Sigma>\<Sigma>8_map f) = \<Sigma>\<Sigma>8_map f o \<oo>\<pp>8"
  using \<oo>\<pp>8_transfer[of "BNF_Def.Grp UNIV f"]
  unfolding \<Sigma>8.rel_Grp \<Sigma>\<Sigma>8.rel_Grp \<Sigma>8_map_def
  unfolding Grp_def rel_fun_def by auto

lemma \<Sigma>\<Sigma>8_map_def2: "\<Sigma>\<Sigma>8_map i = ext8 \<oo>\<pp>8 (leaf8 o i)"
by (rule ext8_unique[OF leaf8_natural \<oo>\<pp>8_natural[symmetric]])

lemma ext8_\<oo>\<pp>8_leaf8: "ext8 \<oo>\<pp>8 leaf8 = id"
apply (rule ext8_unique[symmetric]) unfolding \<Sigma>8.map_id0 o_id id_o by (rule refl)+

lemma ext8_\<Sigma>\<Sigma>8_map:
"ext8 s (j o f) = ext8 s j o \<Sigma>\<Sigma>8_map f"
proof (rule ext8_unique[symmetric])
  show "ext8 s j \<circ> \<Sigma>\<Sigma>8_map f \<circ> leaf8 = j \<circ> f"
  unfolding o_assoc[symmetric] leaf8_natural
  unfolding o_assoc ext8_comp_leaf8 ..
next
  show "ext8 s j \<circ> \<Sigma>\<Sigma>8_map f \<circ> \<oo>\<pp>8 = s \<circ> \<Sigma>8_map (ext8 s j \<circ> \<Sigma>\<Sigma>8_map f)"
  unfolding o_assoc[symmetric] \<oo>\<pp>8_natural[symmetric]
  unfolding o_assoc ext8_commute
  unfolding o_assoc[symmetric] \<Sigma>8.map_comp0 ..
qed

lemma ext8_\<Sigma>8_map:
assumes "t o \<Sigma>8_map f = f o s"
shows "ext8 t (f o i) = f o ext8 s i"
proof (rule ext8_unique[symmetric])
  show "f \<circ> ext8 s i \<circ> leaf8 = f o i"
  unfolding o_assoc[symmetric] ext8_comp_leaf8 ..
next
  show "f \<circ> ext8 s i \<circ> \<oo>\<pp>8 = t \<circ> \<Sigma>8_map (f \<circ> ext8 s i)"
  unfolding \<Sigma>8.map_comp0 o_assoc assms
  unfolding o_assoc[symmetric] ext8_commute[symmetric] ..
qed


subsection{* Monadic laws *}

lemma flat8_commute: "\<oo>\<pp>8 \<circ> \<Sigma>8_map flat8 = flat8 \<circ> \<oo>\<pp>8"
unfolding flat8_def ext8_commute ..

(* The 2 identity laws*)
theorem flat8_leaf8: "flat8 o leaf8 = id"
unfolding flat8_def ext8_comp_leaf8 ..

theorem leaf8_flat8: "flat8 o \<Sigma>\<Sigma>8_map leaf8 = id"
unfolding flat8_def ext8_\<Sigma>\<Sigma>8_map[symmetric] id_o ext8_\<oo>\<pp>8_leaf8 ..

theorem flat8_natural: "flat8 o \<Sigma>\<Sigma>8_map (\<Sigma>\<Sigma>8_map i) = \<Sigma>\<Sigma>8_map i o flat8"
  using flat8_transfer[of "BNF_Def.Grp UNIV i"]
  unfolding prod.rel_Grp \<Sigma>\<Sigma>8.rel_Grp
  unfolding Grp_def rel_fun_def by auto

(* Associativity *)
theorem flat8_assoc: "flat8 o \<Sigma>\<Sigma>8_map flat8 = flat8 o flat8"
unfolding flat8_def unfolding ext8_\<Sigma>\<Sigma>8_map[symmetric] id_o
proof(rule ext8_unique[symmetric], unfold flat8_def[symmetric])
  show "flat8 \<circ> flat8 \<circ> leaf8 = flat8"
  unfolding o_assoc[symmetric] flat8_leaf8 o_id ..
next
  show "flat8 \<circ> flat8 \<circ> \<oo>\<pp>8 = \<oo>\<pp>8 \<circ> \<Sigma>8_map (flat8 \<circ> flat8)"
  unfolding flat8_def unfolding o_assoc[symmetric] ext8_commute
  unfolding flat8_def[symmetric]
  unfolding \<Sigma>8.map_comp0 o_assoc unfolding flat8_commute ..
qed

definition K8_as_\<Sigma>\<Sigma>8 :: "'a K8 \<Rightarrow> 'a \<Sigma>\<Sigma>8" where
"K8_as_\<Sigma>\<Sigma>8 \<equiv> \<oo>\<pp>8 o \<Sigma>8_map leaf8 o Abs_\<Sigma>8 o Inr"

lemma K8_as_\<Sigma>\<Sigma>8_transfer[transfer_rule]:
  "(K8_rel R ===> \<Sigma>\<Sigma>8_rel R) K8_as_\<Sigma>\<Sigma>8 K8_as_\<Sigma>\<Sigma>8"
  unfolding K8_as_\<Sigma>\<Sigma>8_def by transfer_prover

lemma K8_as_\<Sigma>\<Sigma>8_natural:
"K8_as_\<Sigma>\<Sigma>8 o K8_map f = \<Sigma>\<Sigma>8_map f o K8_as_\<Sigma>\<Sigma>8"
  using K8_as_\<Sigma>\<Sigma>8_transfer[of "BNF_Def.Grp UNIV f"]
  unfolding K8.rel_Grp \<Sigma>\<Sigma>8.rel_Grp
  unfolding Grp_def rel_fun_def by auto

end