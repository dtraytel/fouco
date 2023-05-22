header{* Free algebras for an BNF *}

(* Free algebra constructed for a sum of two BNF's S and K: *)
(* Notations: Identical to FreeAlg, just that constants and types are suffixed by "step" instead of "base": *)

theory FreeAlg_step
imports Input_step
begin

declare K_step.map_transfer[transfer_rule]

(* The new-operation functor: *)

composition_bnf (open) raw_\<Sigma>_step: "'a \<Sigma>_base + 'a K_step"
typedef 'a \<Sigma>_step = "UNIV :: ('a \<Sigma>_base + 'a K_step) set" by (rule UNIV_witness)

setup_lifting type_definition_\<Sigma>_step

lift_definition \<Sigma>_step_map :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Sigma>_step \<Rightarrow> 'b \<Sigma>_step" is "\<lambda>f. map_sum (\<Sigma>_base_map f) (K_step_map f)" .
lift_definition \<Sigma>_step_set :: "'a \<Sigma>_step \<Rightarrow> 'a set"
  is "\<lambda>x. UNION (Basic_BNFs.setl x) \<Sigma>_base_set \<union> UNION (Basic_BNFs.setr x) K_step_set" .
lift_definition \<Sigma>_step_rel :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a \<Sigma>_step \<Rightarrow> 'b \<Sigma>_step \<Rightarrow> bool"
  is "\<lambda>R. rel_sum (\<Sigma>_base_rel R) (K_step_rel R)" .
typedef \<Sigma>_step_bd_type = "UNIV :: ((\<Sigma>_base_bd_type + bd_type_K_step) \<times> nat) set" by (rule UNIV_witness)
definition "\<Sigma>_step_bd = dir_image ((\<Sigma>_base_bd +c bd_K_step) *c natLeq) Abs_\<Sigma>_step_bd_type"

bnf "'a \<Sigma>_step"
  map: \<Sigma>_step_map
  sets: \<Sigma>_step_set
  bd: \<Sigma>_step_bd 
  rel: \<Sigma>_step_rel
unfolding \<Sigma>_step_bd_def
apply -
apply transfer apply (rule raw_\<Sigma>_step.map_id0)
apply transfer apply (rule raw_\<Sigma>_step.map_comp0)
apply transfer apply (erule raw_\<Sigma>_step.map_cong0)
apply transfer apply (rule raw_\<Sigma>_step.set_map0)
apply (rule card_order_dir_image[OF bijI raw_\<Sigma>_step.bd_card_order])
apply (metis inj_on_def Abs_\<Sigma>_step_bd_type_inverse[OF UNIV_I])
apply (metis surj_def Abs_\<Sigma>_step_bd_type_cases)
apply (rule conjunct1[OF Cinfinite_cong[OF dir_image[OF _ raw_\<Sigma>_step.bd_Card_order] raw_\<Sigma>_step.bd_Cinfinite]])
apply (metis Abs_\<Sigma>_step_bd_type_inverse[OF UNIV_I])
apply (unfold \<Sigma>_step_set_def map_fun_def id_o) [1] apply (subst o_apply)
apply (rule ordLeq_ordIso_trans[OF raw_\<Sigma>_step.set_bd dir_image[OF _ raw_\<Sigma>_step.bd_Card_order]])
apply (metis Abs_\<Sigma>_step_bd_type_inverse[OF UNIV_I])
apply (rule predicate2I) apply transfer apply (subst raw_\<Sigma>_step.rel_compp) apply assumption
apply transfer' apply (rule raw_\<Sigma>_step.rel_compp_Grp)
done

declare \<Sigma>_step.map_transfer[transfer_rule]

lemma Rep_\<Sigma>_step_transfer[transfer_rule]: "(\<Sigma>_step_rel R ===> rel_sum (\<Sigma>_base_rel R) (K_step_rel R)) Rep_\<Sigma>_step Rep_\<Sigma>_step"
  unfolding rel_fun_def by transfer blast

lemma Abs_\<Sigma>_step_transfer[transfer_rule]: "(rel_sum (\<Sigma>_base_rel R) (K_step_rel R) ===> \<Sigma>_step_rel R) Abs_\<Sigma>_step Abs_\<Sigma>_step"
  unfolding rel_fun_def by transfer blast

theorem Rep_\<Sigma>_step_natural: "map_sum (\<Sigma>_base_map f) (K_step_map f) o Rep_\<Sigma>_step = Rep_\<Sigma>_step o \<Sigma>_step_map f"
  using Rep_\<Sigma>_step_transfer[of "BNF_Def.Grp UNIV f"]
  unfolding \<Sigma>_step.rel_Grp raw_\<Sigma>_step.rel_Grp
  unfolding Grp_def rel_fun_def by auto

theorem Abs_\<Sigma>_step_natural: "\<Sigma>_step_map f o Abs_\<Sigma>_step = Abs_\<Sigma>_step o map_sum (\<Sigma>_base_map f) (K_step_map f)"
  using Abs_\<Sigma>_step_transfer[of "BNF_Def.Grp UNIV f"]
  unfolding \<Sigma>_step.rel_Grp raw_\<Sigma>_step.rel_Grp
  unfolding Grp_def rel_fun_def by auto

lemma Rep_\<Sigma>_step_o_Abs_\<Sigma>_step: "Rep_\<Sigma>_step o Abs_\<Sigma>_step = id"
  apply (rule ext)
  apply (rule box_equals[OF _ o_apply[symmetric] id_apply[symmetric]])
  apply (rule Abs_\<Sigma>_step_inverse[OF UNIV_I])
  done

lemma \<Sigma>_step_rel_\<Sigma>_step_map_\<Sigma>_step_map:
  "\<Sigma>_step_rel R (\<Sigma>_step_map f x) (\<Sigma>_step_map g y) = \<Sigma>_step_rel (BNF_Def.vimage2p f g R) x y"
  unfolding \<Sigma>_step.rel_Grp vimage2p_Grp \<Sigma>_step.rel_compp \<Sigma>_step.rel_conversep
  unfolding relcompp.simps Grp_def by simp

subsection{* Definitions and basic setup *}

(* 'x \<Sigma>\<Sigma>_step consist of \<Sigma>_step-terms with variables in 'x: *)
datatype_new (\<Sigma>\<Sigma>_step_set: 'x) \<Sigma>\<Sigma>_step =
  \<oo>\<pp>_step "'x \<Sigma>\<Sigma>_step \<Sigma>_step" | leaf_step "'x"
  for map: \<Sigma>\<Sigma>_step_map rel: \<Sigma>\<Sigma>_step_rel
declare \<Sigma>\<Sigma>_step.ctor_fold_transfer
  [unfolded rel_pre_\<Sigma>\<Sigma>_step_def id_apply BNF_Comp.id_bnf_comp_def vimage2p_def, transfer_rule]

lemma \<oo>\<pp>_step_transfer[transfer_rule]:
  "(\<Sigma>_step_rel (\<Sigma>\<Sigma>_step_rel R) ===> \<Sigma>\<Sigma>_step_rel R) \<oo>\<pp>_step \<oo>\<pp>_step"
  by (rule rel_funI) (erule iffD2[OF \<Sigma>\<Sigma>_step.rel_inject(1)])

lemma leaf_step_transfer[transfer_rule]: "(R ===> \<Sigma>\<Sigma>_step_rel R) leaf_step leaf_step"
  by (rule rel_funI) (erule iffD2[OF \<Sigma>\<Sigma>_step.rel_inject(2)])

(* The free extension, for an algebra s, of an inteprleaftion i of the
variables into the algebra carrier:  *)
abbreviation "ext_step s \<equiv> rec_\<Sigma>\<Sigma>_step (s o \<Sigma>_step_map snd)"
lemmas ext_step_\<oo>\<pp>_step = \<Sigma>\<Sigma>_step.rec(1)[of "s o \<Sigma>_step_map snd" for s,
  unfolded o_apply \<Sigma>_step.map_comp snd_convol[unfolded convol_def]]
lemmas ext_step_leaf_step = \<Sigma>\<Sigma>_step.rec(2)[of "s o \<Sigma>_step_map snd" for s,
  unfolded o_apply \<Sigma>_step.map_comp snd_convol[unfolded convol_def]]
lemmas leaf_step_inj = \<Sigma>\<Sigma>_step.inject(2)
lemmas \<oo>\<pp>_step_inj = \<Sigma>\<Sigma>_step.inject(1)

lemma ext_step_alt: "ext_step s f = ctor_fold_\<Sigma>\<Sigma>_step (case_sum s f)"
  apply (rule \<Sigma>\<Sigma>_step.ctor_fold_unique)
  apply (rule ext)
  apply (rename_tac x)
  apply (case_tac x)
  apply (auto simp only: rec_\<Sigma>\<Sigma>_step_def \<Sigma>\<Sigma>_step.ctor_rec fun_eq_iff o_apply BNF_Comp.id_bnf_comp_def
    id_def[symmetric] o_id map_pre_\<Sigma>\<Sigma>_step_def id_apply map_sum.simps sum.inject sum.distinct
    \<Sigma>_step.map_comp snd_convol split: sum.splits)
  done

(* The term algebra: *)

lemma \<oo>\<pp>_step_def_pointfree: "\<oo>\<pp>_step \<equiv> ctor_\<Sigma>\<Sigma>_step o Inl"
unfolding \<oo>\<pp>_step_def comp_def BNF_Comp.id_bnf_comp_def .

(* Monadic structure *)
lemma leaf_step_def_pointfree: "leaf_step \<equiv> ctor_\<Sigma>\<Sigma>_step o Inr"
unfolding leaf_step_def comp_def BNF_Comp.id_bnf_comp_def .

definition flat_step :: "('x \<Sigma>\<Sigma>_step) \<Sigma>\<Sigma>_step \<Rightarrow> 'x \<Sigma>\<Sigma>_step" where
  flat_step_def: "flat_step \<equiv> ext_step \<oo>\<pp>_step id"

lemma flat_step_transfer[transfer_rule]: "(\<Sigma>\<Sigma>_step_rel (\<Sigma>\<Sigma>_step_rel R) ===> \<Sigma>\<Sigma>_step_rel R) flat_step flat_step"
  unfolding flat_step_def ext_step_alt by transfer_prover

(* facts about \<Sigma>\<Sigma>_step: *)
lemma ctor_fold_\<Sigma>\<Sigma>_step_pointfree:
"ctor_fold_\<Sigma>\<Sigma>_step s o ctor_\<Sigma>\<Sigma>_step = s o (map_pre_\<Sigma>\<Sigma>_step id (ctor_fold_\<Sigma>\<Sigma>_step s))"
unfolding comp_def \<Sigma>\<Sigma>_step.ctor_fold ..

lemma \<Sigma>\<Sigma>_step_map_ctor_\<Sigma>\<Sigma>_step:
"\<Sigma>\<Sigma>_step_map f o ctor_\<Sigma>\<Sigma>_step = ctor_\<Sigma>\<Sigma>_step o map_sum (\<Sigma>_step_map (\<Sigma>\<Sigma>_step_map f)) f"
unfolding comp_def
unfolding fun_eq_iff
unfolding \<Sigma>\<Sigma>_step.ctor_map
unfolding map_pre_\<Sigma>\<Sigma>_step_def  (* careful here and elsewhere: data newdatatype unfolds more *)
unfolding id_apply BNF_Comp.id_bnf_comp_def id_def[symmetric] o_id id_o by simp

lemma dtor_\<Sigma>\<Sigma>_step_\<Sigma>\<Sigma>_step_map:
"dtor_\<Sigma>\<Sigma>_step o \<Sigma>\<Sigma>_step_map f = map_sum (\<Sigma>_step_map (\<Sigma>\<Sigma>_step_map f)) f o dtor_\<Sigma>\<Sigma>_step"
using \<Sigma>\<Sigma>_step_map_ctor_\<Sigma>\<Sigma>_step[of f] \<Sigma>\<Sigma>_step.dtor_ctor \<Sigma>\<Sigma>_step.ctor_dtor unfolding comp_def fun_eq_iff by metis

lemma dtor_\<Sigma>\<Sigma>_step_ctor_\<Sigma>\<Sigma>_step: "dtor_\<Sigma>\<Sigma>_step \<circ> ctor_\<Sigma>\<Sigma>_step = id"
unfolding comp_def \<Sigma>\<Sigma>_step.dtor_ctor id_def ..

lemma ctor_\<Sigma>\<Sigma>_step_dtor_\<Sigma>\<Sigma>_step: "ctor_\<Sigma>\<Sigma>_step \<circ> dtor_\<Sigma>\<Sigma>_step = id"
unfolding comp_def \<Sigma>\<Sigma>_step.ctor_dtor id_def ..

lemma \<Sigma>\<Sigma>_step_rel_inf: "\<Sigma>\<Sigma>_step_rel (R \<sqinter> \<Sigma>_base) \<le> \<Sigma>\<Sigma>_step_rel R \<sqinter> \<Sigma>\<Sigma>_step_rel \<Sigma>_base"
  apply (rule inf_greatest)
  apply (rule \<Sigma>\<Sigma>_step.rel_mono[OF inf_sup_ord(1)])
  apply (rule \<Sigma>\<Sigma>_step.rel_mono[OF inf_sup_ord(2)])
  done

lemma \<Sigma>\<Sigma>_step_rel_Grp_\<Sigma>\<Sigma>_step_map: "\<Sigma>\<Sigma>_step_rel (BNF_Def.Grp UNIV f) x y \<longleftrightarrow> \<Sigma>\<Sigma>_step_map f x = y"
  unfolding \<Sigma>\<Sigma>_step.rel_Grp by (auto simp: Grp_def)

lemma \<Sigma>\<Sigma>_step_rel_\<Sigma>\<Sigma>_step_map_\<Sigma>\<Sigma>_step_map: "\<Sigma>\<Sigma>_step_rel R (\<Sigma>\<Sigma>_step_map f x) (\<Sigma>\<Sigma>_step_map g y) =
  \<Sigma>\<Sigma>_step_rel (BNF_Def.vimage2p f g R) x y"
  unfolding \<Sigma>\<Sigma>_step.rel_Grp vimage2p_Grp apply (auto simp: \<Sigma>\<Sigma>_step.rel_compp \<Sigma>\<Sigma>_step.rel_conversep relcompp.simps)
  apply (intro exI conjI)
  apply (rule iffD2[OF \<Sigma>\<Sigma>_step_rel_Grp_\<Sigma>\<Sigma>_step_map refl])
  apply assumption
  apply (rule iffD2[OF \<Sigma>\<Sigma>_step_rel_Grp_\<Sigma>\<Sigma>_step_map refl])
  unfolding \<Sigma>\<Sigma>_step_rel_Grp_\<Sigma>\<Sigma>_step_map
  apply simp
  done


subsection{* @{term \<Sigma>_step} extension theorems *}

theorem ext_step_commute:
"ext_step s i o \<oo>\<pp>_step = s o \<Sigma>_step_map (ext_step s i)"
unfolding ext_step_alt \<oo>\<pp>_step_def_pointfree o_assoc ctor_fold_\<Sigma>\<Sigma>_step_pointfree map_pre_\<Sigma>\<Sigma>_step_def
  case_sum_o_map_sum case_sum_o_inj(1) BNF_Comp.id_bnf_comp_def id_def[symmetric] o_id ..

theorem ext_step_comp_leaf_step:
"ext_step s i o leaf_step = i"
unfolding ext_step_alt leaf_step_def_pointfree o_assoc ctor_fold_\<Sigma>\<Sigma>_step_pointfree map_pre_\<Sigma>\<Sigma>_step_def
  case_sum_o_map_sum case_sum_o_inj(2) id_apply BNF_Comp.id_bnf_comp_def id_def[symmetric] o_id ..

theorem ext_step_unique:
assumes leaf_step: "f o leaf_step = i" and com: "f o \<oo>\<pp>_step = s o \<Sigma>_step_map f"
shows "f = ext_step s i"
unfolding ext_step_alt
apply (rule \<Sigma>\<Sigma>_step.ctor_fold_unique)
apply (rule sum_comp_cases)
unfolding map_pre_\<Sigma>\<Sigma>_step_def case_sum_o_map_sum id_apply o_id case_sum_o_inj
  leaf_step[unfolded leaf_step_def_pointfree o_assoc] com[unfolded \<oo>\<pp>_step_def_pointfree o_assoc]
  BNF_Comp.id_bnf_comp_def id_def[symmetric] id_o
by (rule refl)+

subsection{* Customizing @{term \<Sigma>\<Sigma>_step} *}

subsection{* Injectiveness, naturality, adjunction *}

theorem leaf_step_natural: "\<Sigma>\<Sigma>_step_map f o leaf_step = leaf_step o f"
  using leaf_step_transfer[of "BNF_Def.Grp UNIV f"]
  unfolding \<Sigma>\<Sigma>_step.rel_Grp
  unfolding Grp_def rel_fun_def by auto

lemma \<oo>\<pp>_step_natural: "\<oo>\<pp>_step o \<Sigma>_step_map (\<Sigma>\<Sigma>_step_map f) = \<Sigma>\<Sigma>_step_map f o \<oo>\<pp>_step"
  using \<oo>\<pp>_step_transfer[of "BNF_Def.Grp UNIV f"]
  unfolding \<Sigma>_step.rel_Grp \<Sigma>\<Sigma>_step.rel_Grp \<Sigma>_step_map_def
  unfolding Grp_def rel_fun_def by auto

lemma \<Sigma>\<Sigma>_step_map_def2: "\<Sigma>\<Sigma>_step_map i = ext_step \<oo>\<pp>_step (leaf_step o i)"
by (rule ext_step_unique[OF leaf_step_natural \<oo>\<pp>_step_natural[symmetric]])

lemma ext_step_\<oo>\<pp>_step_leaf_step: "ext_step \<oo>\<pp>_step leaf_step = id"
apply (rule ext_step_unique[symmetric]) unfolding \<Sigma>_step.map_id0 o_id id_o by (rule refl)+

lemma ext_step_\<Sigma>\<Sigma>_step_map:
"ext_step s (j o f) = ext_step s j o \<Sigma>\<Sigma>_step_map f"
proof (rule ext_step_unique[symmetric])
  show "ext_step s j \<circ> \<Sigma>\<Sigma>_step_map f \<circ> leaf_step = j \<circ> f"
  unfolding o_assoc[symmetric] leaf_step_natural
  unfolding o_assoc ext_step_comp_leaf_step ..
next
  show "ext_step s j \<circ> \<Sigma>\<Sigma>_step_map f \<circ> \<oo>\<pp>_step = s \<circ> \<Sigma>_step_map (ext_step s j \<circ> \<Sigma>\<Sigma>_step_map f)"
  unfolding o_assoc[symmetric] \<oo>\<pp>_step_natural[symmetric]
  unfolding o_assoc ext_step_commute
  unfolding o_assoc[symmetric] \<Sigma>_step.map_comp0 ..
qed

lemma ext_step_\<Sigma>_step_map:
assumes "t o \<Sigma>_step_map f = f o s"
shows "ext_step t (f o i) = f o ext_step s i"
proof (rule ext_step_unique[symmetric])
  show "f \<circ> ext_step s i \<circ> leaf_step = f o i"
  unfolding o_assoc[symmetric] ext_step_comp_leaf_step ..
next
  show "f \<circ> ext_step s i \<circ> \<oo>\<pp>_step = t \<circ> \<Sigma>_step_map (f \<circ> ext_step s i)"
  unfolding \<Sigma>_step.map_comp0 o_assoc assms
  unfolding o_assoc[symmetric] ext_step_commute[symmetric] ..
qed


subsection{* Monadic laws *}

lemma flat_step_commute: "\<oo>\<pp>_step \<circ> \<Sigma>_step_map flat_step = flat_step \<circ> \<oo>\<pp>_step"
unfolding flat_step_def ext_step_commute ..

(* The 2 identity laws*)
theorem flat_step_leaf_step: "flat_step o leaf_step = id"
unfolding flat_step_def ext_step_comp_leaf_step ..

theorem leaf_step_flat_step: "flat_step o \<Sigma>\<Sigma>_step_map leaf_step = id"
unfolding flat_step_def ext_step_\<Sigma>\<Sigma>_step_map[symmetric] id_o ext_step_\<oo>\<pp>_step_leaf_step ..

theorem flat_step_natural: "flat_step o \<Sigma>\<Sigma>_step_map (\<Sigma>\<Sigma>_step_map i) = \<Sigma>\<Sigma>_step_map i o flat_step"
  using flat_step_transfer[of "BNF_Def.Grp UNIV i"]
  unfolding prod.rel_Grp \<Sigma>\<Sigma>_step.rel_Grp
  unfolding Grp_def rel_fun_def by auto

(* Associativity *)
theorem flat_step_assoc: "flat_step o \<Sigma>\<Sigma>_step_map flat_step = flat_step o flat_step"
unfolding flat_step_def unfolding ext_step_\<Sigma>\<Sigma>_step_map[symmetric] id_o
proof(rule ext_step_unique[symmetric], unfold flat_step_def[symmetric])
  show "flat_step \<circ> flat_step \<circ> leaf_step = flat_step"
  unfolding o_assoc[symmetric] flat_step_leaf_step o_id ..
next
  show "flat_step \<circ> flat_step \<circ> \<oo>\<pp>_step = \<oo>\<pp>_step \<circ> \<Sigma>_step_map (flat_step \<circ> flat_step)"
  unfolding flat_step_def unfolding o_assoc[symmetric] ext_step_commute
  unfolding flat_step_def[symmetric]
  unfolding \<Sigma>_step.map_comp0 o_assoc unfolding flat_step_commute ..
qed

definition K_step_as_\<Sigma>\<Sigma>_step :: "'a K_step \<Rightarrow> 'a \<Sigma>\<Sigma>_step" where
"K_step_as_\<Sigma>\<Sigma>_step \<equiv> \<oo>\<pp>_step o \<Sigma>_step_map leaf_step o Abs_\<Sigma>_step o Inr"

lemma K_step_as_\<Sigma>\<Sigma>_step_transfer[transfer_rule]:
  "(K_step_rel R ===> \<Sigma>\<Sigma>_step_rel R) K_step_as_\<Sigma>\<Sigma>_step K_step_as_\<Sigma>\<Sigma>_step"
  unfolding K_step_as_\<Sigma>\<Sigma>_step_def by transfer_prover

lemma K_step_as_\<Sigma>\<Sigma>_step_natural:
"K_step_as_\<Sigma>\<Sigma>_step o K_step_map f = \<Sigma>\<Sigma>_step_map f o K_step_as_\<Sigma>\<Sigma>_step"
  using K_step_as_\<Sigma>\<Sigma>_step_transfer[of "BNF_Def.Grp UNIV f"]
  unfolding K_step.rel_Grp \<Sigma>\<Sigma>_step.rel_Grp
  unfolding Grp_def rel_fun_def by auto

end