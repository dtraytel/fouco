header{* Free algebras for an BNF *}

(* Free algebra constructed for a sum of two BNF's S and K: *)
(* Notations: Identical to FreeAlg, just that constants and types are suffixed by "step" instead of "base": *)

theory Stream_FreeAlg9
imports Stream_Input9
begin

declare K9.map_transfer[transfer_rule]

(* The new-operation functor: *)

composition_bnf (open) raw_\<Sigma>9: "'a \<Sigma>8 + 'a K9"
typedef 'a \<Sigma>9 = "UNIV :: ('a \<Sigma>8 + 'a K9) set" by (rule UNIV_witness)

setup_lifting type_definition_\<Sigma>9

lift_definition \<Sigma>9_map :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Sigma>9 \<Rightarrow> 'b \<Sigma>9" is "\<lambda>f. map_sum (\<Sigma>8_map f) (K9_map f)" .
lift_definition \<Sigma>9_set :: "'a \<Sigma>9 \<Rightarrow> 'a set"
  is "\<lambda>x. UNION (Basic_BNFs.setl x) \<Sigma>8_set \<union> UNION (Basic_BNFs.setr x) K9_set" .
lift_definition \<Sigma>9_rel :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a \<Sigma>9 \<Rightarrow> 'b \<Sigma>9 \<Rightarrow> bool"
  is "\<lambda>R. rel_sum (\<Sigma>8_rel R) (K9_rel R)" .
typedef \<Sigma>9_bd_type = "UNIV :: ((\<Sigma>8_bd_type + bd_type_K9) \<times> nat) set" by (rule UNIV_witness)
definition "\<Sigma>9_bd = dir_image ((\<Sigma>8_bd +c bd_K9) *c natLeq) Abs_\<Sigma>9_bd_type"

bnf "'a \<Sigma>9"
  map: \<Sigma>9_map
  sets: \<Sigma>9_set
  bd: \<Sigma>9_bd 
  rel: \<Sigma>9_rel
unfolding \<Sigma>9_bd_def
apply -
apply transfer apply (rule raw_\<Sigma>9.map_id0)
apply transfer apply (rule raw_\<Sigma>9.map_comp0)
apply transfer apply (erule raw_\<Sigma>9.map_cong0)
apply transfer apply (rule raw_\<Sigma>9.set_map0)
apply (rule card_order_dir_image[OF bijI raw_\<Sigma>9.bd_card_order])
apply (metis inj_on_def Abs_\<Sigma>9_bd_type_inverse[OF UNIV_I])
apply (metis surj_def Abs_\<Sigma>9_bd_type_cases)
apply (rule conjunct1[OF Cinfinite_cong[OF dir_image[OF _ raw_\<Sigma>9.bd_Card_order] raw_\<Sigma>9.bd_Cinfinite]])
apply (metis Abs_\<Sigma>9_bd_type_inverse[OF UNIV_I])
apply (unfold \<Sigma>9_set_def map_fun_def id_o) [1] apply (subst o_apply)
apply (rule ordLeq_ordIso_trans[OF raw_\<Sigma>9.set_bd dir_image[OF _ raw_\<Sigma>9.bd_Card_order]])
apply (metis Abs_\<Sigma>9_bd_type_inverse[OF UNIV_I])
apply (rule predicate2I) apply transfer apply (subst raw_\<Sigma>9.rel_compp) apply assumption
apply transfer' apply (rule raw_\<Sigma>9.rel_compp_Grp)
done

declare \<Sigma>9.map_transfer[transfer_rule]

lemma Rep_\<Sigma>9_transfer[transfer_rule]: "(\<Sigma>9_rel R ===> rel_sum (\<Sigma>8_rel R) (K9_rel R)) Rep_\<Sigma>9 Rep_\<Sigma>9"
  unfolding rel_fun_def by transfer blast

lemma Abs_\<Sigma>9_transfer[transfer_rule]: "(rel_sum (\<Sigma>8_rel R) (K9_rel R) ===> \<Sigma>9_rel R) Abs_\<Sigma>9 Abs_\<Sigma>9"
  unfolding rel_fun_def by transfer blast

theorem Rep_\<Sigma>9_natural: "map_sum (\<Sigma>8_map f) (K9_map f) o Rep_\<Sigma>9 = Rep_\<Sigma>9 o \<Sigma>9_map f"
  using Rep_\<Sigma>9_transfer[of "BNF_Def.Grp UNIV f"]
  unfolding \<Sigma>9.rel_Grp raw_\<Sigma>9.rel_Grp
  unfolding Grp_def rel_fun_def by auto

theorem Abs_\<Sigma>9_natural: "\<Sigma>9_map f o Abs_\<Sigma>9 = Abs_\<Sigma>9 o map_sum (\<Sigma>8_map f) (K9_map f)"
  using Abs_\<Sigma>9_transfer[of "BNF_Def.Grp UNIV f"]
  unfolding \<Sigma>9.rel_Grp raw_\<Sigma>9.rel_Grp
  unfolding Grp_def rel_fun_def by auto

lemma Rep_\<Sigma>9_o_Abs_\<Sigma>9: "Rep_\<Sigma>9 o Abs_\<Sigma>9 = id"
  apply (rule ext)
  apply (rule box_equals[OF _ o_apply[symmetric] id_apply[symmetric]])
  apply (rule Abs_\<Sigma>9_inverse[OF UNIV_I])
  done

lemma \<Sigma>9_rel_\<Sigma>9_map_\<Sigma>9_map:
  "\<Sigma>9_rel R (\<Sigma>9_map f x) (\<Sigma>9_map g y) = \<Sigma>9_rel (BNF_Def.vimage2p f g R) x y"
  unfolding \<Sigma>9.rel_Grp vimage2p_Grp \<Sigma>9.rel_compp \<Sigma>9.rel_conversep
  unfolding relcompp.simps Grp_def by simp

subsection{* Definitions and basic setup *}

(* 'x \<Sigma>\<Sigma>9 consist of \<Sigma>9-terms with variables in 'x: *)
datatype_new (\<Sigma>\<Sigma>9_set: 'x) \<Sigma>\<Sigma>9 =
  \<oo>\<pp>9 "'x \<Sigma>\<Sigma>9 \<Sigma>9" | leaf9 "'x"
  for map: \<Sigma>\<Sigma>9_map rel: \<Sigma>\<Sigma>9_rel
declare \<Sigma>\<Sigma>9.ctor_fold_transfer
  [unfolded rel_pre_\<Sigma>\<Sigma>9_def id_apply BNF_Comp.id_bnf_comp_def vimage2p_def, transfer_rule]

lemma \<oo>\<pp>9_transfer[transfer_rule]:
  "(\<Sigma>9_rel (\<Sigma>\<Sigma>9_rel R) ===> \<Sigma>\<Sigma>9_rel R) \<oo>\<pp>9 \<oo>\<pp>9"
  by (rule rel_funI) (erule iffD2[OF \<Sigma>\<Sigma>9.rel_inject(1)])

lemma leaf9_transfer[transfer_rule]: "(R ===> \<Sigma>\<Sigma>9_rel R) leaf9 leaf9"
  by (rule rel_funI) (erule iffD2[OF \<Sigma>\<Sigma>9.rel_inject(2)])

(* The free extension, for an algebra s, of an inteprleaftion i of the
variables into the algebra carrier:  *)
abbreviation "ext9 s \<equiv> rec_\<Sigma>\<Sigma>9 (s o \<Sigma>9_map snd)"
lemmas ext9_\<oo>\<pp>9 = \<Sigma>\<Sigma>9.rec(1)[of "s o \<Sigma>9_map snd" for s,
  unfolded o_apply \<Sigma>9.map_comp snd_convol[unfolded convol_def]]
lemmas ext9_leaf9 = \<Sigma>\<Sigma>9.rec(2)[of "s o \<Sigma>9_map snd" for s,
  unfolded o_apply \<Sigma>9.map_comp snd_convol[unfolded convol_def]]
lemmas leaf9_inj = \<Sigma>\<Sigma>9.inject(2)
lemmas \<oo>\<pp>9_inj = \<Sigma>\<Sigma>9.inject(1)

lemma ext9_alt: "ext9 s f = ctor_fold_\<Sigma>\<Sigma>9 (case_sum s f)"
  apply (rule \<Sigma>\<Sigma>9.ctor_fold_unique)
  apply (rule ext)
  apply (rename_tac x)
  apply (case_tac x)
  apply (auto simp only: rec_\<Sigma>\<Sigma>9_def \<Sigma>\<Sigma>9.ctor_rec fun_eq_iff o_apply BNF_Comp.id_bnf_comp_def
    id_def[symmetric] o_id map_pre_\<Sigma>\<Sigma>9_def id_apply map_sum.simps sum.inject sum.distinct
    \<Sigma>9.map_comp snd_convol split: sum.splits)
  done

(* The term algebra: *)

lemma \<oo>\<pp>9_def_pointfree: "\<oo>\<pp>9 \<equiv> ctor_\<Sigma>\<Sigma>9 o Inl"
unfolding \<oo>\<pp>9_def comp_def BNF_Comp.id_bnf_comp_def .

(* Monadic structure *)
lemma leaf9_def_pointfree: "leaf9 \<equiv> ctor_\<Sigma>\<Sigma>9 o Inr"
unfolding leaf9_def comp_def BNF_Comp.id_bnf_comp_def .

definition flat9 :: "('x \<Sigma>\<Sigma>9) \<Sigma>\<Sigma>9 \<Rightarrow> 'x \<Sigma>\<Sigma>9" where
  flat9_def: "flat9 \<equiv> ext9 \<oo>\<pp>9 id"

lemma flat9_transfer[transfer_rule]: "(\<Sigma>\<Sigma>9_rel (\<Sigma>\<Sigma>9_rel R) ===> \<Sigma>\<Sigma>9_rel R) flat9 flat9"
  unfolding flat9_def ext9_alt by transfer_prover

(* facts about \<Sigma>\<Sigma>9: *)
lemma ctor_fold_\<Sigma>\<Sigma>9_pointfree:
"ctor_fold_\<Sigma>\<Sigma>9 s o ctor_\<Sigma>\<Sigma>9 = s o (map_pre_\<Sigma>\<Sigma>9 id (ctor_fold_\<Sigma>\<Sigma>9 s))"
unfolding comp_def \<Sigma>\<Sigma>9.ctor_fold ..

lemma \<Sigma>\<Sigma>9_map_ctor_\<Sigma>\<Sigma>9:
"\<Sigma>\<Sigma>9_map f o ctor_\<Sigma>\<Sigma>9 = ctor_\<Sigma>\<Sigma>9 o map_sum (\<Sigma>9_map (\<Sigma>\<Sigma>9_map f)) f"
unfolding comp_def
unfolding fun_eq_iff
unfolding \<Sigma>\<Sigma>9.ctor_map
unfolding map_pre_\<Sigma>\<Sigma>9_def  (* careful here and elsewhere: data newdatatype unfolds more *)
unfolding id_apply BNF_Comp.id_bnf_comp_def id_def[symmetric] o_id id_o by simp

lemma dtor_\<Sigma>\<Sigma>9_\<Sigma>\<Sigma>9_map:
"dtor_\<Sigma>\<Sigma>9 o \<Sigma>\<Sigma>9_map f = map_sum (\<Sigma>9_map (\<Sigma>\<Sigma>9_map f)) f o dtor_\<Sigma>\<Sigma>9"
using \<Sigma>\<Sigma>9_map_ctor_\<Sigma>\<Sigma>9[of f] \<Sigma>\<Sigma>9.dtor_ctor \<Sigma>\<Sigma>9.ctor_dtor unfolding comp_def fun_eq_iff by metis

lemma dtor_\<Sigma>\<Sigma>9_ctor_\<Sigma>\<Sigma>9: "dtor_\<Sigma>\<Sigma>9 \<circ> ctor_\<Sigma>\<Sigma>9 = id"
unfolding comp_def \<Sigma>\<Sigma>9.dtor_ctor id_def ..

lemma ctor_\<Sigma>\<Sigma>9_dtor_\<Sigma>\<Sigma>9: "ctor_\<Sigma>\<Sigma>9 \<circ> dtor_\<Sigma>\<Sigma>9 = id"
unfolding comp_def \<Sigma>\<Sigma>9.ctor_dtor id_def ..

lemma \<Sigma>\<Sigma>9_rel_inf: "\<Sigma>\<Sigma>9_rel (R \<sqinter> \<Sigma>8) \<le> \<Sigma>\<Sigma>9_rel R \<sqinter> \<Sigma>\<Sigma>9_rel \<Sigma>8"
  apply (rule inf_greatest)
  apply (rule \<Sigma>\<Sigma>9.rel_mono[OF inf_sup_ord(1)])
  apply (rule \<Sigma>\<Sigma>9.rel_mono[OF inf_sup_ord(2)])
  done

lemma \<Sigma>\<Sigma>9_rel_Grp_\<Sigma>\<Sigma>9_map: "\<Sigma>\<Sigma>9_rel (BNF_Def.Grp UNIV f) x y \<longleftrightarrow> \<Sigma>\<Sigma>9_map f x = y"
  unfolding \<Sigma>\<Sigma>9.rel_Grp by (auto simp: Grp_def)

lemma \<Sigma>\<Sigma>9_rel_\<Sigma>\<Sigma>9_map_\<Sigma>\<Sigma>9_map: "\<Sigma>\<Sigma>9_rel R (\<Sigma>\<Sigma>9_map f x) (\<Sigma>\<Sigma>9_map g y) =
  \<Sigma>\<Sigma>9_rel (BNF_Def.vimage2p f g R) x y"
  unfolding \<Sigma>\<Sigma>9.rel_Grp vimage2p_Grp apply (auto simp: \<Sigma>\<Sigma>9.rel_compp \<Sigma>\<Sigma>9.rel_conversep relcompp.simps)
  apply (intro exI conjI)
  apply (rule iffD2[OF \<Sigma>\<Sigma>9_rel_Grp_\<Sigma>\<Sigma>9_map refl])
  apply assumption
  apply (rule iffD2[OF \<Sigma>\<Sigma>9_rel_Grp_\<Sigma>\<Sigma>9_map refl])
  unfolding \<Sigma>\<Sigma>9_rel_Grp_\<Sigma>\<Sigma>9_map
  apply simp
  done


subsection{* @{term \<Sigma>9} extension theorems *}

theorem ext9_commute:
"ext9 s i o \<oo>\<pp>9 = s o \<Sigma>9_map (ext9 s i)"
unfolding ext9_alt \<oo>\<pp>9_def_pointfree o_assoc ctor_fold_\<Sigma>\<Sigma>9_pointfree map_pre_\<Sigma>\<Sigma>9_def
  case_sum_o_map_sum case_sum_o_inj(1) BNF_Comp.id_bnf_comp_def id_def[symmetric] o_id ..

theorem ext9_comp_leaf9:
"ext9 s i o leaf9 = i"
unfolding ext9_alt leaf9_def_pointfree o_assoc ctor_fold_\<Sigma>\<Sigma>9_pointfree map_pre_\<Sigma>\<Sigma>9_def
  case_sum_o_map_sum case_sum_o_inj(2) id_apply BNF_Comp.id_bnf_comp_def id_def[symmetric] o_id ..

theorem ext9_unique:
assumes leaf9: "f o leaf9 = i" and com: "f o \<oo>\<pp>9 = s o \<Sigma>9_map f"
shows "f = ext9 s i"
unfolding ext9_alt
apply (rule \<Sigma>\<Sigma>9.ctor_fold_unique)
apply (rule sum_comp_cases)
unfolding map_pre_\<Sigma>\<Sigma>9_def case_sum_o_map_sum id_apply o_id case_sum_o_inj
  leaf9[unfolded leaf9_def_pointfree o_assoc] com[unfolded \<oo>\<pp>9_def_pointfree o_assoc]
  BNF_Comp.id_bnf_comp_def id_def[symmetric] id_o
by (rule refl)+

subsection{* Customizing @{term \<Sigma>\<Sigma>9} *}

subsection{* Injectiveness, naturality, adjunction *}

theorem leaf9_natural: "\<Sigma>\<Sigma>9_map f o leaf9 = leaf9 o f"
  using leaf9_transfer[of "BNF_Def.Grp UNIV f"]
  unfolding \<Sigma>\<Sigma>9.rel_Grp
  unfolding Grp_def rel_fun_def by auto

lemma \<oo>\<pp>9_natural: "\<oo>\<pp>9 o \<Sigma>9_map (\<Sigma>\<Sigma>9_map f) = \<Sigma>\<Sigma>9_map f o \<oo>\<pp>9"
  using \<oo>\<pp>9_transfer[of "BNF_Def.Grp UNIV f"]
  unfolding \<Sigma>9.rel_Grp \<Sigma>\<Sigma>9.rel_Grp \<Sigma>9_map_def
  unfolding Grp_def rel_fun_def by auto

lemma \<Sigma>\<Sigma>9_map_def2: "\<Sigma>\<Sigma>9_map i = ext9 \<oo>\<pp>9 (leaf9 o i)"
by (rule ext9_unique[OF leaf9_natural \<oo>\<pp>9_natural[symmetric]])

lemma ext9_\<oo>\<pp>9_leaf9: "ext9 \<oo>\<pp>9 leaf9 = id"
apply (rule ext9_unique[symmetric]) unfolding \<Sigma>9.map_id0 o_id id_o by (rule refl)+

lemma ext9_\<Sigma>\<Sigma>9_map:
"ext9 s (j o f) = ext9 s j o \<Sigma>\<Sigma>9_map f"
proof (rule ext9_unique[symmetric])
  show "ext9 s j \<circ> \<Sigma>\<Sigma>9_map f \<circ> leaf9 = j \<circ> f"
  unfolding o_assoc[symmetric] leaf9_natural
  unfolding o_assoc ext9_comp_leaf9 ..
next
  show "ext9 s j \<circ> \<Sigma>\<Sigma>9_map f \<circ> \<oo>\<pp>9 = s \<circ> \<Sigma>9_map (ext9 s j \<circ> \<Sigma>\<Sigma>9_map f)"
  unfolding o_assoc[symmetric] \<oo>\<pp>9_natural[symmetric]
  unfolding o_assoc ext9_commute
  unfolding o_assoc[symmetric] \<Sigma>9.map_comp0 ..
qed

lemma ext9_\<Sigma>9_map:
assumes "t o \<Sigma>9_map f = f o s"
shows "ext9 t (f o i) = f o ext9 s i"
proof (rule ext9_unique[symmetric])
  show "f \<circ> ext9 s i \<circ> leaf9 = f o i"
  unfolding o_assoc[symmetric] ext9_comp_leaf9 ..
next
  show "f \<circ> ext9 s i \<circ> \<oo>\<pp>9 = t \<circ> \<Sigma>9_map (f \<circ> ext9 s i)"
  unfolding \<Sigma>9.map_comp0 o_assoc assms
  unfolding o_assoc[symmetric] ext9_commute[symmetric] ..
qed


subsection{* Monadic laws *}

lemma flat9_commute: "\<oo>\<pp>9 \<circ> \<Sigma>9_map flat9 = flat9 \<circ> \<oo>\<pp>9"
unfolding flat9_def ext9_commute ..

(* The 2 identity laws*)
theorem flat9_leaf9: "flat9 o leaf9 = id"
unfolding flat9_def ext9_comp_leaf9 ..

theorem leaf9_flat9: "flat9 o \<Sigma>\<Sigma>9_map leaf9 = id"
unfolding flat9_def ext9_\<Sigma>\<Sigma>9_map[symmetric] id_o ext9_\<oo>\<pp>9_leaf9 ..

theorem flat9_natural: "flat9 o \<Sigma>\<Sigma>9_map (\<Sigma>\<Sigma>9_map i) = \<Sigma>\<Sigma>9_map i o flat9"
  using flat9_transfer[of "BNF_Def.Grp UNIV i"]
  unfolding prod.rel_Grp \<Sigma>\<Sigma>9.rel_Grp
  unfolding Grp_def rel_fun_def by auto

(* Associativity *)
theorem flat9_assoc: "flat9 o \<Sigma>\<Sigma>9_map flat9 = flat9 o flat9"
unfolding flat9_def unfolding ext9_\<Sigma>\<Sigma>9_map[symmetric] id_o
proof(rule ext9_unique[symmetric], unfold flat9_def[symmetric])
  show "flat9 \<circ> flat9 \<circ> leaf9 = flat9"
  unfolding o_assoc[symmetric] flat9_leaf9 o_id ..
next
  show "flat9 \<circ> flat9 \<circ> \<oo>\<pp>9 = \<oo>\<pp>9 \<circ> \<Sigma>9_map (flat9 \<circ> flat9)"
  unfolding flat9_def unfolding o_assoc[symmetric] ext9_commute
  unfolding flat9_def[symmetric]
  unfolding \<Sigma>9.map_comp0 o_assoc unfolding flat9_commute ..
qed

definition K9_as_\<Sigma>\<Sigma>9 :: "'a K9 \<Rightarrow> 'a \<Sigma>\<Sigma>9" where
"K9_as_\<Sigma>\<Sigma>9 \<equiv> \<oo>\<pp>9 o \<Sigma>9_map leaf9 o Abs_\<Sigma>9 o Inr"

lemma K9_as_\<Sigma>\<Sigma>9_transfer[transfer_rule]:
  "(K9_rel R ===> \<Sigma>\<Sigma>9_rel R) K9_as_\<Sigma>\<Sigma>9 K9_as_\<Sigma>\<Sigma>9"
  unfolding K9_as_\<Sigma>\<Sigma>9_def by transfer_prover

lemma K9_as_\<Sigma>\<Sigma>9_natural:
"K9_as_\<Sigma>\<Sigma>9 o K9_map f = \<Sigma>\<Sigma>9_map f o K9_as_\<Sigma>\<Sigma>9"
  using K9_as_\<Sigma>\<Sigma>9_transfer[of "BNF_Def.Grp UNIV f"]
  unfolding K9.rel_Grp \<Sigma>\<Sigma>9.rel_Grp
  unfolding Grp_def rel_fun_def by auto

end