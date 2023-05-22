header{* Free algebras for an BNF *}

(* Free algebra constructed for a sum of two BNF's S and K: *)
(* Notations: Identical to FreeAlg, just that constants and types are suffixed by "step" instead of "base": *)

theory Stream_FreeAlg7
imports Stream_Input7
begin

declare K7.map_transfer[transfer_rule]

(* The new-operation functor: *)

composition_bnf (open) raw_\<Sigma>7: "'a \<Sigma>6 + 'a K7"
typedef 'a \<Sigma>7 = "UNIV :: ('a \<Sigma>6 + 'a K7) set" by (rule UNIV_witness)

setup_lifting type_definition_\<Sigma>7

lift_definition \<Sigma>7_map :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Sigma>7 \<Rightarrow> 'b \<Sigma>7" is "\<lambda>f. map_sum (\<Sigma>6_map f) (K7_map f)" .
lift_definition \<Sigma>7_set :: "'a \<Sigma>7 \<Rightarrow> 'a set"
  is "\<lambda>x. UNION (Basic_BNFs.setl x) \<Sigma>6_set \<union> UNION (Basic_BNFs.setr x) K7_set" .
lift_definition \<Sigma>7_rel :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a \<Sigma>7 \<Rightarrow> 'b \<Sigma>7 \<Rightarrow> bool"
  is "\<lambda>R. rel_sum (\<Sigma>6_rel R) (K7_rel R)" .
typedef \<Sigma>7_bd_type = "UNIV :: ((\<Sigma>6_bd_type + bd_type_K7) \<times> nat) set" by (rule UNIV_witness)
definition "\<Sigma>7_bd = dir_image ((\<Sigma>6_bd +c bd_K7) *c natLeq) Abs_\<Sigma>7_bd_type"

bnf "'a \<Sigma>7"
  map: \<Sigma>7_map
  sets: \<Sigma>7_set
  bd: \<Sigma>7_bd 
  rel: \<Sigma>7_rel
unfolding \<Sigma>7_bd_def
apply -
apply transfer apply (rule raw_\<Sigma>7.map_id0)
apply transfer apply (rule raw_\<Sigma>7.map_comp0)
apply transfer apply (erule raw_\<Sigma>7.map_cong0)
apply transfer apply (rule raw_\<Sigma>7.set_map0)
apply (rule card_order_dir_image[OF bijI raw_\<Sigma>7.bd_card_order])
apply (metis inj_on_def Abs_\<Sigma>7_bd_type_inverse[OF UNIV_I])
apply (metis surj_def Abs_\<Sigma>7_bd_type_cases)
apply (rule conjunct1[OF Cinfinite_cong[OF dir_image[OF _ raw_\<Sigma>7.bd_Card_order] raw_\<Sigma>7.bd_Cinfinite]])
apply (metis Abs_\<Sigma>7_bd_type_inverse[OF UNIV_I])
apply (unfold \<Sigma>7_set_def map_fun_def id_o) [1] apply (subst o_apply)
apply (rule ordLeq_ordIso_trans[OF raw_\<Sigma>7.set_bd dir_image[OF _ raw_\<Sigma>7.bd_Card_order]])
apply (metis Abs_\<Sigma>7_bd_type_inverse[OF UNIV_I])
apply (rule predicate2I) apply transfer apply (subst raw_\<Sigma>7.rel_compp) apply assumption
apply transfer' apply (rule raw_\<Sigma>7.rel_compp_Grp)
done

declare \<Sigma>7.map_transfer[transfer_rule]

lemma Rep_\<Sigma>7_transfer[transfer_rule]: "(\<Sigma>7_rel R ===> rel_sum (\<Sigma>6_rel R) (K7_rel R)) Rep_\<Sigma>7 Rep_\<Sigma>7"
  unfolding rel_fun_def by transfer blast

lemma Abs_\<Sigma>7_transfer[transfer_rule]: "(rel_sum (\<Sigma>6_rel R) (K7_rel R) ===> \<Sigma>7_rel R) Abs_\<Sigma>7 Abs_\<Sigma>7"
  unfolding rel_fun_def by transfer blast

theorem Rep_\<Sigma>7_natural: "map_sum (\<Sigma>6_map f) (K7_map f) o Rep_\<Sigma>7 = Rep_\<Sigma>7 o \<Sigma>7_map f"
  using Rep_\<Sigma>7_transfer[of "BNF_Def.Grp UNIV f"]
  unfolding \<Sigma>7.rel_Grp raw_\<Sigma>7.rel_Grp
  unfolding Grp_def rel_fun_def by auto

theorem Abs_\<Sigma>7_natural: "\<Sigma>7_map f o Abs_\<Sigma>7 = Abs_\<Sigma>7 o map_sum (\<Sigma>6_map f) (K7_map f)"
  using Abs_\<Sigma>7_transfer[of "BNF_Def.Grp UNIV f"]
  unfolding \<Sigma>7.rel_Grp raw_\<Sigma>7.rel_Grp
  unfolding Grp_def rel_fun_def by auto

lemma Rep_\<Sigma>7_o_Abs_\<Sigma>7: "Rep_\<Sigma>7 o Abs_\<Sigma>7 = id"
  apply (rule ext)
  apply (rule box_equals[OF _ o_apply[symmetric] id_apply[symmetric]])
  apply (rule Abs_\<Sigma>7_inverse[OF UNIV_I])
  done

lemma \<Sigma>7_rel_\<Sigma>7_map_\<Sigma>7_map:
  "\<Sigma>7_rel R (\<Sigma>7_map f x) (\<Sigma>7_map g y) = \<Sigma>7_rel (BNF_Def.vimage2p f g R) x y"
  unfolding \<Sigma>7.rel_Grp vimage2p_Grp \<Sigma>7.rel_compp \<Sigma>7.rel_conversep
  unfolding relcompp.simps Grp_def by simp

subsection{* Definitions and basic setup *}

(* 'x \<Sigma>\<Sigma>7 consist of \<Sigma>7-terms with variables in 'x: *)
datatype_new (\<Sigma>\<Sigma>7_set: 'x) \<Sigma>\<Sigma>7 =
  \<oo>\<pp>7 "'x \<Sigma>\<Sigma>7 \<Sigma>7" | leaf7 "'x"
  for map: \<Sigma>\<Sigma>7_map rel: \<Sigma>\<Sigma>7_rel
declare \<Sigma>\<Sigma>7.ctor_fold_transfer
  [unfolded rel_pre_\<Sigma>\<Sigma>7_def id_apply BNF_Comp.id_bnf_comp_def vimage2p_def, transfer_rule]

lemma \<oo>\<pp>7_transfer[transfer_rule]:
  "(\<Sigma>7_rel (\<Sigma>\<Sigma>7_rel R) ===> \<Sigma>\<Sigma>7_rel R) \<oo>\<pp>7 \<oo>\<pp>7"
  by (rule rel_funI) (erule iffD2[OF \<Sigma>\<Sigma>7.rel_inject(1)])

lemma leaf7_transfer[transfer_rule]: "(R ===> \<Sigma>\<Sigma>7_rel R) leaf7 leaf7"
  by (rule rel_funI) (erule iffD2[OF \<Sigma>\<Sigma>7.rel_inject(2)])

(* The free extension, for an algebra s, of an inteprleaftion i of the
variables into the algebra carrier:  *)
abbreviation "ext7 s \<equiv> rec_\<Sigma>\<Sigma>7 (s o \<Sigma>7_map snd)"
lemmas ext7_\<oo>\<pp>7 = \<Sigma>\<Sigma>7.rec(1)[of "s o \<Sigma>7_map snd" for s,
  unfolded o_apply \<Sigma>7.map_comp snd_convol[unfolded convol_def]]
lemmas ext7_leaf7 = \<Sigma>\<Sigma>7.rec(2)[of "s o \<Sigma>7_map snd" for s,
  unfolded o_apply \<Sigma>7.map_comp snd_convol[unfolded convol_def]]
lemmas leaf7_inj = \<Sigma>\<Sigma>7.inject(2)
lemmas \<oo>\<pp>7_inj = \<Sigma>\<Sigma>7.inject(1)

lemma ext7_alt: "ext7 s f = ctor_fold_\<Sigma>\<Sigma>7 (case_sum s f)"
  apply (rule \<Sigma>\<Sigma>7.ctor_fold_unique)
  apply (rule ext)
  apply (rename_tac x)
  apply (case_tac x)
  apply (auto simp only: rec_\<Sigma>\<Sigma>7_def \<Sigma>\<Sigma>7.ctor_rec fun_eq_iff o_apply BNF_Comp.id_bnf_comp_def
    id_def[symmetric] o_id map_pre_\<Sigma>\<Sigma>7_def id_apply map_sum.simps sum.inject sum.distinct
    \<Sigma>7.map_comp snd_convol split: sum.splits)
  done

(* The term algebra: *)

lemma \<oo>\<pp>7_def_pointfree: "\<oo>\<pp>7 \<equiv> ctor_\<Sigma>\<Sigma>7 o Inl"
unfolding \<oo>\<pp>7_def comp_def BNF_Comp.id_bnf_comp_def .

(* Monadic structure *)
lemma leaf7_def_pointfree: "leaf7 \<equiv> ctor_\<Sigma>\<Sigma>7 o Inr"
unfolding leaf7_def comp_def BNF_Comp.id_bnf_comp_def .

definition flat7 :: "('x \<Sigma>\<Sigma>7) \<Sigma>\<Sigma>7 \<Rightarrow> 'x \<Sigma>\<Sigma>7" where
  flat7_def: "flat7 \<equiv> ext7 \<oo>\<pp>7 id"

lemma flat7_transfer[transfer_rule]: "(\<Sigma>\<Sigma>7_rel (\<Sigma>\<Sigma>7_rel R) ===> \<Sigma>\<Sigma>7_rel R) flat7 flat7"
  unfolding flat7_def ext7_alt by transfer_prover

(* facts about \<Sigma>\<Sigma>7: *)
lemma ctor_fold_\<Sigma>\<Sigma>7_pointfree:
"ctor_fold_\<Sigma>\<Sigma>7 s o ctor_\<Sigma>\<Sigma>7 = s o (map_pre_\<Sigma>\<Sigma>7 id (ctor_fold_\<Sigma>\<Sigma>7 s))"
unfolding comp_def \<Sigma>\<Sigma>7.ctor_fold ..

lemma \<Sigma>\<Sigma>7_map_ctor_\<Sigma>\<Sigma>7:
"\<Sigma>\<Sigma>7_map f o ctor_\<Sigma>\<Sigma>7 = ctor_\<Sigma>\<Sigma>7 o map_sum (\<Sigma>7_map (\<Sigma>\<Sigma>7_map f)) f"
unfolding comp_def
unfolding fun_eq_iff
unfolding \<Sigma>\<Sigma>7.ctor_map
unfolding map_pre_\<Sigma>\<Sigma>7_def  (* careful here and elsewhere: data newdatatype unfolds more *)
unfolding id_apply BNF_Comp.id_bnf_comp_def id_def[symmetric] o_id id_o by simp

lemma dtor_\<Sigma>\<Sigma>7_\<Sigma>\<Sigma>7_map:
"dtor_\<Sigma>\<Sigma>7 o \<Sigma>\<Sigma>7_map f = map_sum (\<Sigma>7_map (\<Sigma>\<Sigma>7_map f)) f o dtor_\<Sigma>\<Sigma>7"
using \<Sigma>\<Sigma>7_map_ctor_\<Sigma>\<Sigma>7[of f] \<Sigma>\<Sigma>7.dtor_ctor \<Sigma>\<Sigma>7.ctor_dtor unfolding comp_def fun_eq_iff by metis

lemma dtor_\<Sigma>\<Sigma>7_ctor_\<Sigma>\<Sigma>7: "dtor_\<Sigma>\<Sigma>7 \<circ> ctor_\<Sigma>\<Sigma>7 = id"
unfolding comp_def \<Sigma>\<Sigma>7.dtor_ctor id_def ..

lemma ctor_\<Sigma>\<Sigma>7_dtor_\<Sigma>\<Sigma>7: "ctor_\<Sigma>\<Sigma>7 \<circ> dtor_\<Sigma>\<Sigma>7 = id"
unfolding comp_def \<Sigma>\<Sigma>7.ctor_dtor id_def ..

lemma \<Sigma>\<Sigma>7_rel_inf: "\<Sigma>\<Sigma>7_rel (R \<sqinter> \<Sigma>6) \<le> \<Sigma>\<Sigma>7_rel R \<sqinter> \<Sigma>\<Sigma>7_rel \<Sigma>6"
  apply (rule inf_greatest)
  apply (rule \<Sigma>\<Sigma>7.rel_mono[OF inf_sup_ord(1)])
  apply (rule \<Sigma>\<Sigma>7.rel_mono[OF inf_sup_ord(2)])
  done

lemma \<Sigma>\<Sigma>7_rel_Grp_\<Sigma>\<Sigma>7_map: "\<Sigma>\<Sigma>7_rel (BNF_Def.Grp UNIV f) x y \<longleftrightarrow> \<Sigma>\<Sigma>7_map f x = y"
  unfolding \<Sigma>\<Sigma>7.rel_Grp by (auto simp: Grp_def)

lemma \<Sigma>\<Sigma>7_rel_\<Sigma>\<Sigma>7_map_\<Sigma>\<Sigma>7_map: "\<Sigma>\<Sigma>7_rel R (\<Sigma>\<Sigma>7_map f x) (\<Sigma>\<Sigma>7_map g y) =
  \<Sigma>\<Sigma>7_rel (BNF_Def.vimage2p f g R) x y"
  unfolding \<Sigma>\<Sigma>7.rel_Grp vimage2p_Grp apply (auto simp: \<Sigma>\<Sigma>7.rel_compp \<Sigma>\<Sigma>7.rel_conversep relcompp.simps)
  apply (intro exI conjI)
  apply (rule iffD2[OF \<Sigma>\<Sigma>7_rel_Grp_\<Sigma>\<Sigma>7_map refl])
  apply assumption
  apply (rule iffD2[OF \<Sigma>\<Sigma>7_rel_Grp_\<Sigma>\<Sigma>7_map refl])
  unfolding \<Sigma>\<Sigma>7_rel_Grp_\<Sigma>\<Sigma>7_map
  apply simp
  done


subsection{* @{term \<Sigma>7} extension theorems *}

theorem ext7_commute:
"ext7 s i o \<oo>\<pp>7 = s o \<Sigma>7_map (ext7 s i)"
unfolding ext7_alt \<oo>\<pp>7_def_pointfree o_assoc ctor_fold_\<Sigma>\<Sigma>7_pointfree map_pre_\<Sigma>\<Sigma>7_def
  case_sum_o_map_sum case_sum_o_inj(1) BNF_Comp.id_bnf_comp_def id_def[symmetric] o_id ..

theorem ext7_comp_leaf7:
"ext7 s i o leaf7 = i"
unfolding ext7_alt leaf7_def_pointfree o_assoc ctor_fold_\<Sigma>\<Sigma>7_pointfree map_pre_\<Sigma>\<Sigma>7_def
  case_sum_o_map_sum case_sum_o_inj(2) id_apply BNF_Comp.id_bnf_comp_def id_def[symmetric] o_id ..

theorem ext7_unique:
assumes leaf7: "f o leaf7 = i" and com: "f o \<oo>\<pp>7 = s o \<Sigma>7_map f"
shows "f = ext7 s i"
unfolding ext7_alt
apply (rule \<Sigma>\<Sigma>7.ctor_fold_unique)
apply (rule sum_comp_cases)
unfolding map_pre_\<Sigma>\<Sigma>7_def case_sum_o_map_sum id_apply o_id case_sum_o_inj
  leaf7[unfolded leaf7_def_pointfree o_assoc] com[unfolded \<oo>\<pp>7_def_pointfree o_assoc]
  BNF_Comp.id_bnf_comp_def id_def[symmetric] id_o
by (rule refl)+

subsection{* Customizing @{term \<Sigma>\<Sigma>7} *}

subsection{* Injectiveness, naturality, adjunction *}

theorem leaf7_natural: "\<Sigma>\<Sigma>7_map f o leaf7 = leaf7 o f"
  using leaf7_transfer[of "BNF_Def.Grp UNIV f"]
  unfolding \<Sigma>\<Sigma>7.rel_Grp
  unfolding Grp_def rel_fun_def by auto

lemma \<oo>\<pp>7_natural: "\<oo>\<pp>7 o \<Sigma>7_map (\<Sigma>\<Sigma>7_map f) = \<Sigma>\<Sigma>7_map f o \<oo>\<pp>7"
  using \<oo>\<pp>7_transfer[of "BNF_Def.Grp UNIV f"]
  unfolding \<Sigma>7.rel_Grp \<Sigma>\<Sigma>7.rel_Grp \<Sigma>7_map_def
  unfolding Grp_def rel_fun_def by auto

lemma \<Sigma>\<Sigma>7_map_def2: "\<Sigma>\<Sigma>7_map i = ext7 \<oo>\<pp>7 (leaf7 o i)"
by (rule ext7_unique[OF leaf7_natural \<oo>\<pp>7_natural[symmetric]])

lemma ext7_\<oo>\<pp>7_leaf7: "ext7 \<oo>\<pp>7 leaf7 = id"
apply (rule ext7_unique[symmetric]) unfolding \<Sigma>7.map_id0 o_id id_o by (rule refl)+

lemma ext7_\<Sigma>\<Sigma>7_map:
"ext7 s (j o f) = ext7 s j o \<Sigma>\<Sigma>7_map f"
proof (rule ext7_unique[symmetric])
  show "ext7 s j \<circ> \<Sigma>\<Sigma>7_map f \<circ> leaf7 = j \<circ> f"
  unfolding o_assoc[symmetric] leaf7_natural
  unfolding o_assoc ext7_comp_leaf7 ..
next
  show "ext7 s j \<circ> \<Sigma>\<Sigma>7_map f \<circ> \<oo>\<pp>7 = s \<circ> \<Sigma>7_map (ext7 s j \<circ> \<Sigma>\<Sigma>7_map f)"
  unfolding o_assoc[symmetric] \<oo>\<pp>7_natural[symmetric]
  unfolding o_assoc ext7_commute
  unfolding o_assoc[symmetric] \<Sigma>7.map_comp0 ..
qed

lemma ext7_\<Sigma>7_map:
assumes "t o \<Sigma>7_map f = f o s"
shows "ext7 t (f o i) = f o ext7 s i"
proof (rule ext7_unique[symmetric])
  show "f \<circ> ext7 s i \<circ> leaf7 = f o i"
  unfolding o_assoc[symmetric] ext7_comp_leaf7 ..
next
  show "f \<circ> ext7 s i \<circ> \<oo>\<pp>7 = t \<circ> \<Sigma>7_map (f \<circ> ext7 s i)"
  unfolding \<Sigma>7.map_comp0 o_assoc assms
  unfolding o_assoc[symmetric] ext7_commute[symmetric] ..
qed


subsection{* Monadic laws *}

lemma flat7_commute: "\<oo>\<pp>7 \<circ> \<Sigma>7_map flat7 = flat7 \<circ> \<oo>\<pp>7"
unfolding flat7_def ext7_commute ..

(* The 2 identity laws*)
theorem flat7_leaf7: "flat7 o leaf7 = id"
unfolding flat7_def ext7_comp_leaf7 ..

theorem leaf7_flat7: "flat7 o \<Sigma>\<Sigma>7_map leaf7 = id"
unfolding flat7_def ext7_\<Sigma>\<Sigma>7_map[symmetric] id_o ext7_\<oo>\<pp>7_leaf7 ..

theorem flat7_natural: "flat7 o \<Sigma>\<Sigma>7_map (\<Sigma>\<Sigma>7_map i) = \<Sigma>\<Sigma>7_map i o flat7"
  using flat7_transfer[of "BNF_Def.Grp UNIV i"]
  unfolding prod.rel_Grp \<Sigma>\<Sigma>7.rel_Grp
  unfolding Grp_def rel_fun_def by auto

(* Associativity *)
theorem flat7_assoc: "flat7 o \<Sigma>\<Sigma>7_map flat7 = flat7 o flat7"
unfolding flat7_def unfolding ext7_\<Sigma>\<Sigma>7_map[symmetric] id_o
proof(rule ext7_unique[symmetric], unfold flat7_def[symmetric])
  show "flat7 \<circ> flat7 \<circ> leaf7 = flat7"
  unfolding o_assoc[symmetric] flat7_leaf7 o_id ..
next
  show "flat7 \<circ> flat7 \<circ> \<oo>\<pp>7 = \<oo>\<pp>7 \<circ> \<Sigma>7_map (flat7 \<circ> flat7)"
  unfolding flat7_def unfolding o_assoc[symmetric] ext7_commute
  unfolding flat7_def[symmetric]
  unfolding \<Sigma>7.map_comp0 o_assoc unfolding flat7_commute ..
qed

definition K7_as_\<Sigma>\<Sigma>7 :: "'a K7 \<Rightarrow> 'a \<Sigma>\<Sigma>7" where
"K7_as_\<Sigma>\<Sigma>7 \<equiv> \<oo>\<pp>7 o \<Sigma>7_map leaf7 o Abs_\<Sigma>7 o Inr"

lemma K7_as_\<Sigma>\<Sigma>7_transfer[transfer_rule]:
  "(K7_rel R ===> \<Sigma>\<Sigma>7_rel R) K7_as_\<Sigma>\<Sigma>7 K7_as_\<Sigma>\<Sigma>7"
  unfolding K7_as_\<Sigma>\<Sigma>7_def by transfer_prover

lemma K7_as_\<Sigma>\<Sigma>7_natural:
"K7_as_\<Sigma>\<Sigma>7 o K7_map f = \<Sigma>\<Sigma>7_map f o K7_as_\<Sigma>\<Sigma>7"
  using K7_as_\<Sigma>\<Sigma>7_transfer[of "BNF_Def.Grp UNIV f"]
  unfolding K7.rel_Grp \<Sigma>\<Sigma>7.rel_Grp
  unfolding Grp_def rel_fun_def by auto

end