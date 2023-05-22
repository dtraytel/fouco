header{* Free algebras for an BNF *}

(* Free algebra constructed for a sum of two BNF's S and K: *)
(* Notations: Identical to FreeAlg, just that constants and types are suffixed by "step" instead of "base": *)

theory Tree_FreeAlg2
imports Tree_Input2
begin

declare K2.map_transfer[transfer_rule]

(* The new-operation functor: *)

composition_bnf (open) raw_\<Sigma>2: "'a \<Sigma>1 + 'a K2"
typedef 'a \<Sigma>2 = "UNIV :: ('a \<Sigma>1 + 'a K2) set" by (rule UNIV_witness)

setup_lifting type_definition_\<Sigma>2

lift_definition \<Sigma>2_map :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Sigma>2 \<Rightarrow> 'b \<Sigma>2" is "\<lambda>f. map_sum (\<Sigma>1_map f) (K2_map f)" .
lift_definition \<Sigma>2_set :: "'a \<Sigma>2 \<Rightarrow> 'a set"
  is "\<lambda>x. UNION (Basic_BNFs.setl x) \<Sigma>1_set \<union> UNION (Basic_BNFs.setr x) K2_set" .
lift_definition \<Sigma>2_rel :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a \<Sigma>2 \<Rightarrow> 'b \<Sigma>2 \<Rightarrow> bool"
  is "\<lambda>R. rel_sum (\<Sigma>1_rel R) (K2_rel R)" .
typedef \<Sigma>2_bd_type = "UNIV :: ((\<Sigma>1_bd_type + bd_type_K2) \<times> nat) set" by (rule UNIV_witness)
definition "\<Sigma>2_bd = dir_image ((\<Sigma>1_bd +c bd_K2) *c natLeq) Abs_\<Sigma>2_bd_type"

bnf "'a \<Sigma>2"
  map: \<Sigma>2_map
  sets: \<Sigma>2_set
  bd: \<Sigma>2_bd 
  rel: \<Sigma>2_rel
unfolding \<Sigma>2_bd_def
apply -
apply transfer apply (rule raw_\<Sigma>2.map_id0)
apply transfer apply (rule raw_\<Sigma>2.map_comp0)
apply transfer apply (erule raw_\<Sigma>2.map_cong0)
apply transfer apply (rule raw_\<Sigma>2.set_map0)
apply (rule card_order_dir_image[OF bijI raw_\<Sigma>2.bd_card_order])
apply (metis inj_on_def Abs_\<Sigma>2_bd_type_inverse[OF UNIV_I])
apply (metis surj_def Abs_\<Sigma>2_bd_type_cases)
apply (rule conjunct1[OF Cinfinite_cong[OF dir_image[OF _ raw_\<Sigma>2.bd_Card_order] raw_\<Sigma>2.bd_Cinfinite]])
apply (metis Abs_\<Sigma>2_bd_type_inverse[OF UNIV_I])
apply (unfold \<Sigma>2_set_def map_fun_def id_o) [1] apply (subst o_apply)
apply (rule ordLeq_ordIso_trans[OF raw_\<Sigma>2.set_bd dir_image[OF _ raw_\<Sigma>2.bd_Card_order]])
apply (metis Abs_\<Sigma>2_bd_type_inverse[OF UNIV_I])
apply (rule predicate2I) apply transfer apply (subst raw_\<Sigma>2.rel_compp) apply assumption
apply transfer' apply (rule raw_\<Sigma>2.rel_compp_Grp)
done

declare \<Sigma>2.map_transfer[transfer_rule]

lemma Rep_\<Sigma>2_transfer[transfer_rule]: "(\<Sigma>2_rel R ===> rel_sum (\<Sigma>1_rel R) (K2_rel R)) Rep_\<Sigma>2 Rep_\<Sigma>2"
  unfolding rel_fun_def by transfer blast

lemma Abs_\<Sigma>2_transfer[transfer_rule]: "(rel_sum (\<Sigma>1_rel R) (K2_rel R) ===> \<Sigma>2_rel R) Abs_\<Sigma>2 Abs_\<Sigma>2"
  unfolding rel_fun_def by transfer blast

theorem Rep_\<Sigma>2_natural: "map_sum (\<Sigma>1_map f) (K2_map f) o Rep_\<Sigma>2 = Rep_\<Sigma>2 o \<Sigma>2_map f"
  using Rep_\<Sigma>2_transfer[of "BNF_Def.Grp UNIV f"]
  unfolding \<Sigma>2.rel_Grp raw_\<Sigma>2.rel_Grp
  unfolding Grp_def rel_fun_def by auto

theorem Abs_\<Sigma>2_natural: "\<Sigma>2_map f o Abs_\<Sigma>2 = Abs_\<Sigma>2 o map_sum (\<Sigma>1_map f) (K2_map f)"
  using Abs_\<Sigma>2_transfer[of "BNF_Def.Grp UNIV f"]
  unfolding \<Sigma>2.rel_Grp raw_\<Sigma>2.rel_Grp
  unfolding Grp_def rel_fun_def by auto

lemma Rep_\<Sigma>2_o_Abs_\<Sigma>2: "Rep_\<Sigma>2 o Abs_\<Sigma>2 = id"
  apply (rule ext)
  apply (rule box_equals[OF _ o_apply[symmetric] id_apply[symmetric]])
  apply (rule Abs_\<Sigma>2_inverse[OF UNIV_I])
  done

lemma \<Sigma>2_rel_\<Sigma>2_map_\<Sigma>2_map:
  "\<Sigma>2_rel R (\<Sigma>2_map f x) (\<Sigma>2_map g y) = \<Sigma>2_rel (BNF_Def.vimage2p f g R) x y"
  unfolding \<Sigma>2.rel_Grp vimage2p_Grp \<Sigma>2.rel_compp \<Sigma>2.rel_conversep
  unfolding relcompp.simps Grp_def by simp

subsection{* Definitions and basic setup *}

(* 'x \<Sigma>\<Sigma>2 consist of \<Sigma>2-terms with variables in 'x: *)
datatype_new (\<Sigma>\<Sigma>2_set: 'x) \<Sigma>\<Sigma>2 =
  \<oo>\<pp>2 "'x \<Sigma>\<Sigma>2 \<Sigma>2" | leaf2 "'x"
  for map: \<Sigma>\<Sigma>2_map rel: \<Sigma>\<Sigma>2_rel
declare \<Sigma>\<Sigma>2.ctor_fold_transfer
  [unfolded rel_pre_\<Sigma>\<Sigma>2_def id_apply BNF_Comp.id_bnf_comp_def vimage2p_def, transfer_rule]

lemma \<oo>\<pp>2_transfer[transfer_rule]:
  "(\<Sigma>2_rel (\<Sigma>\<Sigma>2_rel R) ===> \<Sigma>\<Sigma>2_rel R) \<oo>\<pp>2 \<oo>\<pp>2"
  by (rule rel_funI) (erule iffD2[OF \<Sigma>\<Sigma>2.rel_inject(1)])

lemma leaf2_transfer[transfer_rule]: "(R ===> \<Sigma>\<Sigma>2_rel R) leaf2 leaf2"
  by (rule rel_funI) (erule iffD2[OF \<Sigma>\<Sigma>2.rel_inject(2)])

(* The free extension, for an algebra s, of an inteprleaftion i of the
variables into the algebra carrier:  *)
abbreviation "ext2 s \<equiv> rec_\<Sigma>\<Sigma>2 (s o \<Sigma>2_map snd)"
lemmas ext2_\<oo>\<pp>2 = \<Sigma>\<Sigma>2.rec(1)[of "s o \<Sigma>2_map snd" for s,
  unfolded o_apply \<Sigma>2.map_comp snd_convol[unfolded convol_def]]
lemmas ext2_leaf2 = \<Sigma>\<Sigma>2.rec(2)[of "s o \<Sigma>2_map snd" for s,
  unfolded o_apply \<Sigma>2.map_comp snd_convol[unfolded convol_def]]
lemmas leaf2_inj = \<Sigma>\<Sigma>2.inject(2)
lemmas \<oo>\<pp>2_inj = \<Sigma>\<Sigma>2.inject(1)

lemma ext2_alt: "ext2 s f = ctor_fold_\<Sigma>\<Sigma>2 (case_sum s f)"
  apply (rule \<Sigma>\<Sigma>2.ctor_fold_unique)
  apply (rule ext)
  apply (rename_tac x)
  apply (case_tac x)
  apply (auto simp only: rec_\<Sigma>\<Sigma>2_def \<Sigma>\<Sigma>2.ctor_rec fun_eq_iff o_apply BNF_Comp.id_bnf_comp_def
    id_def[symmetric] o_id map_pre_\<Sigma>\<Sigma>2_def id_apply map_sum.simps sum.inject sum.distinct
    \<Sigma>2.map_comp snd_convol split: sum.splits)
  done

(* The term algebra: *)

lemma \<oo>\<pp>2_def_pointfree: "\<oo>\<pp>2 \<equiv> ctor_\<Sigma>\<Sigma>2 o Inl"
unfolding \<oo>\<pp>2_def comp_def BNF_Comp.id_bnf_comp_def .

(* Monadic structure *)
lemma leaf2_def_pointfree: "leaf2 \<equiv> ctor_\<Sigma>\<Sigma>2 o Inr"
unfolding leaf2_def comp_def BNF_Comp.id_bnf_comp_def .

definition flat2 :: "('x \<Sigma>\<Sigma>2) \<Sigma>\<Sigma>2 \<Rightarrow> 'x \<Sigma>\<Sigma>2" where
  flat2_def: "flat2 \<equiv> ext2 \<oo>\<pp>2 id"

lemma flat2_transfer[transfer_rule]: "(\<Sigma>\<Sigma>2_rel (\<Sigma>\<Sigma>2_rel R) ===> \<Sigma>\<Sigma>2_rel R) flat2 flat2"
  unfolding flat2_def ext2_alt by transfer_prover

(* facts about \<Sigma>\<Sigma>2: *)
lemma ctor_fold_\<Sigma>\<Sigma>2_pointfree:
"ctor_fold_\<Sigma>\<Sigma>2 s o ctor_\<Sigma>\<Sigma>2 = s o (map_pre_\<Sigma>\<Sigma>2 id (ctor_fold_\<Sigma>\<Sigma>2 s))"
unfolding comp_def \<Sigma>\<Sigma>2.ctor_fold ..

lemma \<Sigma>\<Sigma>2_map_ctor_\<Sigma>\<Sigma>2:
"\<Sigma>\<Sigma>2_map f o ctor_\<Sigma>\<Sigma>2 = ctor_\<Sigma>\<Sigma>2 o map_sum (\<Sigma>2_map (\<Sigma>\<Sigma>2_map f)) f"
unfolding comp_def
unfolding fun_eq_iff
unfolding \<Sigma>\<Sigma>2.ctor_map
unfolding map_pre_\<Sigma>\<Sigma>2_def  (* careful here and elsewhere: data newdatatype unfolds more *)
unfolding id_apply BNF_Comp.id_bnf_comp_def id_def[symmetric] o_id id_o by simp

lemma dtor_\<Sigma>\<Sigma>2_\<Sigma>\<Sigma>2_map:
"dtor_\<Sigma>\<Sigma>2 o \<Sigma>\<Sigma>2_map f = map_sum (\<Sigma>2_map (\<Sigma>\<Sigma>2_map f)) f o dtor_\<Sigma>\<Sigma>2"
using \<Sigma>\<Sigma>2_map_ctor_\<Sigma>\<Sigma>2[of f] \<Sigma>\<Sigma>2.dtor_ctor \<Sigma>\<Sigma>2.ctor_dtor unfolding comp_def fun_eq_iff by metis

lemma dtor_\<Sigma>\<Sigma>2_ctor_\<Sigma>\<Sigma>2: "dtor_\<Sigma>\<Sigma>2 \<circ> ctor_\<Sigma>\<Sigma>2 = id"
unfolding comp_def \<Sigma>\<Sigma>2.dtor_ctor id_def ..

lemma ctor_\<Sigma>\<Sigma>2_dtor_\<Sigma>\<Sigma>2: "ctor_\<Sigma>\<Sigma>2 \<circ> dtor_\<Sigma>\<Sigma>2 = id"
unfolding comp_def \<Sigma>\<Sigma>2.ctor_dtor id_def ..

lemma \<Sigma>\<Sigma>2_rel_inf: "\<Sigma>\<Sigma>2_rel (R \<sqinter> \<Sigma>1) \<le> \<Sigma>\<Sigma>2_rel R \<sqinter> \<Sigma>\<Sigma>2_rel \<Sigma>1"
  apply (rule inf_greatest)
  apply (rule \<Sigma>\<Sigma>2.rel_mono[OF inf_sup_ord(1)])
  apply (rule \<Sigma>\<Sigma>2.rel_mono[OF inf_sup_ord(2)])
  done

lemma \<Sigma>\<Sigma>2_rel_Grp_\<Sigma>\<Sigma>2_map: "\<Sigma>\<Sigma>2_rel (BNF_Def.Grp UNIV f) x y \<longleftrightarrow> \<Sigma>\<Sigma>2_map f x = y"
  unfolding \<Sigma>\<Sigma>2.rel_Grp by (auto simp: Grp_def)

lemma \<Sigma>\<Sigma>2_rel_\<Sigma>\<Sigma>2_map_\<Sigma>\<Sigma>2_map: "\<Sigma>\<Sigma>2_rel R (\<Sigma>\<Sigma>2_map f x) (\<Sigma>\<Sigma>2_map g y) =
  \<Sigma>\<Sigma>2_rel (BNF_Def.vimage2p f g R) x y"
  unfolding \<Sigma>\<Sigma>2.rel_Grp vimage2p_Grp apply (auto simp: \<Sigma>\<Sigma>2.rel_compp \<Sigma>\<Sigma>2.rel_conversep relcompp.simps)
  apply (intro exI conjI)
  apply (rule iffD2[OF \<Sigma>\<Sigma>2_rel_Grp_\<Sigma>\<Sigma>2_map refl])
  apply assumption
  apply (rule iffD2[OF \<Sigma>\<Sigma>2_rel_Grp_\<Sigma>\<Sigma>2_map refl])
  unfolding \<Sigma>\<Sigma>2_rel_Grp_\<Sigma>\<Sigma>2_map
  apply simp
  done


subsection{* @{term \<Sigma>2} extension theorems *}

theorem ext2_commute:
"ext2 s i o \<oo>\<pp>2 = s o \<Sigma>2_map (ext2 s i)"
unfolding ext2_alt \<oo>\<pp>2_def_pointfree o_assoc ctor_fold_\<Sigma>\<Sigma>2_pointfree map_pre_\<Sigma>\<Sigma>2_def
  case_sum_o_map_sum case_sum_o_inj(1) BNF_Comp.id_bnf_comp_def id_def[symmetric] o_id ..

theorem ext2_comp_leaf2:
"ext2 s i o leaf2 = i"
unfolding ext2_alt leaf2_def_pointfree o_assoc ctor_fold_\<Sigma>\<Sigma>2_pointfree map_pre_\<Sigma>\<Sigma>2_def
  case_sum_o_map_sum case_sum_o_inj(2) id_apply BNF_Comp.id_bnf_comp_def id_def[symmetric] o_id ..

theorem ext2_unique:
assumes leaf2: "f o leaf2 = i" and com: "f o \<oo>\<pp>2 = s o \<Sigma>2_map f"
shows "f = ext2 s i"
unfolding ext2_alt
apply (rule \<Sigma>\<Sigma>2.ctor_fold_unique)
apply (rule sum_comp_cases)
unfolding map_pre_\<Sigma>\<Sigma>2_def case_sum_o_map_sum id_apply o_id case_sum_o_inj
  leaf2[unfolded leaf2_def_pointfree o_assoc] com[unfolded \<oo>\<pp>2_def_pointfree o_assoc]
  BNF_Comp.id_bnf_comp_def id_def[symmetric] id_o
by (rule refl)+

subsection{* Customizing @{term \<Sigma>\<Sigma>2} *}

subsection{* Injectiveness, naturality, adjunction *}

theorem leaf2_natural: "\<Sigma>\<Sigma>2_map f o leaf2 = leaf2 o f"
  using leaf2_transfer[of "BNF_Def.Grp UNIV f"]
  unfolding \<Sigma>\<Sigma>2.rel_Grp
  unfolding Grp_def rel_fun_def by auto

lemma \<oo>\<pp>2_natural: "\<oo>\<pp>2 o \<Sigma>2_map (\<Sigma>\<Sigma>2_map f) = \<Sigma>\<Sigma>2_map f o \<oo>\<pp>2"
  using \<oo>\<pp>2_transfer[of "BNF_Def.Grp UNIV f"]
  unfolding \<Sigma>2.rel_Grp \<Sigma>\<Sigma>2.rel_Grp \<Sigma>2_map_def
  unfolding Grp_def rel_fun_def by auto

lemma \<Sigma>\<Sigma>2_map_def2: "\<Sigma>\<Sigma>2_map i = ext2 \<oo>\<pp>2 (leaf2 o i)"
by (rule ext2_unique[OF leaf2_natural \<oo>\<pp>2_natural[symmetric]])

lemma ext2_\<oo>\<pp>2_leaf2: "ext2 \<oo>\<pp>2 leaf2 = id"
apply (rule ext2_unique[symmetric]) unfolding \<Sigma>2.map_id0 o_id id_o by (rule refl)+

lemma ext2_\<Sigma>\<Sigma>2_map:
"ext2 s (j o f) = ext2 s j o \<Sigma>\<Sigma>2_map f"
proof (rule ext2_unique[symmetric])
  show "ext2 s j \<circ> \<Sigma>\<Sigma>2_map f \<circ> leaf2 = j \<circ> f"
  unfolding o_assoc[symmetric] leaf2_natural
  unfolding o_assoc ext2_comp_leaf2 ..
next
  show "ext2 s j \<circ> \<Sigma>\<Sigma>2_map f \<circ> \<oo>\<pp>2 = s \<circ> \<Sigma>2_map (ext2 s j \<circ> \<Sigma>\<Sigma>2_map f)"
  unfolding o_assoc[symmetric] \<oo>\<pp>2_natural[symmetric]
  unfolding o_assoc ext2_commute
  unfolding o_assoc[symmetric] \<Sigma>2.map_comp0 ..
qed

lemma ext2_\<Sigma>2_map:
assumes "t o \<Sigma>2_map f = f o s"
shows "ext2 t (f o i) = f o ext2 s i"
proof (rule ext2_unique[symmetric])
  show "f \<circ> ext2 s i \<circ> leaf2 = f o i"
  unfolding o_assoc[symmetric] ext2_comp_leaf2 ..
next
  show "f \<circ> ext2 s i \<circ> \<oo>\<pp>2 = t \<circ> \<Sigma>2_map (f \<circ> ext2 s i)"
  unfolding \<Sigma>2.map_comp0 o_assoc assms
  unfolding o_assoc[symmetric] ext2_commute[symmetric] ..
qed


subsection{* Monadic laws *}

lemma flat2_commute: "\<oo>\<pp>2 \<circ> \<Sigma>2_map flat2 = flat2 \<circ> \<oo>\<pp>2"
unfolding flat2_def ext2_commute ..

(* The 2 identity laws*)
theorem flat2_leaf2: "flat2 o leaf2 = id"
unfolding flat2_def ext2_comp_leaf2 ..

theorem leaf2_flat2: "flat2 o \<Sigma>\<Sigma>2_map leaf2 = id"
unfolding flat2_def ext2_\<Sigma>\<Sigma>2_map[symmetric] id_o ext2_\<oo>\<pp>2_leaf2 ..

theorem flat2_natural: "flat2 o \<Sigma>\<Sigma>2_map (\<Sigma>\<Sigma>2_map i) = \<Sigma>\<Sigma>2_map i o flat2"
  using flat2_transfer[of "BNF_Def.Grp UNIV i"]
  unfolding prod.rel_Grp \<Sigma>\<Sigma>2.rel_Grp
  unfolding Grp_def rel_fun_def by auto

(* Associativity *)
theorem flat2_assoc: "flat2 o \<Sigma>\<Sigma>2_map flat2 = flat2 o flat2"
unfolding flat2_def unfolding ext2_\<Sigma>\<Sigma>2_map[symmetric] id_o
proof(rule ext2_unique[symmetric], unfold flat2_def[symmetric])
  show "flat2 \<circ> flat2 \<circ> leaf2 = flat2"
  unfolding o_assoc[symmetric] flat2_leaf2 o_id ..
next
  show "flat2 \<circ> flat2 \<circ> \<oo>\<pp>2 = \<oo>\<pp>2 \<circ> \<Sigma>2_map (flat2 \<circ> flat2)"
  unfolding flat2_def unfolding o_assoc[symmetric] ext2_commute
  unfolding flat2_def[symmetric]
  unfolding \<Sigma>2.map_comp0 o_assoc unfolding flat2_commute ..
qed

definition K2_as_\<Sigma>\<Sigma>2 :: "'a K2 \<Rightarrow> 'a \<Sigma>\<Sigma>2" where
"K2_as_\<Sigma>\<Sigma>2 \<equiv> \<oo>\<pp>2 o \<Sigma>2_map leaf2 o Abs_\<Sigma>2 o Inr"

lemma K2_as_\<Sigma>\<Sigma>2_transfer[transfer_rule]:
  "(K2_rel R ===> \<Sigma>\<Sigma>2_rel R) K2_as_\<Sigma>\<Sigma>2 K2_as_\<Sigma>\<Sigma>2"
  unfolding K2_as_\<Sigma>\<Sigma>2_def by transfer_prover

lemma K2_as_\<Sigma>\<Sigma>2_natural:
"K2_as_\<Sigma>\<Sigma>2 o K2_map f = \<Sigma>\<Sigma>2_map f o K2_as_\<Sigma>\<Sigma>2"
  using K2_as_\<Sigma>\<Sigma>2_transfer[of "BNF_Def.Grp UNIV f"]
  unfolding K2.rel_Grp \<Sigma>\<Sigma>2.rel_Grp
  unfolding Grp_def rel_fun_def by auto

end