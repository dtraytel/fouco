header{* Free algebras for an BNF *}

(* Free algebra constructed for a sum of two BNF's S and K: *)
(* Notations: Identical to FreeAlg, just that constants and types are suffixed by "step" instead of "base": *)

theory Stream_FreeAlg3
imports Stream_Input3
begin

declare K3.map_transfer[transfer_rule]

(* The new-operation functor: *)

composition_bnf (open) raw_\<Sigma>3: "'a \<Sigma>2 + 'a K3"
typedef 'a \<Sigma>3 = "UNIV :: ('a \<Sigma>2 + 'a K3) set" by (rule UNIV_witness)

setup_lifting type_definition_\<Sigma>3

lift_definition \<Sigma>3_map :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Sigma>3 \<Rightarrow> 'b \<Sigma>3" is "\<lambda>f. map_sum (\<Sigma>2_map f) (K3_map f)" .
lift_definition \<Sigma>3_set :: "'a \<Sigma>3 \<Rightarrow> 'a set"
  is "\<lambda>x. UNION (Basic_BNFs.setl x) \<Sigma>2_set \<union> UNION (Basic_BNFs.setr x) K3_set" .
lift_definition \<Sigma>3_rel :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a \<Sigma>3 \<Rightarrow> 'b \<Sigma>3 \<Rightarrow> bool"
  is "\<lambda>R. rel_sum (\<Sigma>2_rel R) (K3_rel R)" .
typedef \<Sigma>3_bd_type = "UNIV :: ((\<Sigma>2_bd_type + bd_type_K3) \<times> nat) set" by (rule UNIV_witness)
definition "\<Sigma>3_bd = dir_image ((\<Sigma>2_bd +c bd_K3) *c natLeq) Abs_\<Sigma>3_bd_type"

bnf "'a \<Sigma>3"
  map: \<Sigma>3_map
  sets: \<Sigma>3_set
  bd: \<Sigma>3_bd 
  rel: \<Sigma>3_rel
unfolding \<Sigma>3_bd_def
apply -
apply transfer apply (rule raw_\<Sigma>3.map_id0)
apply transfer apply (rule raw_\<Sigma>3.map_comp0)
apply transfer apply (erule raw_\<Sigma>3.map_cong0)
apply transfer apply (rule raw_\<Sigma>3.set_map0)
apply (rule card_order_dir_image[OF bijI raw_\<Sigma>3.bd_card_order])
apply (metis inj_on_def Abs_\<Sigma>3_bd_type_inverse[OF UNIV_I])
apply (metis surj_def Abs_\<Sigma>3_bd_type_cases)
apply (rule conjunct1[OF Cinfinite_cong[OF dir_image[OF _ raw_\<Sigma>3.bd_Card_order] raw_\<Sigma>3.bd_Cinfinite]])
apply (metis Abs_\<Sigma>3_bd_type_inverse[OF UNIV_I])
apply (unfold \<Sigma>3_set_def map_fun_def id_o) [1] apply (subst o_apply)
apply (rule ordLeq_ordIso_trans[OF raw_\<Sigma>3.set_bd dir_image[OF _ raw_\<Sigma>3.bd_Card_order]])
apply (metis Abs_\<Sigma>3_bd_type_inverse[OF UNIV_I])
apply (rule predicate2I) apply transfer apply (subst raw_\<Sigma>3.rel_compp) apply assumption
apply transfer' apply (rule raw_\<Sigma>3.rel_compp_Grp)
done

declare \<Sigma>3.map_transfer[transfer_rule]

lemma Rep_\<Sigma>3_transfer[transfer_rule]: "(\<Sigma>3_rel R ===> rel_sum (\<Sigma>2_rel R) (K3_rel R)) Rep_\<Sigma>3 Rep_\<Sigma>3"
  unfolding rel_fun_def by transfer blast

lemma Abs_\<Sigma>3_transfer[transfer_rule]: "(rel_sum (\<Sigma>2_rel R) (K3_rel R) ===> \<Sigma>3_rel R) Abs_\<Sigma>3 Abs_\<Sigma>3"
  unfolding rel_fun_def by transfer blast

theorem Rep_\<Sigma>3_natural: "map_sum (\<Sigma>2_map f) (K3_map f) o Rep_\<Sigma>3 = Rep_\<Sigma>3 o \<Sigma>3_map f"
  using Rep_\<Sigma>3_transfer[of "BNF_Def.Grp UNIV f"]
  unfolding \<Sigma>3.rel_Grp raw_\<Sigma>3.rel_Grp
  unfolding Grp_def rel_fun_def by auto

theorem Abs_\<Sigma>3_natural: "\<Sigma>3_map f o Abs_\<Sigma>3 = Abs_\<Sigma>3 o map_sum (\<Sigma>2_map f) (K3_map f)"
  using Abs_\<Sigma>3_transfer[of "BNF_Def.Grp UNIV f"]
  unfolding \<Sigma>3.rel_Grp raw_\<Sigma>3.rel_Grp
  unfolding Grp_def rel_fun_def by auto

lemma Rep_\<Sigma>3_o_Abs_\<Sigma>3: "Rep_\<Sigma>3 o Abs_\<Sigma>3 = id"
  apply (rule ext)
  apply (rule box_equals[OF _ o_apply[symmetric] id_apply[symmetric]])
  apply (rule Abs_\<Sigma>3_inverse[OF UNIV_I])
  done

lemma \<Sigma>3_rel_\<Sigma>3_map_\<Sigma>3_map:
  "\<Sigma>3_rel R (\<Sigma>3_map f x) (\<Sigma>3_map g y) = \<Sigma>3_rel (BNF_Def.vimage2p f g R) x y"
  unfolding \<Sigma>3.rel_Grp vimage2p_Grp \<Sigma>3.rel_compp \<Sigma>3.rel_conversep
  unfolding relcompp.simps Grp_def by simp

subsection{* Definitions and basic setup *}

(* 'x \<Sigma>\<Sigma>3 consist of \<Sigma>3-terms with variables in 'x: *)
datatype_new (\<Sigma>\<Sigma>3_set: 'x) \<Sigma>\<Sigma>3 =
  \<oo>\<pp>3 "'x \<Sigma>\<Sigma>3 \<Sigma>3" | leaf3 "'x"
  for map: \<Sigma>\<Sigma>3_map rel: \<Sigma>\<Sigma>3_rel
declare \<Sigma>\<Sigma>3.ctor_fold_transfer
  [unfolded rel_pre_\<Sigma>\<Sigma>3_def id_apply BNF_Comp.id_bnf_comp_def vimage2p_def, transfer_rule]

lemma \<oo>\<pp>3_transfer[transfer_rule]:
  "(\<Sigma>3_rel (\<Sigma>\<Sigma>3_rel R) ===> \<Sigma>\<Sigma>3_rel R) \<oo>\<pp>3 \<oo>\<pp>3"
  by (rule rel_funI) (erule iffD2[OF \<Sigma>\<Sigma>3.rel_inject(1)])

lemma leaf3_transfer[transfer_rule]: "(R ===> \<Sigma>\<Sigma>3_rel R) leaf3 leaf3"
  by (rule rel_funI) (erule iffD2[OF \<Sigma>\<Sigma>3.rel_inject(2)])

(* The free extension, for an algebra s, of an inteprleaftion i of the
variables into the algebra carrier:  *)
abbreviation "ext3 s \<equiv> rec_\<Sigma>\<Sigma>3 (s o \<Sigma>3_map snd)"
lemmas ext3_\<oo>\<pp>3 = \<Sigma>\<Sigma>3.rec(1)[of "s o \<Sigma>3_map snd" for s,
  unfolded o_apply \<Sigma>3.map_comp snd_convol[unfolded convol_def]]
lemmas ext3_leaf3 = \<Sigma>\<Sigma>3.rec(2)[of "s o \<Sigma>3_map snd" for s,
  unfolded o_apply \<Sigma>3.map_comp snd_convol[unfolded convol_def]]
lemmas leaf3_inj = \<Sigma>\<Sigma>3.inject(2)
lemmas \<oo>\<pp>3_inj = \<Sigma>\<Sigma>3.inject(1)

lemma ext3_alt: "ext3 s f = ctor_fold_\<Sigma>\<Sigma>3 (case_sum s f)"
  apply (rule \<Sigma>\<Sigma>3.ctor_fold_unique)
  apply (rule ext)
  apply (rename_tac x)
  apply (case_tac x)
  apply (auto simp only: rec_\<Sigma>\<Sigma>3_def \<Sigma>\<Sigma>3.ctor_rec fun_eq_iff o_apply BNF_Comp.id_bnf_comp_def
    id_def[symmetric] o_id map_pre_\<Sigma>\<Sigma>3_def id_apply map_sum.simps sum.inject sum.distinct
    \<Sigma>3.map_comp snd_convol split: sum.splits)
  done

(* The term algebra: *)

lemma \<oo>\<pp>3_def_pointfree: "\<oo>\<pp>3 \<equiv> ctor_\<Sigma>\<Sigma>3 o Inl"
unfolding \<oo>\<pp>3_def comp_def BNF_Comp.id_bnf_comp_def .

(* Monadic structure *)
lemma leaf3_def_pointfree: "leaf3 \<equiv> ctor_\<Sigma>\<Sigma>3 o Inr"
unfolding leaf3_def comp_def BNF_Comp.id_bnf_comp_def .

definition flat3 :: "('x \<Sigma>\<Sigma>3) \<Sigma>\<Sigma>3 \<Rightarrow> 'x \<Sigma>\<Sigma>3" where
  flat3_def: "flat3 \<equiv> ext3 \<oo>\<pp>3 id"

lemma flat3_transfer[transfer_rule]: "(\<Sigma>\<Sigma>3_rel (\<Sigma>\<Sigma>3_rel R) ===> \<Sigma>\<Sigma>3_rel R) flat3 flat3"
  unfolding flat3_def ext3_alt by transfer_prover

(* facts about \<Sigma>\<Sigma>3: *)
lemma ctor_fold_\<Sigma>\<Sigma>3_pointfree:
"ctor_fold_\<Sigma>\<Sigma>3 s o ctor_\<Sigma>\<Sigma>3 = s o (map_pre_\<Sigma>\<Sigma>3 id (ctor_fold_\<Sigma>\<Sigma>3 s))"
unfolding comp_def \<Sigma>\<Sigma>3.ctor_fold ..

lemma \<Sigma>\<Sigma>3_map_ctor_\<Sigma>\<Sigma>3:
"\<Sigma>\<Sigma>3_map f o ctor_\<Sigma>\<Sigma>3 = ctor_\<Sigma>\<Sigma>3 o map_sum (\<Sigma>3_map (\<Sigma>\<Sigma>3_map f)) f"
unfolding comp_def
unfolding fun_eq_iff
unfolding \<Sigma>\<Sigma>3.ctor_map
unfolding map_pre_\<Sigma>\<Sigma>3_def  (* careful here and elsewhere: data newdatatype unfolds more *)
unfolding id_apply BNF_Comp.id_bnf_comp_def id_def[symmetric] o_id id_o by simp

lemma dtor_\<Sigma>\<Sigma>3_\<Sigma>\<Sigma>3_map:
"dtor_\<Sigma>\<Sigma>3 o \<Sigma>\<Sigma>3_map f = map_sum (\<Sigma>3_map (\<Sigma>\<Sigma>3_map f)) f o dtor_\<Sigma>\<Sigma>3"
using \<Sigma>\<Sigma>3_map_ctor_\<Sigma>\<Sigma>3[of f] \<Sigma>\<Sigma>3.dtor_ctor \<Sigma>\<Sigma>3.ctor_dtor unfolding comp_def fun_eq_iff by metis

lemma dtor_\<Sigma>\<Sigma>3_ctor_\<Sigma>\<Sigma>3: "dtor_\<Sigma>\<Sigma>3 \<circ> ctor_\<Sigma>\<Sigma>3 = id"
unfolding comp_def \<Sigma>\<Sigma>3.dtor_ctor id_def ..

lemma ctor_\<Sigma>\<Sigma>3_dtor_\<Sigma>\<Sigma>3: "ctor_\<Sigma>\<Sigma>3 \<circ> dtor_\<Sigma>\<Sigma>3 = id"
unfolding comp_def \<Sigma>\<Sigma>3.ctor_dtor id_def ..

lemma \<Sigma>\<Sigma>3_rel_inf: "\<Sigma>\<Sigma>3_rel (R \<sqinter> \<Sigma>2) \<le> \<Sigma>\<Sigma>3_rel R \<sqinter> \<Sigma>\<Sigma>3_rel \<Sigma>2"
  apply (rule inf_greatest)
  apply (rule \<Sigma>\<Sigma>3.rel_mono[OF inf_sup_ord(1)])
  apply (rule \<Sigma>\<Sigma>3.rel_mono[OF inf_sup_ord(2)])
  done

lemma \<Sigma>\<Sigma>3_rel_Grp_\<Sigma>\<Sigma>3_map: "\<Sigma>\<Sigma>3_rel (BNF_Def.Grp UNIV f) x y \<longleftrightarrow> \<Sigma>\<Sigma>3_map f x = y"
  unfolding \<Sigma>\<Sigma>3.rel_Grp by (auto simp: Grp_def)

lemma \<Sigma>\<Sigma>3_rel_\<Sigma>\<Sigma>3_map_\<Sigma>\<Sigma>3_map: "\<Sigma>\<Sigma>3_rel R (\<Sigma>\<Sigma>3_map f x) (\<Sigma>\<Sigma>3_map g y) =
  \<Sigma>\<Sigma>3_rel (BNF_Def.vimage2p f g R) x y"
  unfolding \<Sigma>\<Sigma>3.rel_Grp vimage2p_Grp apply (auto simp: \<Sigma>\<Sigma>3.rel_compp \<Sigma>\<Sigma>3.rel_conversep relcompp.simps)
  apply (intro exI conjI)
  apply (rule iffD2[OF \<Sigma>\<Sigma>3_rel_Grp_\<Sigma>\<Sigma>3_map refl])
  apply assumption
  apply (rule iffD2[OF \<Sigma>\<Sigma>3_rel_Grp_\<Sigma>\<Sigma>3_map refl])
  unfolding \<Sigma>\<Sigma>3_rel_Grp_\<Sigma>\<Sigma>3_map
  apply simp
  done


subsection{* @{term \<Sigma>3} extension theorems *}

theorem ext3_commute:
"ext3 s i o \<oo>\<pp>3 = s o \<Sigma>3_map (ext3 s i)"
unfolding ext3_alt \<oo>\<pp>3_def_pointfree o_assoc ctor_fold_\<Sigma>\<Sigma>3_pointfree map_pre_\<Sigma>\<Sigma>3_def
  case_sum_o_map_sum case_sum_o_inj(1) BNF_Comp.id_bnf_comp_def id_def[symmetric] o_id ..

theorem ext3_comp_leaf3:
"ext3 s i o leaf3 = i"
unfolding ext3_alt leaf3_def_pointfree o_assoc ctor_fold_\<Sigma>\<Sigma>3_pointfree map_pre_\<Sigma>\<Sigma>3_def
  case_sum_o_map_sum case_sum_o_inj(2) id_apply BNF_Comp.id_bnf_comp_def id_def[symmetric] o_id ..

theorem ext3_unique:
assumes leaf3: "f o leaf3 = i" and com: "f o \<oo>\<pp>3 = s o \<Sigma>3_map f"
shows "f = ext3 s i"
unfolding ext3_alt
apply (rule \<Sigma>\<Sigma>3.ctor_fold_unique)
apply (rule sum_comp_cases)
unfolding map_pre_\<Sigma>\<Sigma>3_def case_sum_o_map_sum id_apply o_id case_sum_o_inj
  leaf3[unfolded leaf3_def_pointfree o_assoc] com[unfolded \<oo>\<pp>3_def_pointfree o_assoc]
  BNF_Comp.id_bnf_comp_def id_def[symmetric] id_o
by (rule refl)+

subsection{* Customizing @{term \<Sigma>\<Sigma>3} *}

subsection{* Injectiveness, naturality, adjunction *}

theorem leaf3_natural: "\<Sigma>\<Sigma>3_map f o leaf3 = leaf3 o f"
  using leaf3_transfer[of "BNF_Def.Grp UNIV f"]
  unfolding \<Sigma>\<Sigma>3.rel_Grp
  unfolding Grp_def rel_fun_def by auto

lemma \<oo>\<pp>3_natural: "\<oo>\<pp>3 o \<Sigma>3_map (\<Sigma>\<Sigma>3_map f) = \<Sigma>\<Sigma>3_map f o \<oo>\<pp>3"
  using \<oo>\<pp>3_transfer[of "BNF_Def.Grp UNIV f"]
  unfolding \<Sigma>3.rel_Grp \<Sigma>\<Sigma>3.rel_Grp \<Sigma>3_map_def
  unfolding Grp_def rel_fun_def by auto

lemma \<Sigma>\<Sigma>3_map_def2: "\<Sigma>\<Sigma>3_map i = ext3 \<oo>\<pp>3 (leaf3 o i)"
by (rule ext3_unique[OF leaf3_natural \<oo>\<pp>3_natural[symmetric]])

lemma ext3_\<oo>\<pp>3_leaf3: "ext3 \<oo>\<pp>3 leaf3 = id"
apply (rule ext3_unique[symmetric]) unfolding \<Sigma>3.map_id0 o_id id_o by (rule refl)+

lemma ext3_\<Sigma>\<Sigma>3_map:
"ext3 s (j o f) = ext3 s j o \<Sigma>\<Sigma>3_map f"
proof (rule ext3_unique[symmetric])
  show "ext3 s j \<circ> \<Sigma>\<Sigma>3_map f \<circ> leaf3 = j \<circ> f"
  unfolding o_assoc[symmetric] leaf3_natural
  unfolding o_assoc ext3_comp_leaf3 ..
next
  show "ext3 s j \<circ> \<Sigma>\<Sigma>3_map f \<circ> \<oo>\<pp>3 = s \<circ> \<Sigma>3_map (ext3 s j \<circ> \<Sigma>\<Sigma>3_map f)"
  unfolding o_assoc[symmetric] \<oo>\<pp>3_natural[symmetric]
  unfolding o_assoc ext3_commute
  unfolding o_assoc[symmetric] \<Sigma>3.map_comp0 ..
qed

lemma ext3_\<Sigma>3_map:
assumes "t o \<Sigma>3_map f = f o s"
shows "ext3 t (f o i) = f o ext3 s i"
proof (rule ext3_unique[symmetric])
  show "f \<circ> ext3 s i \<circ> leaf3 = f o i"
  unfolding o_assoc[symmetric] ext3_comp_leaf3 ..
next
  show "f \<circ> ext3 s i \<circ> \<oo>\<pp>3 = t \<circ> \<Sigma>3_map (f \<circ> ext3 s i)"
  unfolding \<Sigma>3.map_comp0 o_assoc assms
  unfolding o_assoc[symmetric] ext3_commute[symmetric] ..
qed


subsection{* Monadic laws *}

lemma flat3_commute: "\<oo>\<pp>3 \<circ> \<Sigma>3_map flat3 = flat3 \<circ> \<oo>\<pp>3"
unfolding flat3_def ext3_commute ..

(* The 2 identity laws*)
theorem flat3_leaf3: "flat3 o leaf3 = id"
unfolding flat3_def ext3_comp_leaf3 ..

theorem leaf3_flat3: "flat3 o \<Sigma>\<Sigma>3_map leaf3 = id"
unfolding flat3_def ext3_\<Sigma>\<Sigma>3_map[symmetric] id_o ext3_\<oo>\<pp>3_leaf3 ..

theorem flat3_natural: "flat3 o \<Sigma>\<Sigma>3_map (\<Sigma>\<Sigma>3_map i) = \<Sigma>\<Sigma>3_map i o flat3"
  using flat3_transfer[of "BNF_Def.Grp UNIV i"]
  unfolding prod.rel_Grp \<Sigma>\<Sigma>3.rel_Grp
  unfolding Grp_def rel_fun_def by auto

(* Associativity *)
theorem flat3_assoc: "flat3 o \<Sigma>\<Sigma>3_map flat3 = flat3 o flat3"
unfolding flat3_def unfolding ext3_\<Sigma>\<Sigma>3_map[symmetric] id_o
proof(rule ext3_unique[symmetric], unfold flat3_def[symmetric])
  show "flat3 \<circ> flat3 \<circ> leaf3 = flat3"
  unfolding o_assoc[symmetric] flat3_leaf3 o_id ..
next
  show "flat3 \<circ> flat3 \<circ> \<oo>\<pp>3 = \<oo>\<pp>3 \<circ> \<Sigma>3_map (flat3 \<circ> flat3)"
  unfolding flat3_def unfolding o_assoc[symmetric] ext3_commute
  unfolding flat3_def[symmetric]
  unfolding \<Sigma>3.map_comp0 o_assoc unfolding flat3_commute ..
qed

definition K3_as_\<Sigma>\<Sigma>3 :: "'a K3 \<Rightarrow> 'a \<Sigma>\<Sigma>3" where
"K3_as_\<Sigma>\<Sigma>3 \<equiv> \<oo>\<pp>3 o \<Sigma>3_map leaf3 o Abs_\<Sigma>3 o Inr"

lemma K3_as_\<Sigma>\<Sigma>3_transfer[transfer_rule]:
  "(K3_rel R ===> \<Sigma>\<Sigma>3_rel R) K3_as_\<Sigma>\<Sigma>3 K3_as_\<Sigma>\<Sigma>3"
  unfolding K3_as_\<Sigma>\<Sigma>3_def by transfer_prover

lemma K3_as_\<Sigma>\<Sigma>3_natural:
"K3_as_\<Sigma>\<Sigma>3 o K3_map f = \<Sigma>\<Sigma>3_map f o K3_as_\<Sigma>\<Sigma>3"
  using K3_as_\<Sigma>\<Sigma>3_transfer[of "BNF_Def.Grp UNIV f"]
  unfolding K3.rel_Grp \<Sigma>\<Sigma>3.rel_Grp
  unfolding Grp_def rel_fun_def by auto

end