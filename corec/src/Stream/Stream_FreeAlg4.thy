header{* Free algebras for an BNF *}

(* Free algebra constructed for a sum of two BNF's S and K: *)
(* Notations: Identical to FreeAlg, just that constants and types are suffixed by "step" instead of "base": *)

theory Stream_FreeAlg4
imports Stream_Input4
begin

declare K4.map_transfer[transfer_rule]

(* The new-operation functor: *)

composition_bnf (open) raw_\<Sigma>4: "'a \<Sigma>3 + 'a K4"
typedef 'a \<Sigma>4 = "UNIV :: ('a \<Sigma>3 + 'a K4) set" by (rule UNIV_witness)

setup_lifting type_definition_\<Sigma>4

lift_definition \<Sigma>4_map :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Sigma>4 \<Rightarrow> 'b \<Sigma>4" is "\<lambda>f. map_sum (\<Sigma>3_map f) (K4_map f)" .
lift_definition \<Sigma>4_set :: "'a \<Sigma>4 \<Rightarrow> 'a set"
  is "\<lambda>x. UNION (Basic_BNFs.setl x) \<Sigma>3_set \<union> UNION (Basic_BNFs.setr x) K4_set" .
lift_definition \<Sigma>4_rel :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a \<Sigma>4 \<Rightarrow> 'b \<Sigma>4 \<Rightarrow> bool"
  is "\<lambda>R. rel_sum (\<Sigma>3_rel R) (K4_rel R)" .
typedef \<Sigma>4_bd_type = "UNIV :: ((\<Sigma>3_bd_type + bd_type_K4) \<times> nat) set" by (rule UNIV_witness)
definition "\<Sigma>4_bd = dir_image ((\<Sigma>3_bd +c bd_K4) *c natLeq) Abs_\<Sigma>4_bd_type"

bnf "'a \<Sigma>4"
  map: \<Sigma>4_map
  sets: \<Sigma>4_set
  bd: \<Sigma>4_bd 
  rel: \<Sigma>4_rel
unfolding \<Sigma>4_bd_def
apply -
apply transfer apply (rule raw_\<Sigma>4.map_id0)
apply transfer apply (rule raw_\<Sigma>4.map_comp0)
apply transfer apply (erule raw_\<Sigma>4.map_cong0)
apply transfer apply (rule raw_\<Sigma>4.set_map0)
apply (rule card_order_dir_image[OF bijI raw_\<Sigma>4.bd_card_order])
apply (metis inj_on_def Abs_\<Sigma>4_bd_type_inverse[OF UNIV_I])
apply (metis surj_def Abs_\<Sigma>4_bd_type_cases)
apply (rule conjunct1[OF Cinfinite_cong[OF dir_image[OF _ raw_\<Sigma>4.bd_Card_order] raw_\<Sigma>4.bd_Cinfinite]])
apply (metis Abs_\<Sigma>4_bd_type_inverse[OF UNIV_I])
apply (unfold \<Sigma>4_set_def map_fun_def id_o) [1] apply (subst o_apply)
apply (rule ordLeq_ordIso_trans[OF raw_\<Sigma>4.set_bd dir_image[OF _ raw_\<Sigma>4.bd_Card_order]])
apply (metis Abs_\<Sigma>4_bd_type_inverse[OF UNIV_I])
apply (rule predicate2I) apply transfer apply (subst raw_\<Sigma>4.rel_compp) apply assumption
apply transfer' apply (rule raw_\<Sigma>4.rel_compp_Grp)
done

declare \<Sigma>4.map_transfer[transfer_rule]

lemma Rep_\<Sigma>4_transfer[transfer_rule]: "(\<Sigma>4_rel R ===> rel_sum (\<Sigma>3_rel R) (K4_rel R)) Rep_\<Sigma>4 Rep_\<Sigma>4"
  unfolding rel_fun_def by transfer blast

lemma Abs_\<Sigma>4_transfer[transfer_rule]: "(rel_sum (\<Sigma>3_rel R) (K4_rel R) ===> \<Sigma>4_rel R) Abs_\<Sigma>4 Abs_\<Sigma>4"
  unfolding rel_fun_def by transfer blast

theorem Rep_\<Sigma>4_natural: "map_sum (\<Sigma>3_map f) (K4_map f) o Rep_\<Sigma>4 = Rep_\<Sigma>4 o \<Sigma>4_map f"
  using Rep_\<Sigma>4_transfer[of "BNF_Def.Grp UNIV f"]
  unfolding \<Sigma>4.rel_Grp raw_\<Sigma>4.rel_Grp
  unfolding Grp_def rel_fun_def by auto

theorem Abs_\<Sigma>4_natural: "\<Sigma>4_map f o Abs_\<Sigma>4 = Abs_\<Sigma>4 o map_sum (\<Sigma>3_map f) (K4_map f)"
  using Abs_\<Sigma>4_transfer[of "BNF_Def.Grp UNIV f"]
  unfolding \<Sigma>4.rel_Grp raw_\<Sigma>4.rel_Grp
  unfolding Grp_def rel_fun_def by auto

lemma Rep_\<Sigma>4_o_Abs_\<Sigma>4: "Rep_\<Sigma>4 o Abs_\<Sigma>4 = id"
  apply (rule ext)
  apply (rule box_equals[OF _ o_apply[symmetric] id_apply[symmetric]])
  apply (rule Abs_\<Sigma>4_inverse[OF UNIV_I])
  done

lemma \<Sigma>4_rel_\<Sigma>4_map_\<Sigma>4_map:
  "\<Sigma>4_rel R (\<Sigma>4_map f x) (\<Sigma>4_map g y) = \<Sigma>4_rel (BNF_Def.vimage2p f g R) x y"
  unfolding \<Sigma>4.rel_Grp vimage2p_Grp \<Sigma>4.rel_compp \<Sigma>4.rel_conversep
  unfolding relcompp.simps Grp_def by simp

subsection{* Definitions and basic setup *}

(* 'x \<Sigma>\<Sigma>4 consist of \<Sigma>4-terms with variables in 'x: *)
datatype_new (\<Sigma>\<Sigma>4_set: 'x) \<Sigma>\<Sigma>4 =
  \<oo>\<pp>4 "'x \<Sigma>\<Sigma>4 \<Sigma>4" | leaf4 "'x"
  for map: \<Sigma>\<Sigma>4_map rel: \<Sigma>\<Sigma>4_rel
declare \<Sigma>\<Sigma>4.ctor_fold_transfer
  [unfolded rel_pre_\<Sigma>\<Sigma>4_def id_apply BNF_Comp.id_bnf_comp_def vimage2p_def, transfer_rule]

lemma \<oo>\<pp>4_transfer[transfer_rule]:
  "(\<Sigma>4_rel (\<Sigma>\<Sigma>4_rel R) ===> \<Sigma>\<Sigma>4_rel R) \<oo>\<pp>4 \<oo>\<pp>4"
  by (rule rel_funI) (erule iffD2[OF \<Sigma>\<Sigma>4.rel_inject(1)])

lemma leaf4_transfer[transfer_rule]: "(R ===> \<Sigma>\<Sigma>4_rel R) leaf4 leaf4"
  by (rule rel_funI) (erule iffD2[OF \<Sigma>\<Sigma>4.rel_inject(2)])

(* The free extension, for an algebra s, of an inteprleaftion i of the
variables into the algebra carrier:  *)
abbreviation "ext4 s \<equiv> rec_\<Sigma>\<Sigma>4 (s o \<Sigma>4_map snd)"
lemmas ext4_\<oo>\<pp>4 = \<Sigma>\<Sigma>4.rec(1)[of "s o \<Sigma>4_map snd" for s,
  unfolded o_apply \<Sigma>4.map_comp snd_convol[unfolded convol_def]]
lemmas ext4_leaf4 = \<Sigma>\<Sigma>4.rec(2)[of "s o \<Sigma>4_map snd" for s,
  unfolded o_apply \<Sigma>4.map_comp snd_convol[unfolded convol_def]]
lemmas leaf4_inj = \<Sigma>\<Sigma>4.inject(2)
lemmas \<oo>\<pp>4_inj = \<Sigma>\<Sigma>4.inject(1)

lemma ext4_alt: "ext4 s f = ctor_fold_\<Sigma>\<Sigma>4 (case_sum s f)"
  apply (rule \<Sigma>\<Sigma>4.ctor_fold_unique)
  apply (rule ext)
  apply (rename_tac x)
  apply (case_tac x)
  apply (auto simp only: rec_\<Sigma>\<Sigma>4_def \<Sigma>\<Sigma>4.ctor_rec fun_eq_iff o_apply BNF_Comp.id_bnf_comp_def
    id_def[symmetric] o_id map_pre_\<Sigma>\<Sigma>4_def id_apply map_sum.simps sum.inject sum.distinct
    \<Sigma>4.map_comp snd_convol split: sum.splits)
  done

(* The term algebra: *)

lemma \<oo>\<pp>4_def_pointfree: "\<oo>\<pp>4 \<equiv> ctor_\<Sigma>\<Sigma>4 o Inl"
unfolding \<oo>\<pp>4_def comp_def BNF_Comp.id_bnf_comp_def .

(* Monadic structure *)
lemma leaf4_def_pointfree: "leaf4 \<equiv> ctor_\<Sigma>\<Sigma>4 o Inr"
unfolding leaf4_def comp_def BNF_Comp.id_bnf_comp_def .

definition flat4 :: "('x \<Sigma>\<Sigma>4) \<Sigma>\<Sigma>4 \<Rightarrow> 'x \<Sigma>\<Sigma>4" where
  flat4_def: "flat4 \<equiv> ext4 \<oo>\<pp>4 id"

lemma flat4_transfer[transfer_rule]: "(\<Sigma>\<Sigma>4_rel (\<Sigma>\<Sigma>4_rel R) ===> \<Sigma>\<Sigma>4_rel R) flat4 flat4"
  unfolding flat4_def ext4_alt by transfer_prover

(* facts about \<Sigma>\<Sigma>4: *)
lemma ctor_fold_\<Sigma>\<Sigma>4_pointfree:
"ctor_fold_\<Sigma>\<Sigma>4 s o ctor_\<Sigma>\<Sigma>4 = s o (map_pre_\<Sigma>\<Sigma>4 id (ctor_fold_\<Sigma>\<Sigma>4 s))"
unfolding comp_def \<Sigma>\<Sigma>4.ctor_fold ..

lemma \<Sigma>\<Sigma>4_map_ctor_\<Sigma>\<Sigma>4:
"\<Sigma>\<Sigma>4_map f o ctor_\<Sigma>\<Sigma>4 = ctor_\<Sigma>\<Sigma>4 o map_sum (\<Sigma>4_map (\<Sigma>\<Sigma>4_map f)) f"
unfolding comp_def
unfolding fun_eq_iff
unfolding \<Sigma>\<Sigma>4.ctor_map
unfolding map_pre_\<Sigma>\<Sigma>4_def  (* careful here and elsewhere: data newdatatype unfolds more *)
unfolding id_apply BNF_Comp.id_bnf_comp_def id_def[symmetric] o_id id_o by simp

lemma dtor_\<Sigma>\<Sigma>4_\<Sigma>\<Sigma>4_map:
"dtor_\<Sigma>\<Sigma>4 o \<Sigma>\<Sigma>4_map f = map_sum (\<Sigma>4_map (\<Sigma>\<Sigma>4_map f)) f o dtor_\<Sigma>\<Sigma>4"
using \<Sigma>\<Sigma>4_map_ctor_\<Sigma>\<Sigma>4[of f] \<Sigma>\<Sigma>4.dtor_ctor \<Sigma>\<Sigma>4.ctor_dtor unfolding comp_def fun_eq_iff by metis

lemma dtor_\<Sigma>\<Sigma>4_ctor_\<Sigma>\<Sigma>4: "dtor_\<Sigma>\<Sigma>4 \<circ> ctor_\<Sigma>\<Sigma>4 = id"
unfolding comp_def \<Sigma>\<Sigma>4.dtor_ctor id_def ..

lemma ctor_\<Sigma>\<Sigma>4_dtor_\<Sigma>\<Sigma>4: "ctor_\<Sigma>\<Sigma>4 \<circ> dtor_\<Sigma>\<Sigma>4 = id"
unfolding comp_def \<Sigma>\<Sigma>4.ctor_dtor id_def ..

lemma \<Sigma>\<Sigma>4_rel_inf: "\<Sigma>\<Sigma>4_rel (R \<sqinter> \<Sigma>3) \<le> \<Sigma>\<Sigma>4_rel R \<sqinter> \<Sigma>\<Sigma>4_rel \<Sigma>3"
  apply (rule inf_greatest)
  apply (rule \<Sigma>\<Sigma>4.rel_mono[OF inf_sup_ord(1)])
  apply (rule \<Sigma>\<Sigma>4.rel_mono[OF inf_sup_ord(2)])
  done

lemma \<Sigma>\<Sigma>4_rel_Grp_\<Sigma>\<Sigma>4_map: "\<Sigma>\<Sigma>4_rel (BNF_Def.Grp UNIV f) x y \<longleftrightarrow> \<Sigma>\<Sigma>4_map f x = y"
  unfolding \<Sigma>\<Sigma>4.rel_Grp by (auto simp: Grp_def)

lemma \<Sigma>\<Sigma>4_rel_\<Sigma>\<Sigma>4_map_\<Sigma>\<Sigma>4_map: "\<Sigma>\<Sigma>4_rel R (\<Sigma>\<Sigma>4_map f x) (\<Sigma>\<Sigma>4_map g y) =
  \<Sigma>\<Sigma>4_rel (BNF_Def.vimage2p f g R) x y"
  unfolding \<Sigma>\<Sigma>4.rel_Grp vimage2p_Grp apply (auto simp: \<Sigma>\<Sigma>4.rel_compp \<Sigma>\<Sigma>4.rel_conversep relcompp.simps)
  apply (intro exI conjI)
  apply (rule iffD2[OF \<Sigma>\<Sigma>4_rel_Grp_\<Sigma>\<Sigma>4_map refl])
  apply assumption
  apply (rule iffD2[OF \<Sigma>\<Sigma>4_rel_Grp_\<Sigma>\<Sigma>4_map refl])
  unfolding \<Sigma>\<Sigma>4_rel_Grp_\<Sigma>\<Sigma>4_map
  apply simp
  done


subsection{* @{term \<Sigma>4} extension theorems *}

theorem ext4_commute:
"ext4 s i o \<oo>\<pp>4 = s o \<Sigma>4_map (ext4 s i)"
unfolding ext4_alt \<oo>\<pp>4_def_pointfree o_assoc ctor_fold_\<Sigma>\<Sigma>4_pointfree map_pre_\<Sigma>\<Sigma>4_def
  case_sum_o_map_sum case_sum_o_inj(1) BNF_Comp.id_bnf_comp_def id_def[symmetric] o_id ..

theorem ext4_comp_leaf4:
"ext4 s i o leaf4 = i"
unfolding ext4_alt leaf4_def_pointfree o_assoc ctor_fold_\<Sigma>\<Sigma>4_pointfree map_pre_\<Sigma>\<Sigma>4_def
  case_sum_o_map_sum case_sum_o_inj(2) id_apply BNF_Comp.id_bnf_comp_def id_def[symmetric] o_id ..

theorem ext4_unique:
assumes leaf4: "f o leaf4 = i" and com: "f o \<oo>\<pp>4 = s o \<Sigma>4_map f"
shows "f = ext4 s i"
unfolding ext4_alt
apply (rule \<Sigma>\<Sigma>4.ctor_fold_unique)
apply (rule sum_comp_cases)
unfolding map_pre_\<Sigma>\<Sigma>4_def case_sum_o_map_sum id_apply o_id case_sum_o_inj
  leaf4[unfolded leaf4_def_pointfree o_assoc] com[unfolded \<oo>\<pp>4_def_pointfree o_assoc]
  BNF_Comp.id_bnf_comp_def id_def[symmetric] id_o
by (rule refl)+

subsection{* Customizing @{term \<Sigma>\<Sigma>4} *}

subsection{* Injectiveness, naturality, adjunction *}

theorem leaf4_natural: "\<Sigma>\<Sigma>4_map f o leaf4 = leaf4 o f"
  using leaf4_transfer[of "BNF_Def.Grp UNIV f"]
  unfolding \<Sigma>\<Sigma>4.rel_Grp
  unfolding Grp_def rel_fun_def by auto

lemma \<oo>\<pp>4_natural: "\<oo>\<pp>4 o \<Sigma>4_map (\<Sigma>\<Sigma>4_map f) = \<Sigma>\<Sigma>4_map f o \<oo>\<pp>4"
  using \<oo>\<pp>4_transfer[of "BNF_Def.Grp UNIV f"]
  unfolding \<Sigma>4.rel_Grp \<Sigma>\<Sigma>4.rel_Grp \<Sigma>4_map_def
  unfolding Grp_def rel_fun_def by auto

lemma \<Sigma>\<Sigma>4_map_def2: "\<Sigma>\<Sigma>4_map i = ext4 \<oo>\<pp>4 (leaf4 o i)"
by (rule ext4_unique[OF leaf4_natural \<oo>\<pp>4_natural[symmetric]])

lemma ext4_\<oo>\<pp>4_leaf4: "ext4 \<oo>\<pp>4 leaf4 = id"
apply (rule ext4_unique[symmetric]) unfolding \<Sigma>4.map_id0 o_id id_o by (rule refl)+

lemma ext4_\<Sigma>\<Sigma>4_map:
"ext4 s (j o f) = ext4 s j o \<Sigma>\<Sigma>4_map f"
proof (rule ext4_unique[symmetric])
  show "ext4 s j \<circ> \<Sigma>\<Sigma>4_map f \<circ> leaf4 = j \<circ> f"
  unfolding o_assoc[symmetric] leaf4_natural
  unfolding o_assoc ext4_comp_leaf4 ..
next
  show "ext4 s j \<circ> \<Sigma>\<Sigma>4_map f \<circ> \<oo>\<pp>4 = s \<circ> \<Sigma>4_map (ext4 s j \<circ> \<Sigma>\<Sigma>4_map f)"
  unfolding o_assoc[symmetric] \<oo>\<pp>4_natural[symmetric]
  unfolding o_assoc ext4_commute
  unfolding o_assoc[symmetric] \<Sigma>4.map_comp0 ..
qed

lemma ext4_\<Sigma>4_map:
assumes "t o \<Sigma>4_map f = f o s"
shows "ext4 t (f o i) = f o ext4 s i"
proof (rule ext4_unique[symmetric])
  show "f \<circ> ext4 s i \<circ> leaf4 = f o i"
  unfolding o_assoc[symmetric] ext4_comp_leaf4 ..
next
  show "f \<circ> ext4 s i \<circ> \<oo>\<pp>4 = t \<circ> \<Sigma>4_map (f \<circ> ext4 s i)"
  unfolding \<Sigma>4.map_comp0 o_assoc assms
  unfolding o_assoc[symmetric] ext4_commute[symmetric] ..
qed


subsection{* Monadic laws *}

lemma flat4_commute: "\<oo>\<pp>4 \<circ> \<Sigma>4_map flat4 = flat4 \<circ> \<oo>\<pp>4"
unfolding flat4_def ext4_commute ..

(* The 2 identity laws*)
theorem flat4_leaf4: "flat4 o leaf4 = id"
unfolding flat4_def ext4_comp_leaf4 ..

theorem leaf4_flat4: "flat4 o \<Sigma>\<Sigma>4_map leaf4 = id"
unfolding flat4_def ext4_\<Sigma>\<Sigma>4_map[symmetric] id_o ext4_\<oo>\<pp>4_leaf4 ..

theorem flat4_natural: "flat4 o \<Sigma>\<Sigma>4_map (\<Sigma>\<Sigma>4_map i) = \<Sigma>\<Sigma>4_map i o flat4"
  using flat4_transfer[of "BNF_Def.Grp UNIV i"]
  unfolding prod.rel_Grp \<Sigma>\<Sigma>4.rel_Grp
  unfolding Grp_def rel_fun_def by auto

(* Associativity *)
theorem flat4_assoc: "flat4 o \<Sigma>\<Sigma>4_map flat4 = flat4 o flat4"
unfolding flat4_def unfolding ext4_\<Sigma>\<Sigma>4_map[symmetric] id_o
proof(rule ext4_unique[symmetric], unfold flat4_def[symmetric])
  show "flat4 \<circ> flat4 \<circ> leaf4 = flat4"
  unfolding o_assoc[symmetric] flat4_leaf4 o_id ..
next
  show "flat4 \<circ> flat4 \<circ> \<oo>\<pp>4 = \<oo>\<pp>4 \<circ> \<Sigma>4_map (flat4 \<circ> flat4)"
  unfolding flat4_def unfolding o_assoc[symmetric] ext4_commute
  unfolding flat4_def[symmetric]
  unfolding \<Sigma>4.map_comp0 o_assoc unfolding flat4_commute ..
qed

definition K4_as_\<Sigma>\<Sigma>4 :: "'a K4 \<Rightarrow> 'a \<Sigma>\<Sigma>4" where
"K4_as_\<Sigma>\<Sigma>4 \<equiv> \<oo>\<pp>4 o \<Sigma>4_map leaf4 o Abs_\<Sigma>4 o Inr"

lemma K4_as_\<Sigma>\<Sigma>4_transfer[transfer_rule]:
  "(K4_rel R ===> \<Sigma>\<Sigma>4_rel R) K4_as_\<Sigma>\<Sigma>4 K4_as_\<Sigma>\<Sigma>4"
  unfolding K4_as_\<Sigma>\<Sigma>4_def by transfer_prover

lemma K4_as_\<Sigma>\<Sigma>4_natural:
"K4_as_\<Sigma>\<Sigma>4 o K4_map f = \<Sigma>\<Sigma>4_map f o K4_as_\<Sigma>\<Sigma>4"
  using K4_as_\<Sigma>\<Sigma>4_transfer[of "BNF_Def.Grp UNIV f"]
  unfolding K4.rel_Grp \<Sigma>\<Sigma>4.rel_Grp
  unfolding Grp_def rel_fun_def by auto

end