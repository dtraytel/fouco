header{* Free algebras for an BNF *}

(* Free algebra constructed for a sum of two BNF's S and K: *)
(* Notations: Identical to FreeAlg, just that constants and types are suffixed by "step" instead of "base": *)

theory Stream_FreeAlg5
imports Stream_Input5
begin

declare K5.map_transfer[transfer_rule]

(* The new-operation functor: *)

composition_bnf (open) raw_\<Sigma>5: "'a \<Sigma>4 + 'a K5"
typedef 'a \<Sigma>5 = "UNIV :: ('a \<Sigma>4 + 'a K5) set" by (rule UNIV_witness)

setup_lifting type_definition_\<Sigma>5

lift_definition \<Sigma>5_map :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Sigma>5 \<Rightarrow> 'b \<Sigma>5" is "\<lambda>f. map_sum (\<Sigma>4_map f) (K5_map f)" .
lift_definition \<Sigma>5_set :: "'a \<Sigma>5 \<Rightarrow> 'a set"
  is "\<lambda>x. UNION (Basic_BNFs.setl x) \<Sigma>4_set \<union> UNION (Basic_BNFs.setr x) K5_set" .
lift_definition \<Sigma>5_rel :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a \<Sigma>5 \<Rightarrow> 'b \<Sigma>5 \<Rightarrow> bool"
  is "\<lambda>R. rel_sum (\<Sigma>4_rel R) (K5_rel R)" .
typedef \<Sigma>5_bd_type = "UNIV :: ((\<Sigma>4_bd_type + bd_type_K5) \<times> nat) set" by (rule UNIV_witness)
definition "\<Sigma>5_bd = dir_image ((\<Sigma>4_bd +c bd_K5) *c natLeq) Abs_\<Sigma>5_bd_type"

bnf "'a \<Sigma>5"
  map: \<Sigma>5_map
  sets: \<Sigma>5_set
  bd: \<Sigma>5_bd 
  rel: \<Sigma>5_rel
unfolding \<Sigma>5_bd_def
apply -
apply transfer apply (rule raw_\<Sigma>5.map_id0)
apply transfer apply (rule raw_\<Sigma>5.map_comp0)
apply transfer apply (erule raw_\<Sigma>5.map_cong0)
apply transfer apply (rule raw_\<Sigma>5.set_map0)
apply (rule card_order_dir_image[OF bijI raw_\<Sigma>5.bd_card_order])
apply (metis inj_on_def Abs_\<Sigma>5_bd_type_inverse[OF UNIV_I])
apply (metis surj_def Abs_\<Sigma>5_bd_type_cases)
apply (rule conjunct1[OF Cinfinite_cong[OF dir_image[OF _ raw_\<Sigma>5.bd_Card_order] raw_\<Sigma>5.bd_Cinfinite]])
apply (metis Abs_\<Sigma>5_bd_type_inverse[OF UNIV_I])
apply (unfold \<Sigma>5_set_def map_fun_def id_o) [1] apply (subst o_apply)
apply (rule ordLeq_ordIso_trans[OF raw_\<Sigma>5.set_bd dir_image[OF _ raw_\<Sigma>5.bd_Card_order]])
apply (metis Abs_\<Sigma>5_bd_type_inverse[OF UNIV_I])
apply (rule predicate2I) apply transfer apply (subst raw_\<Sigma>5.rel_compp) apply assumption
apply transfer' apply (rule raw_\<Sigma>5.rel_compp_Grp)
done

declare \<Sigma>5.map_transfer[transfer_rule]

lemma Rep_\<Sigma>5_transfer[transfer_rule]: "(\<Sigma>5_rel R ===> rel_sum (\<Sigma>4_rel R) (K5_rel R)) Rep_\<Sigma>5 Rep_\<Sigma>5"
  unfolding rel_fun_def by transfer blast

lemma Abs_\<Sigma>5_transfer[transfer_rule]: "(rel_sum (\<Sigma>4_rel R) (K5_rel R) ===> \<Sigma>5_rel R) Abs_\<Sigma>5 Abs_\<Sigma>5"
  unfolding rel_fun_def by transfer blast

theorem Rep_\<Sigma>5_natural: "map_sum (\<Sigma>4_map f) (K5_map f) o Rep_\<Sigma>5 = Rep_\<Sigma>5 o \<Sigma>5_map f"
  using Rep_\<Sigma>5_transfer[of "BNF_Def.Grp UNIV f"]
  unfolding \<Sigma>5.rel_Grp raw_\<Sigma>5.rel_Grp
  unfolding Grp_def rel_fun_def by auto

theorem Abs_\<Sigma>5_natural: "\<Sigma>5_map f o Abs_\<Sigma>5 = Abs_\<Sigma>5 o map_sum (\<Sigma>4_map f) (K5_map f)"
  using Abs_\<Sigma>5_transfer[of "BNF_Def.Grp UNIV f"]
  unfolding \<Sigma>5.rel_Grp raw_\<Sigma>5.rel_Grp
  unfolding Grp_def rel_fun_def by auto

lemma Rep_\<Sigma>5_o_Abs_\<Sigma>5: "Rep_\<Sigma>5 o Abs_\<Sigma>5 = id"
  apply (rule ext)
  apply (rule box_equals[OF _ o_apply[symmetric] id_apply[symmetric]])
  apply (rule Abs_\<Sigma>5_inverse[OF UNIV_I])
  done

lemma \<Sigma>5_rel_\<Sigma>5_map_\<Sigma>5_map:
  "\<Sigma>5_rel R (\<Sigma>5_map f x) (\<Sigma>5_map g y) = \<Sigma>5_rel (BNF_Def.vimage2p f g R) x y"
  unfolding \<Sigma>5.rel_Grp vimage2p_Grp \<Sigma>5.rel_compp \<Sigma>5.rel_conversep
  unfolding relcompp.simps Grp_def by simp

subsection{* Definitions and basic setup *}

(* 'x \<Sigma>\<Sigma>5 consist of \<Sigma>5-terms with variables in 'x: *)
datatype_new (\<Sigma>\<Sigma>5_set: 'x) \<Sigma>\<Sigma>5 =
  \<oo>\<pp>5 "'x \<Sigma>\<Sigma>5 \<Sigma>5" | leaf5 "'x"
  for map: \<Sigma>\<Sigma>5_map rel: \<Sigma>\<Sigma>5_rel
declare \<Sigma>\<Sigma>5.ctor_fold_transfer
  [unfolded rel_pre_\<Sigma>\<Sigma>5_def id_apply BNF_Comp.id_bnf_comp_def vimage2p_def, transfer_rule]

lemma \<oo>\<pp>5_transfer[transfer_rule]:
  "(\<Sigma>5_rel (\<Sigma>\<Sigma>5_rel R) ===> \<Sigma>\<Sigma>5_rel R) \<oo>\<pp>5 \<oo>\<pp>5"
  by (rule rel_funI) (erule iffD2[OF \<Sigma>\<Sigma>5.rel_inject(1)])

lemma leaf5_transfer[transfer_rule]: "(R ===> \<Sigma>\<Sigma>5_rel R) leaf5 leaf5"
  by (rule rel_funI) (erule iffD2[OF \<Sigma>\<Sigma>5.rel_inject(2)])

(* The free extension, for an algebra s, of an inteprleaftion i of the
variables into the algebra carrier:  *)
abbreviation "ext5 s \<equiv> rec_\<Sigma>\<Sigma>5 (s o \<Sigma>5_map snd)"
lemmas ext5_\<oo>\<pp>5 = \<Sigma>\<Sigma>5.rec(1)[of "s o \<Sigma>5_map snd" for s,
  unfolded o_apply \<Sigma>5.map_comp snd_convol[unfolded convol_def]]
lemmas ext5_leaf5 = \<Sigma>\<Sigma>5.rec(2)[of "s o \<Sigma>5_map snd" for s,
  unfolded o_apply \<Sigma>5.map_comp snd_convol[unfolded convol_def]]
lemmas leaf5_inj = \<Sigma>\<Sigma>5.inject(2)
lemmas \<oo>\<pp>5_inj = \<Sigma>\<Sigma>5.inject(1)

lemma ext5_alt: "ext5 s f = ctor_fold_\<Sigma>\<Sigma>5 (case_sum s f)"
  apply (rule \<Sigma>\<Sigma>5.ctor_fold_unique)
  apply (rule ext)
  apply (rename_tac x)
  apply (case_tac x)
  apply (auto simp only: rec_\<Sigma>\<Sigma>5_def \<Sigma>\<Sigma>5.ctor_rec fun_eq_iff o_apply BNF_Comp.id_bnf_comp_def
    id_def[symmetric] o_id map_pre_\<Sigma>\<Sigma>5_def id_apply map_sum.simps sum.inject sum.distinct
    \<Sigma>5.map_comp snd_convol split: sum.splits)
  done

(* The term algebra: *)

lemma \<oo>\<pp>5_def_pointfree: "\<oo>\<pp>5 \<equiv> ctor_\<Sigma>\<Sigma>5 o Inl"
unfolding \<oo>\<pp>5_def comp_def BNF_Comp.id_bnf_comp_def .

(* Monadic structure *)
lemma leaf5_def_pointfree: "leaf5 \<equiv> ctor_\<Sigma>\<Sigma>5 o Inr"
unfolding leaf5_def comp_def BNF_Comp.id_bnf_comp_def .

definition flat5 :: "('x \<Sigma>\<Sigma>5) \<Sigma>\<Sigma>5 \<Rightarrow> 'x \<Sigma>\<Sigma>5" where
  flat5_def: "flat5 \<equiv> ext5 \<oo>\<pp>5 id"

lemma flat5_transfer[transfer_rule]: "(\<Sigma>\<Sigma>5_rel (\<Sigma>\<Sigma>5_rel R) ===> \<Sigma>\<Sigma>5_rel R) flat5 flat5"
  unfolding flat5_def ext5_alt by transfer_prover

(* facts about \<Sigma>\<Sigma>5: *)
lemma ctor_fold_\<Sigma>\<Sigma>5_pointfree:
"ctor_fold_\<Sigma>\<Sigma>5 s o ctor_\<Sigma>\<Sigma>5 = s o (map_pre_\<Sigma>\<Sigma>5 id (ctor_fold_\<Sigma>\<Sigma>5 s))"
unfolding comp_def \<Sigma>\<Sigma>5.ctor_fold ..

lemma \<Sigma>\<Sigma>5_map_ctor_\<Sigma>\<Sigma>5:
"\<Sigma>\<Sigma>5_map f o ctor_\<Sigma>\<Sigma>5 = ctor_\<Sigma>\<Sigma>5 o map_sum (\<Sigma>5_map (\<Sigma>\<Sigma>5_map f)) f"
unfolding comp_def
unfolding fun_eq_iff
unfolding \<Sigma>\<Sigma>5.ctor_map
unfolding map_pre_\<Sigma>\<Sigma>5_def  (* careful here and elsewhere: data newdatatype unfolds more *)
unfolding id_apply BNF_Comp.id_bnf_comp_def id_def[symmetric] o_id id_o by simp

lemma dtor_\<Sigma>\<Sigma>5_\<Sigma>\<Sigma>5_map:
"dtor_\<Sigma>\<Sigma>5 o \<Sigma>\<Sigma>5_map f = map_sum (\<Sigma>5_map (\<Sigma>\<Sigma>5_map f)) f o dtor_\<Sigma>\<Sigma>5"
using \<Sigma>\<Sigma>5_map_ctor_\<Sigma>\<Sigma>5[of f] \<Sigma>\<Sigma>5.dtor_ctor \<Sigma>\<Sigma>5.ctor_dtor unfolding comp_def fun_eq_iff by metis

lemma dtor_\<Sigma>\<Sigma>5_ctor_\<Sigma>\<Sigma>5: "dtor_\<Sigma>\<Sigma>5 \<circ> ctor_\<Sigma>\<Sigma>5 = id"
unfolding comp_def \<Sigma>\<Sigma>5.dtor_ctor id_def ..

lemma ctor_\<Sigma>\<Sigma>5_dtor_\<Sigma>\<Sigma>5: "ctor_\<Sigma>\<Sigma>5 \<circ> dtor_\<Sigma>\<Sigma>5 = id"
unfolding comp_def \<Sigma>\<Sigma>5.ctor_dtor id_def ..

lemma \<Sigma>\<Sigma>5_rel_inf: "\<Sigma>\<Sigma>5_rel (R \<sqinter> \<Sigma>4) \<le> \<Sigma>\<Sigma>5_rel R \<sqinter> \<Sigma>\<Sigma>5_rel \<Sigma>4"
  apply (rule inf_greatest)
  apply (rule \<Sigma>\<Sigma>5.rel_mono[OF inf_sup_ord(1)])
  apply (rule \<Sigma>\<Sigma>5.rel_mono[OF inf_sup_ord(2)])
  done

lemma \<Sigma>\<Sigma>5_rel_Grp_\<Sigma>\<Sigma>5_map: "\<Sigma>\<Sigma>5_rel (BNF_Def.Grp UNIV f) x y \<longleftrightarrow> \<Sigma>\<Sigma>5_map f x = y"
  unfolding \<Sigma>\<Sigma>5.rel_Grp by (auto simp: Grp_def)

lemma \<Sigma>\<Sigma>5_rel_\<Sigma>\<Sigma>5_map_\<Sigma>\<Sigma>5_map: "\<Sigma>\<Sigma>5_rel R (\<Sigma>\<Sigma>5_map f x) (\<Sigma>\<Sigma>5_map g y) =
  \<Sigma>\<Sigma>5_rel (BNF_Def.vimage2p f g R) x y"
  unfolding \<Sigma>\<Sigma>5.rel_Grp vimage2p_Grp apply (auto simp: \<Sigma>\<Sigma>5.rel_compp \<Sigma>\<Sigma>5.rel_conversep relcompp.simps)
  apply (intro exI conjI)
  apply (rule iffD2[OF \<Sigma>\<Sigma>5_rel_Grp_\<Sigma>\<Sigma>5_map refl])
  apply assumption
  apply (rule iffD2[OF \<Sigma>\<Sigma>5_rel_Grp_\<Sigma>\<Sigma>5_map refl])
  unfolding \<Sigma>\<Sigma>5_rel_Grp_\<Sigma>\<Sigma>5_map
  apply simp
  done


subsection{* @{term \<Sigma>5} extension theorems *}

theorem ext5_commute:
"ext5 s i o \<oo>\<pp>5 = s o \<Sigma>5_map (ext5 s i)"
unfolding ext5_alt \<oo>\<pp>5_def_pointfree o_assoc ctor_fold_\<Sigma>\<Sigma>5_pointfree map_pre_\<Sigma>\<Sigma>5_def
  case_sum_o_map_sum case_sum_o_inj(1) BNF_Comp.id_bnf_comp_def id_def[symmetric] o_id ..

theorem ext5_comp_leaf5:
"ext5 s i o leaf5 = i"
unfolding ext5_alt leaf5_def_pointfree o_assoc ctor_fold_\<Sigma>\<Sigma>5_pointfree map_pre_\<Sigma>\<Sigma>5_def
  case_sum_o_map_sum case_sum_o_inj(2) id_apply BNF_Comp.id_bnf_comp_def id_def[symmetric] o_id ..

theorem ext5_unique:
assumes leaf5: "f o leaf5 = i" and com: "f o \<oo>\<pp>5 = s o \<Sigma>5_map f"
shows "f = ext5 s i"
unfolding ext5_alt
apply (rule \<Sigma>\<Sigma>5.ctor_fold_unique)
apply (rule sum_comp_cases)
unfolding map_pre_\<Sigma>\<Sigma>5_def case_sum_o_map_sum id_apply o_id case_sum_o_inj
  leaf5[unfolded leaf5_def_pointfree o_assoc] com[unfolded \<oo>\<pp>5_def_pointfree o_assoc]
  BNF_Comp.id_bnf_comp_def id_def[symmetric] id_o
by (rule refl)+

subsection{* Customizing @{term \<Sigma>\<Sigma>5} *}

subsection{* Injectiveness, naturality, adjunction *}

theorem leaf5_natural: "\<Sigma>\<Sigma>5_map f o leaf5 = leaf5 o f"
  using leaf5_transfer[of "BNF_Def.Grp UNIV f"]
  unfolding \<Sigma>\<Sigma>5.rel_Grp
  unfolding Grp_def rel_fun_def by auto

lemma \<oo>\<pp>5_natural: "\<oo>\<pp>5 o \<Sigma>5_map (\<Sigma>\<Sigma>5_map f) = \<Sigma>\<Sigma>5_map f o \<oo>\<pp>5"
  using \<oo>\<pp>5_transfer[of "BNF_Def.Grp UNIV f"]
  unfolding \<Sigma>5.rel_Grp \<Sigma>\<Sigma>5.rel_Grp \<Sigma>5_map_def
  unfolding Grp_def rel_fun_def by auto

lemma \<Sigma>\<Sigma>5_map_def2: "\<Sigma>\<Sigma>5_map i = ext5 \<oo>\<pp>5 (leaf5 o i)"
by (rule ext5_unique[OF leaf5_natural \<oo>\<pp>5_natural[symmetric]])

lemma ext5_\<oo>\<pp>5_leaf5: "ext5 \<oo>\<pp>5 leaf5 = id"
apply (rule ext5_unique[symmetric]) unfolding \<Sigma>5.map_id0 o_id id_o by (rule refl)+

lemma ext5_\<Sigma>\<Sigma>5_map:
"ext5 s (j o f) = ext5 s j o \<Sigma>\<Sigma>5_map f"
proof (rule ext5_unique[symmetric])
  show "ext5 s j \<circ> \<Sigma>\<Sigma>5_map f \<circ> leaf5 = j \<circ> f"
  unfolding o_assoc[symmetric] leaf5_natural
  unfolding o_assoc ext5_comp_leaf5 ..
next
  show "ext5 s j \<circ> \<Sigma>\<Sigma>5_map f \<circ> \<oo>\<pp>5 = s \<circ> \<Sigma>5_map (ext5 s j \<circ> \<Sigma>\<Sigma>5_map f)"
  unfolding o_assoc[symmetric] \<oo>\<pp>5_natural[symmetric]
  unfolding o_assoc ext5_commute
  unfolding o_assoc[symmetric] \<Sigma>5.map_comp0 ..
qed

lemma ext5_\<Sigma>5_map:
assumes "t o \<Sigma>5_map f = f o s"
shows "ext5 t (f o i) = f o ext5 s i"
proof (rule ext5_unique[symmetric])
  show "f \<circ> ext5 s i \<circ> leaf5 = f o i"
  unfolding o_assoc[symmetric] ext5_comp_leaf5 ..
next
  show "f \<circ> ext5 s i \<circ> \<oo>\<pp>5 = t \<circ> \<Sigma>5_map (f \<circ> ext5 s i)"
  unfolding \<Sigma>5.map_comp0 o_assoc assms
  unfolding o_assoc[symmetric] ext5_commute[symmetric] ..
qed


subsection{* Monadic laws *}

lemma flat5_commute: "\<oo>\<pp>5 \<circ> \<Sigma>5_map flat5 = flat5 \<circ> \<oo>\<pp>5"
unfolding flat5_def ext5_commute ..

(* The 2 identity laws*)
theorem flat5_leaf5: "flat5 o leaf5 = id"
unfolding flat5_def ext5_comp_leaf5 ..

theorem leaf5_flat5: "flat5 o \<Sigma>\<Sigma>5_map leaf5 = id"
unfolding flat5_def ext5_\<Sigma>\<Sigma>5_map[symmetric] id_o ext5_\<oo>\<pp>5_leaf5 ..

theorem flat5_natural: "flat5 o \<Sigma>\<Sigma>5_map (\<Sigma>\<Sigma>5_map i) = \<Sigma>\<Sigma>5_map i o flat5"
  using flat5_transfer[of "BNF_Def.Grp UNIV i"]
  unfolding prod.rel_Grp \<Sigma>\<Sigma>5.rel_Grp
  unfolding Grp_def rel_fun_def by auto

(* Associativity *)
theorem flat5_assoc: "flat5 o \<Sigma>\<Sigma>5_map flat5 = flat5 o flat5"
unfolding flat5_def unfolding ext5_\<Sigma>\<Sigma>5_map[symmetric] id_o
proof(rule ext5_unique[symmetric], unfold flat5_def[symmetric])
  show "flat5 \<circ> flat5 \<circ> leaf5 = flat5"
  unfolding o_assoc[symmetric] flat5_leaf5 o_id ..
next
  show "flat5 \<circ> flat5 \<circ> \<oo>\<pp>5 = \<oo>\<pp>5 \<circ> \<Sigma>5_map (flat5 \<circ> flat5)"
  unfolding flat5_def unfolding o_assoc[symmetric] ext5_commute
  unfolding flat5_def[symmetric]
  unfolding \<Sigma>5.map_comp0 o_assoc unfolding flat5_commute ..
qed

definition K5_as_\<Sigma>\<Sigma>5 :: "'a K5 \<Rightarrow> 'a \<Sigma>\<Sigma>5" where
"K5_as_\<Sigma>\<Sigma>5 \<equiv> \<oo>\<pp>5 o \<Sigma>5_map leaf5 o Abs_\<Sigma>5 o Inr"

lemma K5_as_\<Sigma>\<Sigma>5_transfer[transfer_rule]:
  "(K5_rel R ===> \<Sigma>\<Sigma>5_rel R) K5_as_\<Sigma>\<Sigma>5 K5_as_\<Sigma>\<Sigma>5"
  unfolding K5_as_\<Sigma>\<Sigma>5_def by transfer_prover

lemma K5_as_\<Sigma>\<Sigma>5_natural:
"K5_as_\<Sigma>\<Sigma>5 o K5_map f = \<Sigma>\<Sigma>5_map f o K5_as_\<Sigma>\<Sigma>5"
  using K5_as_\<Sigma>\<Sigma>5_transfer[of "BNF_Def.Grp UNIV f"]
  unfolding K5.rel_Grp \<Sigma>\<Sigma>5.rel_Grp
  unfolding Grp_def rel_fun_def by auto

end