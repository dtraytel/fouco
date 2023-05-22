header{* Free algebras for an BNF *}

(* Free algebra constructed for a sum of two BNF's S and K: *)
(* Notations: Identical to FreeAlg, just that constants and types are suffixed by "step" instead of "base": *)

theory Stream_FreeAlg6
imports Stream_Input6
begin

declare K6.map_transfer[transfer_rule]

(* The new-operation functor: *)

composition_bnf (open) raw_\<Sigma>6: "'a \<Sigma>5 + 'a K6"
typedef 'a \<Sigma>6 = "UNIV :: ('a \<Sigma>5 + 'a K6) set" by (rule UNIV_witness)

setup_lifting type_definition_\<Sigma>6

lift_definition \<Sigma>6_map :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Sigma>6 \<Rightarrow> 'b \<Sigma>6" is "\<lambda>f. map_sum (\<Sigma>5_map f) (K6_map f)" .
lift_definition \<Sigma>6_set :: "'a \<Sigma>6 \<Rightarrow> 'a set"
  is "\<lambda>x. UNION (Basic_BNFs.setl x) \<Sigma>5_set \<union> UNION (Basic_BNFs.setr x) K6_set" .
lift_definition \<Sigma>6_rel :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a \<Sigma>6 \<Rightarrow> 'b \<Sigma>6 \<Rightarrow> bool"
  is "\<lambda>R. rel_sum (\<Sigma>5_rel R) (K6_rel R)" .
typedef \<Sigma>6_bd_type = "UNIV :: ((\<Sigma>5_bd_type + bd_type_K6) \<times> nat) set" by (rule UNIV_witness)
definition "\<Sigma>6_bd = dir_image ((\<Sigma>5_bd +c bd_K6) *c natLeq) Abs_\<Sigma>6_bd_type"

bnf "'a \<Sigma>6"
  map: \<Sigma>6_map
  sets: \<Sigma>6_set
  bd: \<Sigma>6_bd 
  rel: \<Sigma>6_rel
unfolding \<Sigma>6_bd_def
apply -
apply transfer apply (rule raw_\<Sigma>6.map_id0)
apply transfer apply (rule raw_\<Sigma>6.map_comp0)
apply transfer apply (erule raw_\<Sigma>6.map_cong0)
apply transfer apply (rule raw_\<Sigma>6.set_map0)
apply (rule card_order_dir_image[OF bijI raw_\<Sigma>6.bd_card_order])
apply (metis inj_on_def Abs_\<Sigma>6_bd_type_inverse[OF UNIV_I])
apply (metis surj_def Abs_\<Sigma>6_bd_type_cases)
apply (rule conjunct1[OF Cinfinite_cong[OF dir_image[OF _ raw_\<Sigma>6.bd_Card_order] raw_\<Sigma>6.bd_Cinfinite]])
apply (metis Abs_\<Sigma>6_bd_type_inverse[OF UNIV_I])
apply (unfold \<Sigma>6_set_def map_fun_def id_o) [1] apply (subst o_apply)
apply (rule ordLeq_ordIso_trans[OF raw_\<Sigma>6.set_bd dir_image[OF _ raw_\<Sigma>6.bd_Card_order]])
apply (metis Abs_\<Sigma>6_bd_type_inverse[OF UNIV_I])
apply (rule predicate2I) apply transfer apply (subst raw_\<Sigma>6.rel_compp) apply assumption
apply transfer' apply (rule raw_\<Sigma>6.rel_compp_Grp)
done

declare \<Sigma>6.map_transfer[transfer_rule]

lemma Rep_\<Sigma>6_transfer[transfer_rule]: "(\<Sigma>6_rel R ===> rel_sum (\<Sigma>5_rel R) (K6_rel R)) Rep_\<Sigma>6 Rep_\<Sigma>6"
  unfolding rel_fun_def by transfer blast

lemma Abs_\<Sigma>6_transfer[transfer_rule]: "(rel_sum (\<Sigma>5_rel R) (K6_rel R) ===> \<Sigma>6_rel R) Abs_\<Sigma>6 Abs_\<Sigma>6"
  unfolding rel_fun_def by transfer blast

theorem Rep_\<Sigma>6_natural: "map_sum (\<Sigma>5_map f) (K6_map f) o Rep_\<Sigma>6 = Rep_\<Sigma>6 o \<Sigma>6_map f"
  using Rep_\<Sigma>6_transfer[of "BNF_Def.Grp UNIV f"]
  unfolding \<Sigma>6.rel_Grp raw_\<Sigma>6.rel_Grp
  unfolding Grp_def rel_fun_def by auto

theorem Abs_\<Sigma>6_natural: "\<Sigma>6_map f o Abs_\<Sigma>6 = Abs_\<Sigma>6 o map_sum (\<Sigma>5_map f) (K6_map f)"
  using Abs_\<Sigma>6_transfer[of "BNF_Def.Grp UNIV f"]
  unfolding \<Sigma>6.rel_Grp raw_\<Sigma>6.rel_Grp
  unfolding Grp_def rel_fun_def by auto

lemma Rep_\<Sigma>6_o_Abs_\<Sigma>6: "Rep_\<Sigma>6 o Abs_\<Sigma>6 = id"
  apply (rule ext)
  apply (rule box_equals[OF _ o_apply[symmetric] id_apply[symmetric]])
  apply (rule Abs_\<Sigma>6_inverse[OF UNIV_I])
  done

lemma \<Sigma>6_rel_\<Sigma>6_map_\<Sigma>6_map:
  "\<Sigma>6_rel R (\<Sigma>6_map f x) (\<Sigma>6_map g y) = \<Sigma>6_rel (BNF_Def.vimage2p f g R) x y"
  unfolding \<Sigma>6.rel_Grp vimage2p_Grp \<Sigma>6.rel_compp \<Sigma>6.rel_conversep
  unfolding relcompp.simps Grp_def by simp

subsection{* Definitions and basic setup *}

(* 'x \<Sigma>\<Sigma>6 consist of \<Sigma>6-terms with variables in 'x: *)
datatype_new (\<Sigma>\<Sigma>6_set: 'x) \<Sigma>\<Sigma>6 =
  \<oo>\<pp>6 "'x \<Sigma>\<Sigma>6 \<Sigma>6" | leaf6 "'x"
  for map: \<Sigma>\<Sigma>6_map rel: \<Sigma>\<Sigma>6_rel
declare \<Sigma>\<Sigma>6.ctor_fold_transfer
  [unfolded rel_pre_\<Sigma>\<Sigma>6_def id_apply BNF_Comp.id_bnf_comp_def vimage2p_def, transfer_rule]

lemma \<oo>\<pp>6_transfer[transfer_rule]:
  "(\<Sigma>6_rel (\<Sigma>\<Sigma>6_rel R) ===> \<Sigma>\<Sigma>6_rel R) \<oo>\<pp>6 \<oo>\<pp>6"
  by (rule rel_funI) (erule iffD2[OF \<Sigma>\<Sigma>6.rel_inject(1)])

lemma leaf6_transfer[transfer_rule]: "(R ===> \<Sigma>\<Sigma>6_rel R) leaf6 leaf6"
  by (rule rel_funI) (erule iffD2[OF \<Sigma>\<Sigma>6.rel_inject(2)])

(* The free extension, for an algebra s, of an inteprleaftion i of the
variables into the algebra carrier:  *)
abbreviation "ext6 s \<equiv> rec_\<Sigma>\<Sigma>6 (s o \<Sigma>6_map snd)"
lemmas ext6_\<oo>\<pp>6 = \<Sigma>\<Sigma>6.rec(1)[of "s o \<Sigma>6_map snd" for s,
  unfolded o_apply \<Sigma>6.map_comp snd_convol[unfolded convol_def]]
lemmas ext6_leaf6 = \<Sigma>\<Sigma>6.rec(2)[of "s o \<Sigma>6_map snd" for s,
  unfolded o_apply \<Sigma>6.map_comp snd_convol[unfolded convol_def]]
lemmas leaf6_inj = \<Sigma>\<Sigma>6.inject(2)
lemmas \<oo>\<pp>6_inj = \<Sigma>\<Sigma>6.inject(1)

lemma ext6_alt: "ext6 s f = ctor_fold_\<Sigma>\<Sigma>6 (case_sum s f)"
  apply (rule \<Sigma>\<Sigma>6.ctor_fold_unique)
  apply (rule ext)
  apply (rename_tac x)
  apply (case_tac x)
  apply (auto simp only: rec_\<Sigma>\<Sigma>6_def \<Sigma>\<Sigma>6.ctor_rec fun_eq_iff o_apply BNF_Comp.id_bnf_comp_def
    id_def[symmetric] o_id map_pre_\<Sigma>\<Sigma>6_def id_apply map_sum.simps sum.inject sum.distinct
    \<Sigma>6.map_comp snd_convol split: sum.splits)
  done

(* The term algebra: *)

lemma \<oo>\<pp>6_def_pointfree: "\<oo>\<pp>6 \<equiv> ctor_\<Sigma>\<Sigma>6 o Inl"
unfolding \<oo>\<pp>6_def comp_def BNF_Comp.id_bnf_comp_def .

(* Monadic structure *)
lemma leaf6_def_pointfree: "leaf6 \<equiv> ctor_\<Sigma>\<Sigma>6 o Inr"
unfolding leaf6_def comp_def BNF_Comp.id_bnf_comp_def .

definition flat6 :: "('x \<Sigma>\<Sigma>6) \<Sigma>\<Sigma>6 \<Rightarrow> 'x \<Sigma>\<Sigma>6" where
  flat6_def: "flat6 \<equiv> ext6 \<oo>\<pp>6 id"

lemma flat6_transfer[transfer_rule]: "(\<Sigma>\<Sigma>6_rel (\<Sigma>\<Sigma>6_rel R) ===> \<Sigma>\<Sigma>6_rel R) flat6 flat6"
  unfolding flat6_def ext6_alt by transfer_prover

(* facts about \<Sigma>\<Sigma>6: *)
lemma ctor_fold_\<Sigma>\<Sigma>6_pointfree:
"ctor_fold_\<Sigma>\<Sigma>6 s o ctor_\<Sigma>\<Sigma>6 = s o (map_pre_\<Sigma>\<Sigma>6 id (ctor_fold_\<Sigma>\<Sigma>6 s))"
unfolding comp_def \<Sigma>\<Sigma>6.ctor_fold ..

lemma \<Sigma>\<Sigma>6_map_ctor_\<Sigma>\<Sigma>6:
"\<Sigma>\<Sigma>6_map f o ctor_\<Sigma>\<Sigma>6 = ctor_\<Sigma>\<Sigma>6 o map_sum (\<Sigma>6_map (\<Sigma>\<Sigma>6_map f)) f"
unfolding comp_def
unfolding fun_eq_iff
unfolding \<Sigma>\<Sigma>6.ctor_map
unfolding map_pre_\<Sigma>\<Sigma>6_def  (* careful here and elsewhere: data newdatatype unfolds more *)
unfolding id_apply BNF_Comp.id_bnf_comp_def id_def[symmetric] o_id id_o by simp

lemma dtor_\<Sigma>\<Sigma>6_\<Sigma>\<Sigma>6_map:
"dtor_\<Sigma>\<Sigma>6 o \<Sigma>\<Sigma>6_map f = map_sum (\<Sigma>6_map (\<Sigma>\<Sigma>6_map f)) f o dtor_\<Sigma>\<Sigma>6"
using \<Sigma>\<Sigma>6_map_ctor_\<Sigma>\<Sigma>6[of f] \<Sigma>\<Sigma>6.dtor_ctor \<Sigma>\<Sigma>6.ctor_dtor unfolding comp_def fun_eq_iff by metis

lemma dtor_\<Sigma>\<Sigma>6_ctor_\<Sigma>\<Sigma>6: "dtor_\<Sigma>\<Sigma>6 \<circ> ctor_\<Sigma>\<Sigma>6 = id"
unfolding comp_def \<Sigma>\<Sigma>6.dtor_ctor id_def ..

lemma ctor_\<Sigma>\<Sigma>6_dtor_\<Sigma>\<Sigma>6: "ctor_\<Sigma>\<Sigma>6 \<circ> dtor_\<Sigma>\<Sigma>6 = id"
unfolding comp_def \<Sigma>\<Sigma>6.ctor_dtor id_def ..

lemma \<Sigma>\<Sigma>6_rel_inf: "\<Sigma>\<Sigma>6_rel (R \<sqinter> \<Sigma>5) \<le> \<Sigma>\<Sigma>6_rel R \<sqinter> \<Sigma>\<Sigma>6_rel \<Sigma>5"
  apply (rule inf_greatest)
  apply (rule \<Sigma>\<Sigma>6.rel_mono[OF inf_sup_ord(1)])
  apply (rule \<Sigma>\<Sigma>6.rel_mono[OF inf_sup_ord(2)])
  done

lemma \<Sigma>\<Sigma>6_rel_Grp_\<Sigma>\<Sigma>6_map: "\<Sigma>\<Sigma>6_rel (BNF_Def.Grp UNIV f) x y \<longleftrightarrow> \<Sigma>\<Sigma>6_map f x = y"
  unfolding \<Sigma>\<Sigma>6.rel_Grp by (auto simp: Grp_def)

lemma \<Sigma>\<Sigma>6_rel_\<Sigma>\<Sigma>6_map_\<Sigma>\<Sigma>6_map: "\<Sigma>\<Sigma>6_rel R (\<Sigma>\<Sigma>6_map f x) (\<Sigma>\<Sigma>6_map g y) =
  \<Sigma>\<Sigma>6_rel (BNF_Def.vimage2p f g R) x y"
  unfolding \<Sigma>\<Sigma>6.rel_Grp vimage2p_Grp apply (auto simp: \<Sigma>\<Sigma>6.rel_compp \<Sigma>\<Sigma>6.rel_conversep relcompp.simps)
  apply (intro exI conjI)
  apply (rule iffD2[OF \<Sigma>\<Sigma>6_rel_Grp_\<Sigma>\<Sigma>6_map refl])
  apply assumption
  apply (rule iffD2[OF \<Sigma>\<Sigma>6_rel_Grp_\<Sigma>\<Sigma>6_map refl])
  unfolding \<Sigma>\<Sigma>6_rel_Grp_\<Sigma>\<Sigma>6_map
  apply simp
  done


subsection{* @{term \<Sigma>6} extension theorems *}

theorem ext6_commute:
"ext6 s i o \<oo>\<pp>6 = s o \<Sigma>6_map (ext6 s i)"
unfolding ext6_alt \<oo>\<pp>6_def_pointfree o_assoc ctor_fold_\<Sigma>\<Sigma>6_pointfree map_pre_\<Sigma>\<Sigma>6_def
  case_sum_o_map_sum case_sum_o_inj(1) BNF_Comp.id_bnf_comp_def id_def[symmetric] o_id ..

theorem ext6_comp_leaf6:
"ext6 s i o leaf6 = i"
unfolding ext6_alt leaf6_def_pointfree o_assoc ctor_fold_\<Sigma>\<Sigma>6_pointfree map_pre_\<Sigma>\<Sigma>6_def
  case_sum_o_map_sum case_sum_o_inj(2) id_apply BNF_Comp.id_bnf_comp_def id_def[symmetric] o_id ..

theorem ext6_unique:
assumes leaf6: "f o leaf6 = i" and com: "f o \<oo>\<pp>6 = s o \<Sigma>6_map f"
shows "f = ext6 s i"
unfolding ext6_alt
apply (rule \<Sigma>\<Sigma>6.ctor_fold_unique)
apply (rule sum_comp_cases)
unfolding map_pre_\<Sigma>\<Sigma>6_def case_sum_o_map_sum id_apply o_id case_sum_o_inj
  leaf6[unfolded leaf6_def_pointfree o_assoc] com[unfolded \<oo>\<pp>6_def_pointfree o_assoc]
  BNF_Comp.id_bnf_comp_def id_def[symmetric] id_o
by (rule refl)+

subsection{* Customizing @{term \<Sigma>\<Sigma>6} *}

subsection{* Injectiveness, naturality, adjunction *}

theorem leaf6_natural: "\<Sigma>\<Sigma>6_map f o leaf6 = leaf6 o f"
  using leaf6_transfer[of "BNF_Def.Grp UNIV f"]
  unfolding \<Sigma>\<Sigma>6.rel_Grp
  unfolding Grp_def rel_fun_def by auto

lemma \<oo>\<pp>6_natural: "\<oo>\<pp>6 o \<Sigma>6_map (\<Sigma>\<Sigma>6_map f) = \<Sigma>\<Sigma>6_map f o \<oo>\<pp>6"
  using \<oo>\<pp>6_transfer[of "BNF_Def.Grp UNIV f"]
  unfolding \<Sigma>6.rel_Grp \<Sigma>\<Sigma>6.rel_Grp \<Sigma>6_map_def
  unfolding Grp_def rel_fun_def by auto

lemma \<Sigma>\<Sigma>6_map_def2: "\<Sigma>\<Sigma>6_map i = ext6 \<oo>\<pp>6 (leaf6 o i)"
by (rule ext6_unique[OF leaf6_natural \<oo>\<pp>6_natural[symmetric]])

lemma ext6_\<oo>\<pp>6_leaf6: "ext6 \<oo>\<pp>6 leaf6 = id"
apply (rule ext6_unique[symmetric]) unfolding \<Sigma>6.map_id0 o_id id_o by (rule refl)+

lemma ext6_\<Sigma>\<Sigma>6_map:
"ext6 s (j o f) = ext6 s j o \<Sigma>\<Sigma>6_map f"
proof (rule ext6_unique[symmetric])
  show "ext6 s j \<circ> \<Sigma>\<Sigma>6_map f \<circ> leaf6 = j \<circ> f"
  unfolding o_assoc[symmetric] leaf6_natural
  unfolding o_assoc ext6_comp_leaf6 ..
next
  show "ext6 s j \<circ> \<Sigma>\<Sigma>6_map f \<circ> \<oo>\<pp>6 = s \<circ> \<Sigma>6_map (ext6 s j \<circ> \<Sigma>\<Sigma>6_map f)"
  unfolding o_assoc[symmetric] \<oo>\<pp>6_natural[symmetric]
  unfolding o_assoc ext6_commute
  unfolding o_assoc[symmetric] \<Sigma>6.map_comp0 ..
qed

lemma ext6_\<Sigma>6_map:
assumes "t o \<Sigma>6_map f = f o s"
shows "ext6 t (f o i) = f o ext6 s i"
proof (rule ext6_unique[symmetric])
  show "f \<circ> ext6 s i \<circ> leaf6 = f o i"
  unfolding o_assoc[symmetric] ext6_comp_leaf6 ..
next
  show "f \<circ> ext6 s i \<circ> \<oo>\<pp>6 = t \<circ> \<Sigma>6_map (f \<circ> ext6 s i)"
  unfolding \<Sigma>6.map_comp0 o_assoc assms
  unfolding o_assoc[symmetric] ext6_commute[symmetric] ..
qed


subsection{* Monadic laws *}

lemma flat6_commute: "\<oo>\<pp>6 \<circ> \<Sigma>6_map flat6 = flat6 \<circ> \<oo>\<pp>6"
unfolding flat6_def ext6_commute ..

(* The 2 identity laws*)
theorem flat6_leaf6: "flat6 o leaf6 = id"
unfolding flat6_def ext6_comp_leaf6 ..

theorem leaf6_flat6: "flat6 o \<Sigma>\<Sigma>6_map leaf6 = id"
unfolding flat6_def ext6_\<Sigma>\<Sigma>6_map[symmetric] id_o ext6_\<oo>\<pp>6_leaf6 ..

theorem flat6_natural: "flat6 o \<Sigma>\<Sigma>6_map (\<Sigma>\<Sigma>6_map i) = \<Sigma>\<Sigma>6_map i o flat6"
  using flat6_transfer[of "BNF_Def.Grp UNIV i"]
  unfolding prod.rel_Grp \<Sigma>\<Sigma>6.rel_Grp
  unfolding Grp_def rel_fun_def by auto

(* Associativity *)
theorem flat6_assoc: "flat6 o \<Sigma>\<Sigma>6_map flat6 = flat6 o flat6"
unfolding flat6_def unfolding ext6_\<Sigma>\<Sigma>6_map[symmetric] id_o
proof(rule ext6_unique[symmetric], unfold flat6_def[symmetric])
  show "flat6 \<circ> flat6 \<circ> leaf6 = flat6"
  unfolding o_assoc[symmetric] flat6_leaf6 o_id ..
next
  show "flat6 \<circ> flat6 \<circ> \<oo>\<pp>6 = \<oo>\<pp>6 \<circ> \<Sigma>6_map (flat6 \<circ> flat6)"
  unfolding flat6_def unfolding o_assoc[symmetric] ext6_commute
  unfolding flat6_def[symmetric]
  unfolding \<Sigma>6.map_comp0 o_assoc unfolding flat6_commute ..
qed

definition K6_as_\<Sigma>\<Sigma>6 :: "'a K6 \<Rightarrow> 'a \<Sigma>\<Sigma>6" where
"K6_as_\<Sigma>\<Sigma>6 \<equiv> \<oo>\<pp>6 o \<Sigma>6_map leaf6 o Abs_\<Sigma>6 o Inr"

lemma K6_as_\<Sigma>\<Sigma>6_transfer[transfer_rule]:
  "(K6_rel R ===> \<Sigma>\<Sigma>6_rel R) K6_as_\<Sigma>\<Sigma>6 K6_as_\<Sigma>\<Sigma>6"
  unfolding K6_as_\<Sigma>\<Sigma>6_def by transfer_prover

lemma K6_as_\<Sigma>\<Sigma>6_natural:
"K6_as_\<Sigma>\<Sigma>6 o K6_map f = \<Sigma>\<Sigma>6_map f o K6_as_\<Sigma>\<Sigma>6"
  using K6_as_\<Sigma>\<Sigma>6_transfer[of "BNF_Def.Grp UNIV f"]
  unfolding K6.rel_Grp \<Sigma>\<Sigma>6.rel_Grp
  unfolding Grp_def rel_fun_def by auto

end