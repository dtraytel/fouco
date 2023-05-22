header {* The initial algll operation is precisely (the copy of) ctor_J *}

theory More_Corec_Upto_base
imports Corec_Upto_base
begin

lemma alg\<Lambda>_base: "alg\<Lambda>_base o Abs_\<Sigma>_base = ctor_J"
unfolding ctor_J_def apply(rule J.dtor_unfold_unique)
unfolding o_assoc dtor_J_alg\<Lambda>_base
unfolding alg\<Lambda>_base_def unfolding o_assoc[symmetric] Abs_\<Sigma>_base_natural
unfolding F_map_comp[symmetric] o_assoc
unfolding \<Lambda>_base_def
unfolding o_assoc[symmetric] snd_comp_map_prod
unfolding o_assoc \<Sigma>_base.map_comp0[symmetric]
apply(rule sym)
apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric],
            subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric],
            subst o_assoc[symmetric])
unfolding o_id Abs_\<Sigma>_base_natural o_assoc Rep_\<Sigma>_base_o_Abs_\<Sigma>_base
unfolding F_map_comp[symmetric] o_assoc[symmetric] snd_convol
unfolding o_assoc
apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
unfolding o_assoc ..

(* This should be the default evaluator for eval_base on the term algebra: *)

theorem eval_base_\<oo>\<pp>_base_ctor_J:
"eval_base (\<oo>\<pp>_base t) = ctor_J (Rep_\<Sigma>_base (\<Sigma>_base_map eval_base t))"
unfolding eval_base_\<oo>\<pp>_base alg\<Lambda>_base[symmetric] o_apply Rep_\<Sigma>_base_inverse ..


subsection{* Up-to corecursor with guard not necessarily at the top *}

definition ff_base :: "'a F \<Rightarrow> 'a \<Sigma>_base" where "ff_base \<equiv> Abs_\<Sigma>_base" (* just for bootstrapping *)

lemma alg\<Lambda>_base_ff_base: "alg\<Lambda>_base \<circ> ff_base = ctor_J"
unfolding ff_base_def o_assoc alg\<Lambda>_base ..

lemma ff_base_transfer[transfer_rule]: "(F_rel R ===> \<Sigma>_base_rel R) ff_base ff_base"
unfolding ff_base_def by transfer_prover

lemma ff_base_natural: "\<Sigma>_base_map f o ff_base = ff_base o F_map f"
using ff_base_transfer[of "BNF_Def.Grp UNIV f"]
unfolding \<Sigma>_base.rel_Grp F_rel_Grp
unfolding Grp_def rel_fun_def by auto

definition gg_base :: "'a \<Sigma>\<Sigma>_base F \<Rightarrow> 'a \<Sigma>\<Sigma>_base" where
"gg_base \<equiv> \<oo>\<pp>_base o ff_base"

lemma eval_base_gg_base: "eval_base o gg_base = ctor_J o F_map eval_base"
unfolding o_assoc gg_base_def eval_base_comp_\<oo>\<pp>_base alg\<Lambda>_base[symmetric]
unfolding o_assoc[symmetric] unfolding ff_base_def Abs_\<Sigma>_base_natural
..

lemma gg_base_transfer[transfer_rule]: "(F_rel (\<Sigma>\<Sigma>_base_rel R) ===> \<Sigma>\<Sigma>_base_rel R) gg_base gg_base"
unfolding gg_base_def by transfer_prover

lemma gg_base_natural: "\<Sigma>\<Sigma>_base_map f o gg_base = gg_base o F_map (\<Sigma>\<Sigma>_base_map f)"
using gg_base_transfer[of "BNF_Def.Grp UNIV f"]
unfolding \<Sigma>\<Sigma>_base.rel_Grp F_rel_Grp
unfolding Grp_def rel_fun_def by auto

definition unfoldUU_base :: "('a \<Rightarrow> 'a \<Sigma>\<Sigma>_base F \<Sigma>\<Sigma>_base) \<Rightarrow> 'a \<Rightarrow> J" where
"unfoldUU_base s \<equiv> unfoldU_base (F_map flat_base o dd_base o \<Sigma>\<Sigma>_base_map <gg_base, id> o s)"

theorem unfoldUU_base:
"unfoldUU_base s =
 eval_base o \<Sigma>\<Sigma>_base_map (ctor_J o F_map eval_base o F_map (\<Sigma>\<Sigma>_base_map (unfoldUU_base s))) o s"
unfolding unfoldUU_base_def apply(subst unfoldU_base_ctor_J_pointfree[symmetric]) unfolding unfoldUU_base_def[symmetric]
unfolding extdd_base_def F_map_comp[symmetric] o_assoc
apply(subst o_assoc[symmetric]) unfolding F_map_comp[symmetric]
apply(subst o_assoc[symmetric]) unfolding flat_base_natural[symmetric]
apply(subst o_assoc) unfolding eval_base_flat_base
unfolding F_map_comp
apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
unfolding dd_base_natural[symmetric]
unfolding o_assoc apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
unfolding dd_base_natural[symmetric]
unfolding o_assoc[symmetric] \<Sigma>\<Sigma>_base.map_comp0[symmetric]
unfolding o_assoc eval_base_gg_base unfolding \<Sigma>\<Sigma>_base.map_comp0 o_assoc
apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric],
      subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
unfolding \<Sigma>\<Sigma>_base.map_comp0[symmetric]
apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
unfolding \<Sigma>\<Sigma>_base.map_comp0[symmetric] map_prod.comp map_prod_o_convol o_id F_map_comp[symmetric]
apply(rule sym) unfolding o_assoc
apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
unfolding \<Sigma>\<Sigma>_base.map_comp0[symmetric] F_map_comp[symmetric] o_assoc[symmetric] gg_base_natural
unfolding o_assoc eval_base_gg_base
apply(rule sym)
apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
unfolding F_map_comp[symmetric] convol_comp_id2 convol_ctor_J_dtor_J
          \<Sigma>\<Sigma>_base.map_comp0 o_assoc eval_base ctor_dtor_J_pointfree id_o ..

theorem unfoldUU_base_unique:
assumes f: "f = eval_base o \<Sigma>\<Sigma>_base_map (ctor_J o F_map eval_base o F_map (\<Sigma>\<Sigma>_base_map f)) o s"
shows "f = unfoldUU_base s"
unfolding unfoldUU_base_def apply(rule unfoldU_base_unique)
apply(rule sym) apply(subst f) unfolding extdd_base_def
unfolding o_assoc
apply(subst eval_base_def) unfolding dtor_unfold_J_pointfree apply(subst eval_base_def[symmetric])
unfolding o_assoc
apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
unfolding o_assoc \<Sigma>\<Sigma>_base.map_comp0[symmetric]  convol_o id_o dtor_J_ctor_pointfree F_map_comp[symmetric]
unfolding o_assoc[symmetric] flat_base_natural[symmetric]
unfolding o_assoc eval_base_flat_base unfolding o_assoc[symmetric] unfolding F_map_comp
apply(rule sym) apply(subst F_map_comp[symmetric], subst \<Sigma>\<Sigma>_base.map_comp0[symmetric])
unfolding o_assoc apply(subst o_assoc[symmetric])
unfolding dd_base_natural[symmetric]
unfolding o_assoc[symmetric] \<Sigma>\<Sigma>_base.map_comp0[symmetric] map_prod_o_convol o_id
unfolding o_assoc[symmetric] gg_base_natural
unfolding o_assoc eval_base_gg_base F_map_comp ..

(* corecursion: *)
definition corecUU_base :: "('a \<Rightarrow> (J + 'a) \<Sigma>\<Sigma>_base F \<Sigma>\<Sigma>_base) \<Rightarrow> 'a \<Rightarrow> J" where
"corecUU_base s \<equiv>
 unfoldUU_base (case_sum (leaf_base o dd_base o leaf_base o <Inl , F_map Inl \<circ> dtor_J>) s) o Inr"

lemma unfoldUU_base_Inl:
"unfoldUU_base (case_sum (leaf_base \<circ> dd_base \<circ> leaf_base \<circ> <Inl , F_map Inl \<circ> dtor_J>) s) \<circ> Inl = id"
(is "?L = ?R")
proof-
  have "?L = unfoldUU_base (leaf_base o dd_base o leaf_base o <id, dtor_J>)"
  apply(rule unfoldUU_base_unique)
  apply(subst unfoldUU_base)
  unfolding o_assoc[symmetric] case_sum_o_inj snd_convol
  unfolding F_map_comp \<Sigma>\<Sigma>_base.map_comp0
  unfolding o_assoc
  apply(rule sym)
  unfolding o_assoc
  apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric],
              subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
  apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric],
              subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric],
              subst o_assoc[symmetric])
  unfolding leaf_base_natural apply(subst o_assoc[symmetric])
  apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric],
              subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
  unfolding dd_base_natural[symmetric]
  apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric],
              subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
  apply(subst o_assoc[symmetric], subst o_assoc[symmetric])
  unfolding leaf_base_natural
  unfolding o_assoc[symmetric] map_prod_o_convol o_id ..
  also have "... = ?R"
  apply(rule sym, rule unfoldUU_base_unique)
  unfolding \<Sigma>\<Sigma>_base.map_id0 F_map_id o_id
  unfolding o_assoc
  apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric],
              subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
  unfolding dd_base_leaf_base
  unfolding o_assoc[symmetric] snd_convol
  unfolding o_assoc
  apply(subst o_assoc[symmetric])
  unfolding leaf_base_natural unfolding o_assoc eval_base_leaf_base id_o
  apply(subst o_assoc[symmetric])
  unfolding F_map_comp[symmetric] eval_base_leaf_base F_map_id o_id ctor_dtor_J_pointfree ..
  finally show ?thesis .
qed

theorem corecUU_base_pointfree:
"corecUU_base s =
 eval_base o \<Sigma>\<Sigma>_base_map (ctor_J o F_map eval_base o F_map (\<Sigma>\<Sigma>_base_map (case_sum id (corecUU_base s)))) o s"
unfolding corecUU_base_def
apply(subst unfoldUU_base)
unfolding o_assoc[symmetric] unfolding case_sum_o_inj
apply(subst unfoldUU_base_Inl[symmetric, of s])
unfolding o_assoc case_sum_Inl_Inr_L extdd_base_def ..

theorem corecUU_base_unique:
  assumes f: "f = eval_base o \<Sigma>\<Sigma>_base_map (ctor_J o F_map eval_base o F_map (\<Sigma>\<Sigma>_base_map (case_sum id f))) o s"
  shows "f = corecUU_base s"
  unfolding corecUU_base_def
  apply(rule eq_o_InrI[OF unfoldUU_base_Inl unfoldUU_base_unique])
  apply (subst f)
  apply (auto simp: fun_eq_iff eval_base_leaf_base' pre_J.map_comp o_eq_dest[OF dd_base_leaf_base] convol_def
    leaf_base_natural o_assoc case_sum_o_inj(1) eval_base_leaf_base pre_J.map_id J.ctor_dtor split: sum.splits)
  done

theorem corecUU_base:
"corecUU_base s a =
 eval_base (\<Sigma>\<Sigma>_base_map (ctor_J o F_map eval_base o F_map (\<Sigma>\<Sigma>_base_map (case_sum id (corecUU_base s)))) (s a))"
using corecUU_base_pointfree unfolding o_def fun_eq_iff by(rule allE)


end