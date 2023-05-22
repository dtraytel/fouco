header {* More on corecursion and coinduction up to *}

theory More_Corec_Upto_step
imports Corec_Upto_step
begin


subsection{* A natural-transformation-based version of the up-to corecursion principle *}

definition alg\<rho>_step :: "J K_step \<Rightarrow> J" where "alg\<rho>_step \<equiv> eval_step o K_step_as_\<Sigma>\<Sigma>_step"

lemma dd_step_K_step_as_\<Sigma>\<Sigma>_step:
"dd_step o K_step_as_\<Sigma>\<Sigma>_step = \<rho>_step"
unfolding K_step_as_\<Sigma>\<Sigma>_step_def dd_step_def
unfolding o_assoc apply(subst o_assoc[symmetric])
unfolding ddd_step_\<oo>\<pp>_step unfolding o_assoc snd_convol
unfolding o_assoc apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
unfolding \<Sigma>_step.map_comp0[symmetric] ddd_step_leaf_step \<Lambda>_step_natural
unfolding o_assoc F_map_comp[symmetric] leaf_step_flat_step F_map_id id_o \<Lambda>_step_Inr ..

lemma alg\<rho>_step: "dtor_J o alg\<rho>_step = F_map eval_step o \<rho>_step o K_step_map <id, dtor_J>"
unfolding dd_step_K_step_as_\<Sigma>\<Sigma>_step[symmetric] o_assoc
unfolding o_assoc[symmetric] K_step_as_\<Sigma>\<Sigma>_step_natural
unfolding o_assoc eval_step alg\<rho>_step_def ..

lemma flat_step_embL_step: "flat_step o embL_step o \<Sigma>\<Sigma>_base_map embL_step = embL_step o flat_base" (is "?L = ?R")
proof-
  have "?L = ext_base (\<oo>\<pp>_step o Abs_\<Sigma>_step o Inl) embL_step"
  proof(rule ext_base_unique)
    show "flat_step \<circ> embL_step \<circ> \<Sigma>\<Sigma>_base_map embL_step \<circ> leaf_base = embL_step"
    unfolding o_assoc[symmetric] unfolding leaf_base_natural
    unfolding o_assoc apply(subst o_assoc[symmetric])
    apply(subst embL_step_def) unfolding ext_base_comp_leaf_base flat_step_leaf_step id_o ..
  next
    show "flat_step \<circ> embL_step \<circ> \<Sigma>\<Sigma>_base_map embL_step \<circ> \<oo>\<pp>_base = \<oo>\<pp>_step \<circ> Abs_\<Sigma>_step \<circ> Inl \<circ> \<Sigma>_base_map (flat_step \<circ> embL_step \<circ> \<Sigma>\<Sigma>_base_map embL_step)"
    apply(subst o_assoc[symmetric]) unfolding embL_step_natural
    unfolding o_assoc apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric],
                            subst o_assoc[symmetric])
    unfolding embL_step_def unfolding ext_base_commute unfolding embL_step_def[symmetric]
    unfolding o_assoc apply(subst o_assoc[symmetric])
    unfolding \<oo>\<pp>_step_natural[symmetric]
    unfolding o_assoc apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
    unfolding map_sum_Inl Abs_\<Sigma>_step_natural
    unfolding o_assoc[symmetric] map_sum_Inl \<Sigma>_base.map_comp0[symmetric] embL_step_natural[symmetric]
    apply(rule sym) apply(subst \<Sigma>_base.map_comp0) unfolding o_assoc
    unfolding flat_step_def unfolding ext_step_commute
    apply(rule sym) apply(subst o_assoc[symmetric])
    unfolding Abs_\<Sigma>_step_natural unfolding o_assoc[symmetric] map_sum_Inl \<oo>\<pp>_step_natural[symmetric] ..
  qed
  also have "... = ?R"
  proof(rule sym, rule ext_base_unique)
    show "embL_step \<circ> flat_base \<circ> leaf_base = embL_step"
    unfolding o_assoc[symmetric] flat_base_leaf_base o_id ..
  next
    show "embL_step \<circ> flat_base \<circ> \<oo>\<pp>_base = \<oo>\<pp>_step \<circ> Abs_\<Sigma>_step \<circ> Inl \<circ> \<Sigma>_base_map (embL_step \<circ> flat_base)"
    unfolding flat_base_def o_assoc[symmetric] ext_base_commute
    unfolding o_assoc
    apply(subst embL_step_def) unfolding ext_base_commute apply(subst embL_step_def[symmetric])
    unfolding \<Sigma>_base.map_comp0 o_assoc ..
  qed
  finally show ?thesis .
qed

lemma ddd_step_embL_step: "ddd_step \<circ> embL_step = (embL_step ** F_map embL_step) \<circ> ddd_base" (is "?L = ?R")
proof-
  have "?L = ext_base <\<oo>\<pp>_step o Abs_\<Sigma>_step o Inl o \<Sigma>_base_map fst, F_map (flat_step o embL_step) o \<Lambda>_base> (leaf_step ** F_map leaf_step)"
  proof(rule ext_base_unique)
    show "ddd_step \<circ> embL_step \<circ> leaf_base = leaf_step ** F_map leaf_step"
    apply(rule fst_snd_cong)
    unfolding fst_comp_map_prod snd_comp_map_prod
    unfolding  embL_step_def
    apply (subst (3) o_assoc[symmetric]) defer apply (subst (3) o_assoc[symmetric])
    unfolding ext_base_comp_leaf_base
    unfolding ddd_step_def ext_step_comp_leaf_step fst_comp_map_prod snd_comp_map_prod by(rule refl, rule refl)
  next
    show "ddd_step \<circ> embL_step \<circ> \<oo>\<pp>_base =
          <\<oo>\<pp>_step \<circ> Abs_\<Sigma>_step \<circ> Inl \<circ> \<Sigma>_base_map fst , F_map (flat_step \<circ> embL_step) \<circ> \<Lambda>_base> \<circ> \<Sigma>_base_map (ddd_step \<circ> embL_step)" (is "?A = ?B")
    proof(rule fst_snd_cong)
      show "fst o ?A = fst o ?B"
      unfolding o_assoc fst_convol unfolding o_assoc[symmetric] \<Sigma>_base.map_comp0[symmetric]
      unfolding o_assoc
      apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
      apply(subst embL_step_def) unfolding ext_base_commute apply(subst embL_step_def[symmetric])
      unfolding o_assoc apply(subst o_assoc[symmetric])
      apply(subst ddd_step_def) unfolding ext_step_commute apply(subst ddd_step_def[symmetric])
      unfolding o_assoc fst_convol
      apply(subst o_assoc[symmetric]) unfolding \<Sigma>_step.map_comp0[symmetric]
      apply(subst o_assoc[symmetric]) unfolding Abs_\<Sigma>_step_natural map_sum_Inl o_assoc[symmetric]
      unfolding \<Sigma>_base.map_comp0[symmetric] o_assoc ..
    next
      show "snd o ?A = snd o ?B"
      unfolding o_assoc snd_convol unfolding o_assoc[symmetric]
      apply(subst embL_step_def) unfolding ext_base_commute apply(subst embL_step_def[symmetric])
      unfolding o_assoc apply(subst o_assoc[symmetric], subst o_assoc[symmetric])
      apply(subst ddd_step_def) unfolding ext_step_commute apply(subst ddd_step_def[symmetric])
      unfolding o_assoc snd_convol
      unfolding o_assoc apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
      unfolding Abs_\<Sigma>_step_natural map_sum_Inl o_assoc[symmetric]
      unfolding o_assoc apply(subst o_assoc[symmetric], subst o_assoc[symmetric])
      unfolding \<Lambda>_step_Inl unfolding \<Sigma>_base.map_comp0 F_map_comp o_assoc ..
    qed
  qed
  also have "... = ?R"
  proof(rule sym, rule ext_base_unique)
    show "(embL_step ** F_map embL_step) \<circ> ddd_base \<circ> leaf_base = leaf_step ** F_map leaf_step"
    unfolding o_assoc apply(subst o_assoc[symmetric])
    apply(subst ddd_base_def) unfolding ext_base_comp_leaf_base
    unfolding map_prod.comp unfolding F_map_comp[symmetric]
    apply(subst embL_step_def, subst embL_step_def) unfolding ext_base_comp_leaf_base ..
  next
    show "embL_step ** F_map embL_step \<circ> ddd_base \<circ> \<oo>\<pp>_base =
          <\<oo>\<pp>_step \<circ> Abs_\<Sigma>_step \<circ> Inl \<circ> \<Sigma>_base_map fst , F_map (flat_step \<circ> embL_step) \<circ> \<Lambda>_base> \<circ> \<Sigma>_base_map (embL_step ** F_map embL_step \<circ> ddd_base)"
    (is "?A = ?B") proof(rule fst_snd_cong)
      show "fst o ?A = fst o ?B"
      unfolding o_assoc fst_convol fst_comp_map_prod
      unfolding o_assoc[symmetric] \<Sigma>_base.map_comp0[symmetric] unfolding o_assoc unfolding fst_comp_map_prod
      unfolding o_assoc apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
      apply(subst ddd_base_def) unfolding ext_base_commute apply(subst ddd_base_def[symmetric])
      unfolding o_assoc fst_convol
      apply(subst embL_step_def) unfolding ext_base_commute apply(subst embL_step_def[symmetric])
      unfolding \<Sigma>_base.map_comp0 o_assoc ..
    next
      show "snd o ?A = snd o ?B"
      unfolding o_assoc snd_convol snd_comp_map_prod
      unfolding o_assoc apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
      apply(subst ddd_base_def) unfolding ext_base_commute apply(subst ddd_base_def[symmetric])
      unfolding o_assoc apply(subst o_assoc[symmetric]) unfolding snd_convol
      unfolding o_assoc F_map_comp[symmetric]
      unfolding flat_step_embL_step[symmetric]
      unfolding F_map_comp
      unfolding o_assoc apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
      unfolding \<Lambda>_base_natural[symmetric]
      unfolding o_assoc \<Sigma>_base.map_comp0 ..
    qed
  qed
  finally show ?thesis .
qed

lemma dd_step_embL_step: "dd_step \<circ> embL_step = F_map embL_step \<circ> dd_base"
unfolding dd_step_def dd_base_def o_assoc[symmetric] ddd_step_embL_step by auto

lemma F_map_embL_step_\<Sigma>\<Sigma>_base_map:
"F_map embL_step \<circ> dd_base \<circ> \<Sigma>\<Sigma>_base_map <id , dtor_J> =
 dd_step \<circ> \<Sigma>\<Sigma>_step_map <id , dtor_J> \<circ> embL_step"
unfolding o_assoc[symmetric] unfolding embL_step_natural[symmetric]
unfolding o_assoc dd_step_embL_step ..

lemma eval_step_embL_step: "eval_step o embL_step = eval_base"
unfolding eval_base_def apply(rule J.dtor_unfold_unique)
unfolding eval_step_def unfolding o_assoc
unfolding dtor_unfold_J_pointfree
unfolding F_map_comp
apply(subst o_assoc[symmetric], subst o_assoc[symmetric])
unfolding F_map_embL_step_\<Sigma>\<Sigma>_base_map o_assoc ..

theorem alg\<Lambda>_step_alg\<Lambda>_base_alg\<rho>_step:
"alg\<Lambda>_step o Abs_\<Sigma>_step = case_sum alg\<Lambda>_base alg\<rho>_step" (is "?L = ?R")
proof(rule sum_comp_cases)
  show "?L o Inl = ?R o Inl"
  unfolding case_sum_o_inj apply(subst dtor_J_o_inj[symmetric])
  unfolding o_assoc dtor_J_alg\<Lambda>_step unfolding Abs_\<Sigma>_step_natural o_assoc[symmetric] map_sum_Inl
  unfolding o_assoc apply(subst o_assoc[symmetric], subst o_assoc[symmetric]) unfolding \<Lambda>_step_Inl
  unfolding o_assoc F_map_comp[symmetric] eval_step_embL_step dtor_J_alg\<Lambda>_base ..
next
  show "?L o Inr = ?R o Inr"
  unfolding alg\<rho>_step_def case_sum_o_inj alg\<Lambda>_step_def K_step_as_\<Sigma>\<Sigma>_step_def o_assoc ..
qed

theorem alg\<Lambda>_step_Inl: "alg\<Lambda>_step (Abs_\<Sigma>_step (Inl x)) = alg\<Lambda>_base x" (is "?L = ?R")
unfolding o_eq_dest_lhs[OF alg\<Lambda>_step_alg\<Lambda>_base_alg\<rho>_step] by simp

lemma alg\<Lambda>_step_Inl_pointfree: "alg\<Lambda>_step o Abs_\<Sigma>_step o Inl = alg\<Lambda>_base"
unfolding o_def fun_eq_iff alg\<Lambda>_step_Inl by simp

theorem alg\<Lambda>_step_Inr: "alg\<Lambda>_step (Abs_\<Sigma>_step (Inr x)) = alg\<rho>_step x" (is "?L = ?R")
unfolding o_eq_dest_lhs[OF alg\<Lambda>_step_alg\<Lambda>_base_alg\<rho>_step] by simp



subsection{* Up-to corecursor with guard not necessarily at the top *}

definition ff_step :: "'a F \<Rightarrow> 'a \<Sigma>_step" where "ff_step \<equiv> Abs_\<Sigma>_step o Inl o ff_base"

lemma alg\<Lambda>_step_ff_step: "alg\<Lambda>_step \<circ> ff_step = ctor_J"
unfolding ff_step_def o_assoc alg\<Lambda>_step_Inl_pointfree alg\<Lambda>_base_ff_base ..

lemma ff_step_transfer[transfer_rule]: "(F_rel R ===> \<Sigma>_step_rel R) ff_step ff_step"
unfolding ff_step_def by transfer_prover

lemma ff_step_natural: "\<Sigma>_step_map f o ff_step = ff_step o F_map f"
using ff_step_transfer[of "BNF_Def.Grp UNIV f"]
unfolding \<Sigma>_step.rel_Grp F_rel_Grp
unfolding Grp_def rel_fun_def by auto

definition gg_step :: "'a \<Sigma>\<Sigma>_step F \<Rightarrow> 'a \<Sigma>\<Sigma>_step" where
"gg_step \<equiv> \<oo>\<pp>_step o ff_step"

lemma eval_step_gg_step: "eval_step o gg_step = ctor_J o F_map eval_step"
unfolding gg_step_def
unfolding o_assoc unfolding eval_step_comp_\<oo>\<pp>_step
unfolding o_assoc[symmetric] ff_step_natural
unfolding o_assoc alg\<Lambda>_step_ff_step ..

lemma gg_step_transfer[transfer_rule]: "(F_rel (\<Sigma>\<Sigma>_step_rel R) ===> \<Sigma>\<Sigma>_step_rel R) gg_step gg_step"
unfolding gg_step_def by transfer_prover

lemma gg_step_natural: "\<Sigma>\<Sigma>_step_map f o gg_step = gg_step o F_map (\<Sigma>\<Sigma>_step_map f)"
using gg_step_transfer[of "BNF_Def.Grp UNIV f"]
unfolding \<Sigma>\<Sigma>_step.rel_Grp F_rel_Grp
unfolding Grp_def rel_fun_def by auto

definition unfoldUU_step :: "('a \<Rightarrow> 'a \<Sigma>\<Sigma>_step F \<Sigma>\<Sigma>_step) \<Rightarrow> 'a \<Rightarrow> J" where
"unfoldUU_step s \<equiv> unfoldU_step (F_map flat_step o dd_step o \<Sigma>\<Sigma>_step_map <gg_step, id> o s)"

theorem unfoldUU_step:
"unfoldUU_step s =
 eval_step o \<Sigma>\<Sigma>_step_map (ctor_J o F_map eval_step o F_map (\<Sigma>\<Sigma>_step_map (unfoldUU_step s))) o s"
unfolding unfoldUU_step_def apply(subst unfoldU_step_ctor_J_pointfree[symmetric]) unfolding unfoldUU_step_def[symmetric]
unfolding extdd_step_def F_map_comp[symmetric] o_assoc
apply(subst o_assoc[symmetric]) unfolding F_map_comp[symmetric]
apply(subst o_assoc[symmetric]) unfolding flat_step_natural[symmetric]
apply(subst o_assoc) unfolding eval_step_flat_step
unfolding F_map_comp
apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
unfolding dd_step_natural[symmetric]
unfolding o_assoc apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
unfolding dd_step_natural[symmetric]
unfolding o_assoc[symmetric] \<Sigma>\<Sigma>_step.map_comp0[symmetric]
unfolding o_assoc eval_step_gg_step unfolding \<Sigma>\<Sigma>_step.map_comp0 o_assoc
apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric],
      subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
unfolding \<Sigma>\<Sigma>_step.map_comp0[symmetric]
apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
unfolding \<Sigma>\<Sigma>_step.map_comp0[symmetric] map_prod.comp map_prod_o_convol o_id F_map_comp[symmetric]
apply(rule sym) unfolding o_assoc
apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
unfolding \<Sigma>\<Sigma>_step.map_comp0[symmetric] F_map_comp[symmetric] o_assoc[symmetric] gg_step_natural
unfolding o_assoc eval_step_gg_step
apply(rule sym)
apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
unfolding F_map_comp[symmetric] convol_comp_id2 convol_ctor_J_dtor_J
          \<Sigma>\<Sigma>_step.map_comp0 o_assoc eval_step ctor_dtor_J_pointfree id_o ..

theorem unfoldUU_step_unique:
assumes f: "f = eval_step o \<Sigma>\<Sigma>_step_map (ctor_J o F_map eval_step o F_map (\<Sigma>\<Sigma>_step_map f)) o s"
shows "f = unfoldUU_step s"
unfolding unfoldUU_step_def apply(rule unfoldU_step_unique)
apply(rule sym) apply(subst f) unfolding extdd_step_def
unfolding o_assoc
apply(subst eval_step_def) unfolding dtor_unfold_J_pointfree apply(subst eval_step_def[symmetric])
unfolding o_assoc
apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
unfolding o_assoc \<Sigma>\<Sigma>_step.map_comp0[symmetric]  convol_o id_o dtor_J_ctor_pointfree F_map_comp[symmetric]
unfolding o_assoc[symmetric] flat_step_natural[symmetric]
unfolding o_assoc eval_step_flat_step unfolding o_assoc[symmetric] unfolding F_map_comp
apply(rule sym) apply(subst F_map_comp[symmetric], subst \<Sigma>\<Sigma>_step.map_comp0[symmetric])
unfolding o_assoc apply(subst o_assoc[symmetric])
unfolding dd_step_natural[symmetric]
unfolding o_assoc[symmetric] \<Sigma>\<Sigma>_step.map_comp0[symmetric] map_prod_o_convol o_id
unfolding o_assoc[symmetric] gg_step_natural
unfolding o_assoc eval_step_gg_step F_map_comp ..

(* corecursion: *)
definition corecUU_step :: "('a \<Rightarrow> (J + 'a) \<Sigma>\<Sigma>_step F \<Sigma>\<Sigma>_step) \<Rightarrow> 'a \<Rightarrow> J" where
"corecUU_step s \<equiv>
 unfoldUU_step (case_sum (leaf_step o dd_step o leaf_step o <Inl , F_map Inl \<circ> dtor_J>) s) o Inr"

lemma unfoldUU_step_Inl:
"unfoldUU_step (case_sum (leaf_step \<circ> dd_step \<circ> leaf_step \<circ> <Inl , F_map Inl \<circ> dtor_J>) s) \<circ> Inl = id"
(is "?L = ?R")
proof-
  have "?L = unfoldUU_step (leaf_step o dd_step o leaf_step o <id, dtor_J>)"
  apply(rule unfoldUU_step_unique)
  apply(subst unfoldUU_step)
  unfolding o_assoc[symmetric] case_sum_o_inj snd_convol
  unfolding F_map_comp \<Sigma>\<Sigma>_step.map_comp0
  unfolding o_assoc
  apply(rule sym)
  unfolding o_assoc
  apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric],
              subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
  apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric],
              subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric],
              subst o_assoc[symmetric])
  unfolding leaf_step_natural apply(subst o_assoc[symmetric])
  apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric],
              subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
  unfolding dd_step_natural[symmetric]
  apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric],
              subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
  apply(subst o_assoc[symmetric], subst o_assoc[symmetric])
  unfolding leaf_step_natural
  unfolding o_assoc[symmetric] map_prod_o_convol o_id ..
  also have "... = ?R"
  apply(rule sym, rule unfoldUU_step_unique)
  unfolding \<Sigma>\<Sigma>_step.map_id0 F_map_id o_id
  unfolding o_assoc
  apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric],
              subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
  unfolding dd_step_leaf_step
  unfolding o_assoc[symmetric] snd_convol
  unfolding o_assoc
  apply(subst o_assoc[symmetric])
  unfolding leaf_step_natural unfolding o_assoc eval_step_leaf_step id_o
  apply(subst o_assoc[symmetric])
  unfolding F_map_comp[symmetric] eval_step_leaf_step F_map_id o_id ctor_dtor_J_pointfree ..
  finally show ?thesis .
qed

theorem corecUU_step_pointfree:
"corecUU_step s =
 eval_step o \<Sigma>\<Sigma>_step_map (ctor_J o F_map eval_step o F_map (\<Sigma>\<Sigma>_step_map (case_sum id (corecUU_step s)))) o s"
unfolding corecUU_step_def
apply(subst unfoldUU_step)
unfolding o_assoc[symmetric] unfolding case_sum_o_inj
apply(subst unfoldUU_step_Inl[symmetric, of s])
unfolding o_assoc case_sum_Inl_Inr_L extdd_step_def ..

theorem corecUU_step_unique:
  assumes f: "f = eval_step o \<Sigma>\<Sigma>_step_map (ctor_J o F_map eval_step o F_map (\<Sigma>\<Sigma>_step_map (case_sum id f))) o s"
  shows "f = corecUU_step s"
  unfolding corecUU_step_def
  apply(rule eq_o_InrI[OF unfoldUU_step_Inl unfoldUU_step_unique])
  apply (subst f)
  apply (auto simp: fun_eq_iff eval_step_leaf_step' pre_J.map_comp o_eq_dest[OF dd_step_leaf_step] convol_def
    leaf_step_natural o_assoc case_sum_o_inj(1) eval_step_leaf_step pre_J.map_id J.ctor_dtor split: sum.splits)
  done

theorem corecUU_step:
"corecUU_step s a =
 eval_step (\<Sigma>\<Sigma>_step_map (ctor_J o F_map eval_step o F_map (\<Sigma>\<Sigma>_step_map (case_sum id (corecUU_step s)))) (s a))"
using corecUU_step_pointfree unfolding o_def fun_eq_iff by(rule allE)

end