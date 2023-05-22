header {* More on corecursion and coinduction up to *}

theory Binary_Tree_More_Corec_Upto1
imports Binary_Tree_Corec_Upto1
begin


subsection{* A natural-transformation-based version of the up-to corecursion principle *}

definition alg\<rho>1 :: "J K1 \<Rightarrow> J" where "alg\<rho>1 \<equiv> eval1 o K1_as_\<Sigma>\<Sigma>1"

lemma dd1_K1_as_\<Sigma>\<Sigma>1:
"dd1 o K1_as_\<Sigma>\<Sigma>1 = \<rho>1"
unfolding K1_as_\<Sigma>\<Sigma>1_def dd1_def
unfolding o_assoc apply(subst o_assoc[symmetric])
unfolding ddd1_\<oo>\<pp>1 unfolding o_assoc snd_convol
unfolding o_assoc apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
unfolding \<Sigma>1.map_comp0[symmetric] ddd1_leaf1 \<Lambda>1_natural
unfolding o_assoc F_map_comp[symmetric] leaf1_flat1 F_map_id id_o \<Lambda>1_Inr ..

lemma alg\<rho>1: "dtor_J o alg\<rho>1 = F_map eval1 o \<rho>1 o K1_map <id, dtor_J>"
unfolding dd1_K1_as_\<Sigma>\<Sigma>1[symmetric] o_assoc
unfolding o_assoc[symmetric] K1_as_\<Sigma>\<Sigma>1_natural
unfolding o_assoc eval1 alg\<rho>1_def ..

lemma flat1_embL1: "flat1 o embL1 o \<Sigma>\<Sigma>0_map embL1 = embL1 o flat0" (is "?L = ?R")
proof-
  have "?L = ext0 (\<oo>\<pp>1 o Abs_\<Sigma>1 o Inl) embL1"
  proof(rule ext0_unique)
    show "flat1 \<circ> embL1 \<circ> \<Sigma>\<Sigma>0_map embL1 \<circ> leaf0 = embL1"
    unfolding o_assoc[symmetric] unfolding leaf0_natural
    unfolding o_assoc apply(subst o_assoc[symmetric])
    apply(subst embL1_def) unfolding ext0_comp_leaf0 flat1_leaf1 id_o ..
  next
    show "flat1 \<circ> embL1 \<circ> \<Sigma>\<Sigma>0_map embL1 \<circ> \<oo>\<pp>0 = \<oo>\<pp>1 \<circ> Abs_\<Sigma>1 \<circ> Inl \<circ> \<Sigma>0_map (flat1 \<circ> embL1 \<circ> \<Sigma>\<Sigma>0_map embL1)"
    apply(subst o_assoc[symmetric]) unfolding embL1_natural
    unfolding o_assoc apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric],
                            subst o_assoc[symmetric])
    unfolding embL1_def unfolding ext0_commute unfolding embL1_def[symmetric]
    unfolding o_assoc apply(subst o_assoc[symmetric])
    unfolding \<oo>\<pp>1_natural[symmetric]
    unfolding o_assoc apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
    unfolding map_sum_Inl Abs_\<Sigma>1_natural
    unfolding o_assoc[symmetric] map_sum_Inl \<Sigma>0.map_comp0[symmetric] embL1_natural[symmetric]
    apply(rule sym) apply(subst \<Sigma>0.map_comp0) unfolding o_assoc
    unfolding flat1_def unfolding ext1_commute
    apply(rule sym) apply(subst o_assoc[symmetric])
    unfolding Abs_\<Sigma>1_natural unfolding o_assoc[symmetric] map_sum_Inl \<oo>\<pp>1_natural[symmetric] ..
  qed
  also have "... = ?R"
  proof(rule sym, rule ext0_unique)
    show "embL1 \<circ> flat0 \<circ> leaf0 = embL1"
    unfolding o_assoc[symmetric] flat0_leaf0 o_id ..
  next
    show "embL1 \<circ> flat0 \<circ> \<oo>\<pp>0 = \<oo>\<pp>1 \<circ> Abs_\<Sigma>1 \<circ> Inl \<circ> \<Sigma>0_map (embL1 \<circ> flat0)"
    unfolding flat0_def o_assoc[symmetric] ext0_commute
    unfolding o_assoc
    apply(subst embL1_def) unfolding ext0_commute apply(subst embL1_def[symmetric])
    unfolding \<Sigma>0.map_comp0 o_assoc ..
  qed
  finally show ?thesis .
qed

lemma ddd1_embL1: "ddd1 \<circ> embL1 = (embL1 ** F_map embL1) \<circ> ddd0" (is "?L = ?R")
proof-
  have "?L = ext0 <\<oo>\<pp>1 o Abs_\<Sigma>1 o Inl o \<Sigma>0_map fst, F_map (flat1 o embL1) o \<Lambda>0> (leaf1 ** F_map leaf1)"
  proof(rule ext0_unique)
    show "ddd1 \<circ> embL1 \<circ> leaf0 = leaf1 ** F_map leaf1"
    apply(rule fst_snd_cong)
    unfolding fst_comp_map_prod snd_comp_map_prod
    unfolding  embL1_def
    apply (subst (3) o_assoc[symmetric]) defer apply (subst (3) o_assoc[symmetric])
    unfolding ext0_comp_leaf0
    unfolding ddd1_def ext1_comp_leaf1 fst_comp_map_prod snd_comp_map_prod by(rule refl, rule refl)
  next
    show "ddd1 \<circ> embL1 \<circ> \<oo>\<pp>0 =
          <\<oo>\<pp>1 \<circ> Abs_\<Sigma>1 \<circ> Inl \<circ> \<Sigma>0_map fst , F_map (flat1 \<circ> embL1) \<circ> \<Lambda>0> \<circ> \<Sigma>0_map (ddd1 \<circ> embL1)" (is "?A = ?B")
    proof(rule fst_snd_cong)
      show "fst o ?A = fst o ?B"
      unfolding o_assoc fst_convol unfolding o_assoc[symmetric] \<Sigma>0.map_comp0[symmetric]
      unfolding o_assoc
      apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
      apply(subst embL1_def) unfolding ext0_commute apply(subst embL1_def[symmetric])
      unfolding o_assoc apply(subst o_assoc[symmetric])
      apply(subst ddd1_def) unfolding ext1_commute apply(subst ddd1_def[symmetric])
      unfolding o_assoc fst_convol
      apply(subst o_assoc[symmetric]) unfolding \<Sigma>1.map_comp0[symmetric]
      apply(subst o_assoc[symmetric]) unfolding Abs_\<Sigma>1_natural map_sum_Inl o_assoc[symmetric]
      unfolding \<Sigma>0.map_comp0[symmetric] o_assoc ..
    next
      show "snd o ?A = snd o ?B"
      unfolding o_assoc snd_convol unfolding o_assoc[symmetric]
      apply(subst embL1_def) unfolding ext0_commute apply(subst embL1_def[symmetric])
      unfolding o_assoc apply(subst o_assoc[symmetric], subst o_assoc[symmetric])
      apply(subst ddd1_def) unfolding ext1_commute apply(subst ddd1_def[symmetric])
      unfolding o_assoc snd_convol
      unfolding o_assoc apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
      unfolding Abs_\<Sigma>1_natural map_sum_Inl o_assoc[symmetric]
      unfolding o_assoc apply(subst o_assoc[symmetric], subst o_assoc[symmetric])
      unfolding \<Lambda>1_Inl unfolding \<Sigma>0.map_comp0 F_map_comp o_assoc ..
    qed
  qed
  also have "... = ?R"
  proof(rule sym, rule ext0_unique)
    show "(embL1 ** F_map embL1) \<circ> ddd0 \<circ> leaf0 = leaf1 ** F_map leaf1"
    unfolding o_assoc apply(subst o_assoc[symmetric])
    apply(subst ddd0_def) unfolding ext0_comp_leaf0
    unfolding map_prod.comp unfolding F_map_comp[symmetric]
    apply(subst embL1_def, subst embL1_def) unfolding ext0_comp_leaf0 ..
  next
    show "embL1 ** F_map embL1 \<circ> ddd0 \<circ> \<oo>\<pp>0 =
          <\<oo>\<pp>1 \<circ> Abs_\<Sigma>1 \<circ> Inl \<circ> \<Sigma>0_map fst , F_map (flat1 \<circ> embL1) \<circ> \<Lambda>0> \<circ> \<Sigma>0_map (embL1 ** F_map embL1 \<circ> ddd0)"
    (is "?A = ?B") proof(rule fst_snd_cong)
      show "fst o ?A = fst o ?B"
      unfolding o_assoc fst_convol fst_comp_map_prod
      unfolding o_assoc[symmetric] \<Sigma>0.map_comp0[symmetric] unfolding o_assoc unfolding fst_comp_map_prod
      unfolding o_assoc apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
      apply(subst ddd0_def) unfolding ext0_commute apply(subst ddd0_def[symmetric])
      unfolding o_assoc fst_convol
      apply(subst embL1_def) unfolding ext0_commute apply(subst embL1_def[symmetric])
      unfolding \<Sigma>0.map_comp0 o_assoc ..
    next
      show "snd o ?A = snd o ?B"
      unfolding o_assoc snd_convol snd_comp_map_prod
      unfolding o_assoc apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
      apply(subst ddd0_def) unfolding ext0_commute apply(subst ddd0_def[symmetric])
      unfolding o_assoc apply(subst o_assoc[symmetric]) unfolding snd_convol
      unfolding o_assoc F_map_comp[symmetric]
      unfolding flat1_embL1[symmetric]
      unfolding F_map_comp
      unfolding o_assoc apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
      unfolding \<Lambda>0_natural[symmetric]
      unfolding o_assoc \<Sigma>0.map_comp0 ..
    qed
  qed
  finally show ?thesis .
qed

lemma dd1_embL1: "dd1 \<circ> embL1 = F_map embL1 \<circ> dd0"
unfolding dd1_def dd0_def o_assoc[symmetric] ddd1_embL1 by auto

lemma F_map_embL1_\<Sigma>\<Sigma>0_map:
"F_map embL1 \<circ> dd0 \<circ> \<Sigma>\<Sigma>0_map <id , dtor_J> =
 dd1 \<circ> \<Sigma>\<Sigma>1_map <id , dtor_J> \<circ> embL1"
unfolding o_assoc[symmetric] unfolding embL1_natural[symmetric]
unfolding o_assoc dd1_embL1 ..

lemma eval1_embL1: "eval1 o embL1 = eval0"
unfolding eval0_def apply(rule J.dtor_unfold_unique)
unfolding eval1_def unfolding o_assoc
unfolding dtor_unfold_J_pointfree
unfolding F_map_comp
apply(subst o_assoc[symmetric], subst o_assoc[symmetric])
unfolding F_map_embL1_\<Sigma>\<Sigma>0_map o_assoc ..

theorem alg\<Lambda>1_alg\<Lambda>0_alg\<rho>1:
"alg\<Lambda>1 o Abs_\<Sigma>1 = case_sum alg\<Lambda>0 alg\<rho>1" (is "?L = ?R")
proof(rule sum_comp_cases)
  show "?L o Inl = ?R o Inl"
  unfolding case_sum_o_inj apply(subst dtor_J_o_inj[symmetric])
  unfolding o_assoc dtor_J_alg\<Lambda>1 unfolding Abs_\<Sigma>1_natural o_assoc[symmetric] map_sum_Inl
  unfolding o_assoc apply(subst o_assoc[symmetric], subst o_assoc[symmetric]) unfolding \<Lambda>1_Inl
  unfolding o_assoc F_map_comp[symmetric] eval1_embL1 dtor_J_alg\<Lambda>0 ..
next
  show "?L o Inr = ?R o Inr"
  unfolding alg\<rho>1_def case_sum_o_inj alg\<Lambda>1_def K1_as_\<Sigma>\<Sigma>1_def o_assoc ..
qed

theorem alg\<Lambda>1_Inl: "alg\<Lambda>1 (Abs_\<Sigma>1 (Inl x)) = alg\<Lambda>0 x" (is "?L = ?R")
unfolding o_eq_dest_lhs[OF alg\<Lambda>1_alg\<Lambda>0_alg\<rho>1] by simp

lemma alg\<Lambda>1_Inl_pointfree: "alg\<Lambda>1 o Abs_\<Sigma>1 o Inl = alg\<Lambda>0"
unfolding o_def fun_eq_iff alg\<Lambda>1_Inl by simp

theorem alg\<Lambda>1_Inr: "alg\<Lambda>1 (Abs_\<Sigma>1 (Inr x)) = alg\<rho>1 x" (is "?L = ?R")
unfolding o_eq_dest_lhs[OF alg\<Lambda>1_alg\<Lambda>0_alg\<rho>1] by simp



subsection{* Up-to corecursor with guard not necessarily at the top *}

definition ff1 :: "'a F \<Rightarrow> 'a \<Sigma>1" where "ff1 \<equiv> Abs_\<Sigma>1 o Inl o ff0"

lemma alg\<Lambda>1_ff1: "alg\<Lambda>1 \<circ> ff1 = ctor_J"
unfolding ff1_def o_assoc alg\<Lambda>1_Inl_pointfree alg\<Lambda>0_ff0 ..

lemma ff1_transfer[transfer_rule]: "(F_rel R ===> \<Sigma>1_rel R) ff1 ff1"
unfolding ff1_def by transfer_prover

lemma ff1_natural: "\<Sigma>1_map f o ff1 = ff1 o F_map f"
using ff1_transfer[of "BNF_Def.Grp UNIV f"]
unfolding \<Sigma>1.rel_Grp F_rel_Grp
unfolding Grp_def rel_fun_def by auto

definition gg1 :: "'a \<Sigma>\<Sigma>1 F \<Rightarrow> 'a \<Sigma>\<Sigma>1" where
"gg1 \<equiv> \<oo>\<pp>1 o ff1"

lemma eval1_gg1: "eval1 o gg1 = ctor_J o F_map eval1"
unfolding gg1_def
unfolding o_assoc unfolding eval1_comp_\<oo>\<pp>1
unfolding o_assoc[symmetric] ff1_natural
unfolding o_assoc alg\<Lambda>1_ff1 ..

lemma gg1_transfer[transfer_rule]: "(F_rel (\<Sigma>\<Sigma>1_rel R) ===> \<Sigma>\<Sigma>1_rel R) gg1 gg1"
unfolding gg1_def by transfer_prover

lemma gg1_natural: "\<Sigma>\<Sigma>1_map f o gg1 = gg1 o F_map (\<Sigma>\<Sigma>1_map f)"
using gg1_transfer[of "BNF_Def.Grp UNIV f"]
unfolding \<Sigma>\<Sigma>1.rel_Grp F_rel_Grp
unfolding Grp_def rel_fun_def by auto

definition unfoldUU1 :: "('a \<Rightarrow> 'a \<Sigma>\<Sigma>1 F \<Sigma>\<Sigma>1) \<Rightarrow> 'a \<Rightarrow> J" where
"unfoldUU1 s \<equiv> unfoldU1 (F_map flat1 o dd1 o \<Sigma>\<Sigma>1_map <gg1, id> o s)"

theorem unfoldUU1:
"unfoldUU1 s =
 eval1 o \<Sigma>\<Sigma>1_map (ctor_J o F_map eval1 o F_map (\<Sigma>\<Sigma>1_map (unfoldUU1 s))) o s"
unfolding unfoldUU1_def apply(subst unfoldU1_ctor_J_pointfree[symmetric]) unfolding unfoldUU1_def[symmetric]
unfolding extdd1_def F_map_comp[symmetric] o_assoc
apply(subst o_assoc[symmetric]) unfolding F_map_comp[symmetric]
apply(subst o_assoc[symmetric]) unfolding flat1_natural[symmetric]
apply(subst o_assoc) unfolding eval1_flat1
unfolding F_map_comp
apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
unfolding dd1_natural[symmetric]
unfolding o_assoc apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
unfolding dd1_natural[symmetric]
unfolding o_assoc[symmetric] \<Sigma>\<Sigma>1.map_comp0[symmetric]
unfolding o_assoc eval1_gg1 unfolding \<Sigma>\<Sigma>1.map_comp0 o_assoc
apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric],
      subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
unfolding \<Sigma>\<Sigma>1.map_comp0[symmetric]
apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
unfolding \<Sigma>\<Sigma>1.map_comp0[symmetric] map_prod.comp map_prod_o_convol o_id F_map_comp[symmetric]
apply(rule sym) unfolding o_assoc
apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
unfolding \<Sigma>\<Sigma>1.map_comp0[symmetric] F_map_comp[symmetric] o_assoc[symmetric] gg1_natural
unfolding o_assoc eval1_gg1
apply(rule sym)
apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
unfolding F_map_comp[symmetric] convol_comp_id2 convol_ctor_J_dtor_J
          \<Sigma>\<Sigma>1.map_comp0 o_assoc eval1 ctor_dtor_J_pointfree id_o ..

theorem unfoldUU1_unique:
assumes f: "f = eval1 o \<Sigma>\<Sigma>1_map (ctor_J o F_map eval1 o F_map (\<Sigma>\<Sigma>1_map f)) o s"
shows "f = unfoldUU1 s"
unfolding unfoldUU1_def apply(rule unfoldU1_unique)
apply(rule sym) apply(subst f) unfolding extdd1_def
unfolding o_assoc
apply(subst eval1_def) unfolding dtor_unfold_J_pointfree apply(subst eval1_def[symmetric])
unfolding o_assoc
apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
unfolding o_assoc \<Sigma>\<Sigma>1.map_comp0[symmetric]  convol_o id_o dtor_J_ctor_pointfree F_map_comp[symmetric]
unfolding o_assoc[symmetric] flat1_natural[symmetric]
unfolding o_assoc eval1_flat1 unfolding o_assoc[symmetric] unfolding F_map_comp
apply(rule sym) apply(subst F_map_comp[symmetric], subst \<Sigma>\<Sigma>1.map_comp0[symmetric])
unfolding o_assoc apply(subst o_assoc[symmetric])
unfolding dd1_natural[symmetric]
unfolding o_assoc[symmetric] \<Sigma>\<Sigma>1.map_comp0[symmetric] map_prod_o_convol o_id
unfolding o_assoc[symmetric] gg1_natural
unfolding o_assoc eval1_gg1 F_map_comp ..

(* corecursion: *)
definition corecUU1 :: "('a \<Rightarrow> (J + 'a) \<Sigma>\<Sigma>1 F \<Sigma>\<Sigma>1) \<Rightarrow> 'a \<Rightarrow> J" where
"corecUU1 s \<equiv>
 unfoldUU1 (case_sum (leaf1 o dd1 o leaf1 o <Inl , F_map Inl \<circ> dtor_J>) s) o Inr"

lemma unfoldUU1_Inl:
"unfoldUU1 (case_sum (leaf1 \<circ> dd1 \<circ> leaf1 \<circ> <Inl , F_map Inl \<circ> dtor_J>) s) \<circ> Inl = id"
(is "?L = ?R")
proof-
  have "?L = unfoldUU1 (leaf1 o dd1 o leaf1 o <id, dtor_J>)"
  apply(rule unfoldUU1_unique)
  apply(subst unfoldUU1)
  unfolding o_assoc[symmetric] case_sum_o_inj snd_convol
  unfolding F_map_comp \<Sigma>\<Sigma>1.map_comp0
  unfolding o_assoc
  apply(rule sym)
  unfolding o_assoc
  apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric],
              subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
  apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric],
              subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric],
              subst o_assoc[symmetric])
  unfolding leaf1_natural apply(subst o_assoc[symmetric])
  apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric],
              subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
  unfolding dd1_natural[symmetric]
  apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric],
              subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
  apply(subst o_assoc[symmetric], subst o_assoc[symmetric])
  unfolding leaf1_natural
  unfolding o_assoc[symmetric] map_prod_o_convol o_id ..
  also have "... = ?R"
  apply(rule sym, rule unfoldUU1_unique)
  unfolding \<Sigma>\<Sigma>1.map_id0 F_map_id o_id
  unfolding o_assoc
  apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric],
              subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
  unfolding dd1_leaf1
  unfolding o_assoc[symmetric] snd_convol
  unfolding o_assoc
  apply(subst o_assoc[symmetric])
  unfolding leaf1_natural unfolding o_assoc eval1_leaf1 id_o
  apply(subst o_assoc[symmetric])
  unfolding F_map_comp[symmetric] eval1_leaf1 F_map_id o_id ctor_dtor_J_pointfree ..
  finally show ?thesis .
qed

theorem corecUU1_pointfree:
"corecUU1 s =
 eval1 o \<Sigma>\<Sigma>1_map (ctor_J o F_map eval1 o F_map (\<Sigma>\<Sigma>1_map (case_sum id (corecUU1 s)))) o s"
unfolding corecUU1_def
apply(subst unfoldUU1)
unfolding o_assoc[symmetric] unfolding case_sum_o_inj
apply(subst unfoldUU1_Inl[symmetric, of s])
unfolding o_assoc case_sum_Inl_Inr_L extdd1_def ..

theorem corecUU1_unique:
  assumes f: "f = eval1 o \<Sigma>\<Sigma>1_map (ctor_J o F_map eval1 o F_map (\<Sigma>\<Sigma>1_map (case_sum id f))) o s"
  shows "f = corecUU1 s"
  unfolding corecUU1_def
  apply(rule eq_o_InrI[OF unfoldUU1_Inl unfoldUU1_unique])
  apply (subst f)
  apply (auto simp: fun_eq_iff eval1_leaf1' pre_J.map_comp o_eq_dest[OF dd1_leaf1] convol_def
    leaf1_natural o_assoc case_sum_o_inj(1) eval1_leaf1 pre_J.map_id J.ctor_dtor split: sum.splits)
  done

theorem corecUU1:
"corecUU1 s a =
 eval1 (\<Sigma>\<Sigma>1_map (ctor_J o F_map eval1 o F_map (\<Sigma>\<Sigma>1_map (case_sum id (corecUU1 s)))) (s a))"
using corecUU1_pointfree unfolding o_def fun_eq_iff by(rule allE)

end