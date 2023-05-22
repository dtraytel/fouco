header {* More on corecursion and coinduction up to *}

theory Stream_More_Corec_Upto8
imports Stream_Corec_Upto8
begin


subsection{* A natural-transformation-based version of the up-to corecursion principle *}

definition alg\<rho>8 :: "J K8 \<Rightarrow> J" where "alg\<rho>8 \<equiv> eval8 o K8_as_\<Sigma>\<Sigma>8"

lemma dd8_K8_as_\<Sigma>\<Sigma>8:
"dd8 o K8_as_\<Sigma>\<Sigma>8 = \<rho>8"
unfolding K8_as_\<Sigma>\<Sigma>8_def dd8_def
unfolding o_assoc apply(subst o_assoc[symmetric])
unfolding ddd8_\<oo>\<pp>8 unfolding o_assoc snd_convol
unfolding o_assoc apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
unfolding \<Sigma>8.map_comp0[symmetric] ddd8_leaf8 \<Lambda>8_natural
unfolding o_assoc F_map_comp[symmetric] leaf8_flat8 F_map_id id_o \<Lambda>8_Inr ..

lemma alg\<rho>8: "dtor_J o alg\<rho>8 = F_map eval8 o \<rho>8 o K8_map <id, dtor_J>"
unfolding dd8_K8_as_\<Sigma>\<Sigma>8[symmetric] o_assoc
unfolding o_assoc[symmetric] K8_as_\<Sigma>\<Sigma>8_natural
unfolding o_assoc eval8 alg\<rho>8_def ..

lemma flat8_embL8: "flat8 o embL8 o \<Sigma>\<Sigma>7_map embL8 = embL8 o flat7" (is "?L = ?R")
proof-
  have "?L = ext7 (\<oo>\<pp>8 o Abs_\<Sigma>8 o Inl) embL8"
  proof(rule ext7_unique)
    show "flat8 \<circ> embL8 \<circ> \<Sigma>\<Sigma>7_map embL8 \<circ> leaf7 = embL8"
    unfolding o_assoc[symmetric] unfolding leaf7_natural
    unfolding o_assoc apply(subst o_assoc[symmetric])
    apply(subst embL8_def) unfolding ext7_comp_leaf7 flat8_leaf8 id_o ..
  next
    show "flat8 \<circ> embL8 \<circ> \<Sigma>\<Sigma>7_map embL8 \<circ> \<oo>\<pp>7 = \<oo>\<pp>8 \<circ> Abs_\<Sigma>8 \<circ> Inl \<circ> \<Sigma>7_map (flat8 \<circ> embL8 \<circ> \<Sigma>\<Sigma>7_map embL8)"
    apply(subst o_assoc[symmetric]) unfolding embL8_natural
    unfolding o_assoc apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric],
                            subst o_assoc[symmetric])
    unfolding embL8_def unfolding ext7_commute unfolding embL8_def[symmetric]
    unfolding o_assoc apply(subst o_assoc[symmetric])
    unfolding \<oo>\<pp>8_natural[symmetric]
    unfolding o_assoc apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
    unfolding map_sum_Inl Abs_\<Sigma>8_natural
    unfolding o_assoc[symmetric] map_sum_Inl \<Sigma>7.map_comp0[symmetric] embL8_natural[symmetric]
    apply(rule sym) apply(subst \<Sigma>7.map_comp0) unfolding o_assoc
    unfolding flat8_def unfolding ext8_commute
    apply(rule sym) apply(subst o_assoc[symmetric])
    unfolding Abs_\<Sigma>8_natural unfolding o_assoc[symmetric] map_sum_Inl \<oo>\<pp>8_natural[symmetric] ..
  qed
  also have "... = ?R"
  proof(rule sym, rule ext7_unique)
    show "embL8 \<circ> flat7 \<circ> leaf7 = embL8"
    unfolding o_assoc[symmetric] flat7_leaf7 o_id ..
  next
    show "embL8 \<circ> flat7 \<circ> \<oo>\<pp>7 = \<oo>\<pp>8 \<circ> Abs_\<Sigma>8 \<circ> Inl \<circ> \<Sigma>7_map (embL8 \<circ> flat7)"
    unfolding flat7_def o_assoc[symmetric] ext7_commute
    unfolding o_assoc
    apply(subst embL8_def) unfolding ext7_commute apply(subst embL8_def[symmetric])
    unfolding \<Sigma>7.map_comp0 o_assoc ..
  qed
  finally show ?thesis .
qed

lemma ddd8_embL8: "ddd8 \<circ> embL8 = (embL8 ** F_map embL8) \<circ> ddd7" (is "?L = ?R")
proof-
  have "?L = ext7 <\<oo>\<pp>8 o Abs_\<Sigma>8 o Inl o \<Sigma>7_map fst, F_map (flat8 o embL8) o \<Lambda>7> (leaf8 ** F_map leaf8)"
  proof(rule ext7_unique)
    show "ddd8 \<circ> embL8 \<circ> leaf7 = leaf8 ** F_map leaf8"
    apply(rule fst_snd_cong)
    unfolding fst_comp_map_prod snd_comp_map_prod
    unfolding  embL8_def
    apply (subst (3) o_assoc[symmetric]) defer apply (subst (3) o_assoc[symmetric])
    unfolding ext7_comp_leaf7
    unfolding ddd8_def ext8_comp_leaf8 fst_comp_map_prod snd_comp_map_prod by(rule refl, rule refl)
  next
    show "ddd8 \<circ> embL8 \<circ> \<oo>\<pp>7 =
          <\<oo>\<pp>8 \<circ> Abs_\<Sigma>8 \<circ> Inl \<circ> \<Sigma>7_map fst , F_map (flat8 \<circ> embL8) \<circ> \<Lambda>7> \<circ> \<Sigma>7_map (ddd8 \<circ> embL8)" (is "?A = ?B")
    proof(rule fst_snd_cong)
      show "fst o ?A = fst o ?B"
      unfolding o_assoc fst_convol unfolding o_assoc[symmetric] \<Sigma>7.map_comp0[symmetric]
      unfolding o_assoc
      apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
      apply(subst embL8_def) unfolding ext7_commute apply(subst embL8_def[symmetric])
      unfolding o_assoc apply(subst o_assoc[symmetric])
      apply(subst ddd8_def) unfolding ext8_commute apply(subst ddd8_def[symmetric])
      unfolding o_assoc fst_convol
      apply(subst o_assoc[symmetric]) unfolding \<Sigma>8.map_comp0[symmetric]
      apply(subst o_assoc[symmetric]) unfolding Abs_\<Sigma>8_natural map_sum_Inl o_assoc[symmetric]
      unfolding \<Sigma>7.map_comp0[symmetric] o_assoc ..
    next
      show "snd o ?A = snd o ?B"
      unfolding o_assoc snd_convol unfolding o_assoc[symmetric]
      apply(subst embL8_def) unfolding ext7_commute apply(subst embL8_def[symmetric])
      unfolding o_assoc apply(subst o_assoc[symmetric], subst o_assoc[symmetric])
      apply(subst ddd8_def) unfolding ext8_commute apply(subst ddd8_def[symmetric])
      unfolding o_assoc snd_convol
      unfolding o_assoc apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
      unfolding Abs_\<Sigma>8_natural map_sum_Inl o_assoc[symmetric]
      unfolding o_assoc apply(subst o_assoc[symmetric], subst o_assoc[symmetric])
      unfolding \<Lambda>8_Inl unfolding \<Sigma>7.map_comp0 F_map_comp o_assoc ..
    qed
  qed
  also have "... = ?R"
  proof(rule sym, rule ext7_unique)
    show "(embL8 ** F_map embL8) \<circ> ddd7 \<circ> leaf7 = leaf8 ** F_map leaf8"
    unfolding o_assoc apply(subst o_assoc[symmetric])
    apply(subst ddd7_def) unfolding ext7_comp_leaf7
    unfolding map_prod.comp unfolding F_map_comp[symmetric]
    apply(subst embL8_def, subst embL8_def) unfolding ext7_comp_leaf7 ..
  next
    show "embL8 ** F_map embL8 \<circ> ddd7 \<circ> \<oo>\<pp>7 =
          <\<oo>\<pp>8 \<circ> Abs_\<Sigma>8 \<circ> Inl \<circ> \<Sigma>7_map fst , F_map (flat8 \<circ> embL8) \<circ> \<Lambda>7> \<circ> \<Sigma>7_map (embL8 ** F_map embL8 \<circ> ddd7)"
    (is "?A = ?B") proof(rule fst_snd_cong)
      show "fst o ?A = fst o ?B"
      unfolding o_assoc fst_convol fst_comp_map_prod
      unfolding o_assoc[symmetric] \<Sigma>7.map_comp0[symmetric] unfolding o_assoc unfolding fst_comp_map_prod
      unfolding o_assoc apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
      apply(subst ddd7_def) unfolding ext7_commute apply(subst ddd7_def[symmetric])
      unfolding o_assoc fst_convol
      apply(subst embL8_def) unfolding ext7_commute apply(subst embL8_def[symmetric])
      unfolding \<Sigma>7.map_comp0 o_assoc ..
    next
      show "snd o ?A = snd o ?B"
      unfolding o_assoc snd_convol snd_comp_map_prod
      unfolding o_assoc apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
      apply(subst ddd7_def) unfolding ext7_commute apply(subst ddd7_def[symmetric])
      unfolding o_assoc apply(subst o_assoc[symmetric]) unfolding snd_convol
      unfolding o_assoc F_map_comp[symmetric]
      unfolding flat8_embL8[symmetric]
      unfolding F_map_comp
      unfolding o_assoc apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
      unfolding \<Lambda>7_natural[symmetric]
      unfolding o_assoc \<Sigma>7.map_comp0 ..
    qed
  qed
  finally show ?thesis .
qed

lemma dd8_embL8: "dd8 \<circ> embL8 = F_map embL8 \<circ> dd7"
unfolding dd8_def dd7_def o_assoc[symmetric] ddd8_embL8 by auto

lemma F_map_embL8_\<Sigma>\<Sigma>7_map:
"F_map embL8 \<circ> dd7 \<circ> \<Sigma>\<Sigma>7_map <id , dtor_J> =
 dd8 \<circ> \<Sigma>\<Sigma>8_map <id , dtor_J> \<circ> embL8"
unfolding o_assoc[symmetric] unfolding embL8_natural[symmetric]
unfolding o_assoc dd8_embL8 ..

lemma eval8_embL8: "eval8 o embL8 = eval7"
unfolding eval7_def apply(rule J.dtor_unfold_unique)
unfolding eval8_def unfolding o_assoc
unfolding dtor_unfold_J_pointfree
unfolding F_map_comp
apply(subst o_assoc[symmetric], subst o_assoc[symmetric])
unfolding F_map_embL8_\<Sigma>\<Sigma>7_map o_assoc ..

theorem alg\<Lambda>8_alg\<Lambda>7_alg\<rho>8:
"alg\<Lambda>8 o Abs_\<Sigma>8 = case_sum alg\<Lambda>7 alg\<rho>8" (is "?L = ?R")
proof(rule sum_comp_cases)
  show "?L o Inl = ?R o Inl"
  unfolding case_sum_o_inj apply(subst dtor_J_o_inj[symmetric])
  unfolding o_assoc dtor_J_alg\<Lambda>8 unfolding Abs_\<Sigma>8_natural o_assoc[symmetric] map_sum_Inl
  unfolding o_assoc apply(subst o_assoc[symmetric], subst o_assoc[symmetric]) unfolding \<Lambda>8_Inl
  unfolding o_assoc F_map_comp[symmetric] eval8_embL8 dtor_J_alg\<Lambda>7 ..
next
  show "?L o Inr = ?R o Inr"
  unfolding alg\<rho>8_def case_sum_o_inj alg\<Lambda>8_def K8_as_\<Sigma>\<Sigma>8_def o_assoc ..
qed

theorem alg\<Lambda>8_Inl: "alg\<Lambda>8 (Abs_\<Sigma>8 (Inl x)) = alg\<Lambda>7 x" (is "?L = ?R")
unfolding o_eq_dest_lhs[OF alg\<Lambda>8_alg\<Lambda>7_alg\<rho>8] by simp

lemma alg\<Lambda>8_Inl_pointfree: "alg\<Lambda>8 o Abs_\<Sigma>8 o Inl = alg\<Lambda>7"
unfolding o_def fun_eq_iff alg\<Lambda>8_Inl by simp

theorem alg\<Lambda>8_Inr: "alg\<Lambda>8 (Abs_\<Sigma>8 (Inr x)) = alg\<rho>8 x" (is "?L = ?R")
unfolding o_eq_dest_lhs[OF alg\<Lambda>8_alg\<Lambda>7_alg\<rho>8] by simp



subsection{* Up-to corecursor with guard not necessarily at the top *}

definition ff8 :: "'a F \<Rightarrow> 'a \<Sigma>8" where "ff8 \<equiv> Abs_\<Sigma>8 o Inl o ff7"

lemma alg\<Lambda>8_ff8: "alg\<Lambda>8 \<circ> ff8 = ctor_J"
unfolding ff8_def o_assoc alg\<Lambda>8_Inl_pointfree alg\<Lambda>7_ff7 ..

lemma ff8_transfer[transfer_rule]: "(F_rel R ===> \<Sigma>8_rel R) ff8 ff8"
unfolding ff8_def by transfer_prover

lemma ff8_natural: "\<Sigma>8_map f o ff8 = ff8 o F_map f"
using ff8_transfer[of "BNF_Def.Grp UNIV f"]
unfolding \<Sigma>8.rel_Grp F_rel_Grp
unfolding Grp_def rel_fun_def by auto

definition gg8 :: "'a \<Sigma>\<Sigma>8 F \<Rightarrow> 'a \<Sigma>\<Sigma>8" where
"gg8 \<equiv> \<oo>\<pp>8 o ff8"

lemma eval8_gg8: "eval8 o gg8 = ctor_J o F_map eval8"
unfolding gg8_def
unfolding o_assoc unfolding eval8_comp_\<oo>\<pp>8
unfolding o_assoc[symmetric] ff8_natural
unfolding o_assoc alg\<Lambda>8_ff8 ..

lemma gg8_transfer[transfer_rule]: "(F_rel (\<Sigma>\<Sigma>8_rel R) ===> \<Sigma>\<Sigma>8_rel R) gg8 gg8"
unfolding gg8_def by transfer_prover

lemma gg8_natural: "\<Sigma>\<Sigma>8_map f o gg8 = gg8 o F_map (\<Sigma>\<Sigma>8_map f)"
using gg8_transfer[of "BNF_Def.Grp UNIV f"]
unfolding \<Sigma>\<Sigma>8.rel_Grp F_rel_Grp
unfolding Grp_def rel_fun_def by auto

definition unfoldUU8 :: "('a \<Rightarrow> 'a \<Sigma>\<Sigma>8 F \<Sigma>\<Sigma>8) \<Rightarrow> 'a \<Rightarrow> J" where
"unfoldUU8 s \<equiv> unfoldU8 (F_map flat8 o dd8 o \<Sigma>\<Sigma>8_map <gg8, id> o s)"

theorem unfoldUU8:
"unfoldUU8 s =
 eval8 o \<Sigma>\<Sigma>8_map (ctor_J o F_map eval8 o F_map (\<Sigma>\<Sigma>8_map (unfoldUU8 s))) o s"
unfolding unfoldUU8_def apply(subst unfoldU8_ctor_J_pointfree[symmetric]) unfolding unfoldUU8_def[symmetric]
unfolding extdd8_def F_map_comp[symmetric] o_assoc
apply(subst o_assoc[symmetric]) unfolding F_map_comp[symmetric]
apply(subst o_assoc[symmetric]) unfolding flat8_natural[symmetric]
apply(subst o_assoc) unfolding eval8_flat8
unfolding F_map_comp
apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
unfolding dd8_natural[symmetric]
unfolding o_assoc apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
unfolding dd8_natural[symmetric]
unfolding o_assoc[symmetric] \<Sigma>\<Sigma>8.map_comp0[symmetric]
unfolding o_assoc eval8_gg8 unfolding \<Sigma>\<Sigma>8.map_comp0 o_assoc
apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric],
      subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
unfolding \<Sigma>\<Sigma>8.map_comp0[symmetric]
apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
unfolding \<Sigma>\<Sigma>8.map_comp0[symmetric] map_prod.comp map_prod_o_convol o_id F_map_comp[symmetric]
apply(rule sym) unfolding o_assoc
apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
unfolding \<Sigma>\<Sigma>8.map_comp0[symmetric] F_map_comp[symmetric] o_assoc[symmetric] gg8_natural
unfolding o_assoc eval8_gg8
apply(rule sym)
apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
unfolding F_map_comp[symmetric] convol_comp_id2 convol_ctor_J_dtor_J
          \<Sigma>\<Sigma>8.map_comp0 o_assoc eval8 ctor_dtor_J_pointfree id_o ..

theorem unfoldUU8_unique:
assumes f: "f = eval8 o \<Sigma>\<Sigma>8_map (ctor_J o F_map eval8 o F_map (\<Sigma>\<Sigma>8_map f)) o s"
shows "f = unfoldUU8 s"
unfolding unfoldUU8_def apply(rule unfoldU8_unique)
apply(rule sym) apply(subst f) unfolding extdd8_def
unfolding o_assoc
apply(subst eval8_def) unfolding dtor_unfold_J_pointfree apply(subst eval8_def[symmetric])
unfolding o_assoc
apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
unfolding o_assoc \<Sigma>\<Sigma>8.map_comp0[symmetric]  convol_o id_o dtor_J_ctor_pointfree F_map_comp[symmetric]
unfolding o_assoc[symmetric] flat8_natural[symmetric]
unfolding o_assoc eval8_flat8 unfolding o_assoc[symmetric] unfolding F_map_comp
apply(rule sym) apply(subst F_map_comp[symmetric], subst \<Sigma>\<Sigma>8.map_comp0[symmetric])
unfolding o_assoc apply(subst o_assoc[symmetric])
unfolding dd8_natural[symmetric]
unfolding o_assoc[symmetric] \<Sigma>\<Sigma>8.map_comp0[symmetric] map_prod_o_convol o_id
unfolding o_assoc[symmetric] gg8_natural
unfolding o_assoc eval8_gg8 F_map_comp ..

(* corecursion: *)
definition corecUU8 :: "('a \<Rightarrow> (J + 'a) \<Sigma>\<Sigma>8 F \<Sigma>\<Sigma>8) \<Rightarrow> 'a \<Rightarrow> J" where
"corecUU8 s \<equiv>
 unfoldUU8 (case_sum (leaf8 o dd8 o leaf8 o <Inl , F_map Inl \<circ> dtor_J>) s) o Inr"

lemma unfoldUU8_Inl:
"unfoldUU8 (case_sum (leaf8 \<circ> dd8 \<circ> leaf8 \<circ> <Inl , F_map Inl \<circ> dtor_J>) s) \<circ> Inl = id"
(is "?L = ?R")
proof-
  have "?L = unfoldUU8 (leaf8 o dd8 o leaf8 o <id, dtor_J>)"
  apply(rule unfoldUU8_unique)
  apply(subst unfoldUU8)
  unfolding o_assoc[symmetric] case_sum_o_inj snd_convol
  unfolding F_map_comp \<Sigma>\<Sigma>8.map_comp0
  unfolding o_assoc
  apply(rule sym)
  unfolding o_assoc
  apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric],
              subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
  apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric],
              subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric],
              subst o_assoc[symmetric])
  unfolding leaf8_natural apply(subst o_assoc[symmetric])
  apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric],
              subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
  unfolding dd8_natural[symmetric]
  apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric],
              subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
  apply(subst o_assoc[symmetric], subst o_assoc[symmetric])
  unfolding leaf8_natural
  unfolding o_assoc[symmetric] map_prod_o_convol o_id ..
  also have "... = ?R"
  apply(rule sym, rule unfoldUU8_unique)
  unfolding \<Sigma>\<Sigma>8.map_id0 F_map_id o_id
  unfolding o_assoc
  apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric],
              subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
  unfolding dd8_leaf8
  unfolding o_assoc[symmetric] snd_convol
  unfolding o_assoc
  apply(subst o_assoc[symmetric])
  unfolding leaf8_natural unfolding o_assoc eval8_leaf8 id_o
  apply(subst o_assoc[symmetric])
  unfolding F_map_comp[symmetric] eval8_leaf8 F_map_id o_id ctor_dtor_J_pointfree ..
  finally show ?thesis .
qed

theorem corecUU8_pointfree:
"corecUU8 s =
 eval8 o \<Sigma>\<Sigma>8_map (ctor_J o F_map eval8 o F_map (\<Sigma>\<Sigma>8_map (case_sum id (corecUU8 s)))) o s"
unfolding corecUU8_def
apply(subst unfoldUU8)
unfolding o_assoc[symmetric] unfolding case_sum_o_inj
apply(subst unfoldUU8_Inl[symmetric, of s])
unfolding o_assoc case_sum_Inl_Inr_L extdd8_def ..

theorem corecUU8_unique:
  assumes f: "f = eval8 o \<Sigma>\<Sigma>8_map (ctor_J o F_map eval8 o F_map (\<Sigma>\<Sigma>8_map (case_sum id f))) o s"
  shows "f = corecUU8 s"
  unfolding corecUU8_def
  apply(rule eq_o_InrI[OF unfoldUU8_Inl unfoldUU8_unique])
  apply (subst f)
  apply (auto simp: fun_eq_iff eval8_leaf8' pre_J.map_comp o_eq_dest[OF dd8_leaf8] convol_def
    leaf8_natural o_assoc case_sum_o_inj(1) eval8_leaf8 pre_J.map_id J.ctor_dtor split: sum.splits)
  done

theorem corecUU8:
"corecUU8 s a =
 eval8 (\<Sigma>\<Sigma>8_map (ctor_J o F_map eval8 o F_map (\<Sigma>\<Sigma>8_map (case_sum id (corecUU8 s)))) (s a))"
using corecUU8_pointfree unfolding o_def fun_eq_iff by(rule allE)

end