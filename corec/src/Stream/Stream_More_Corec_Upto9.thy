header {* More on corecursion and coinduction up to *}

theory Stream_More_Corec_Upto9
imports Stream_Corec_Upto9
begin


subsection{* A natural-transformation-based version of the up-to corecursion principle *}

definition alg\<rho>9 :: "J K9 \<Rightarrow> J" where "alg\<rho>9 \<equiv> eval9 o K9_as_\<Sigma>\<Sigma>9"

lemma dd9_K9_as_\<Sigma>\<Sigma>9:
"dd9 o K9_as_\<Sigma>\<Sigma>9 = \<rho>9"
unfolding K9_as_\<Sigma>\<Sigma>9_def dd9_def
unfolding o_assoc apply(subst o_assoc[symmetric])
unfolding ddd9_\<oo>\<pp>9 unfolding o_assoc snd_convol
unfolding o_assoc apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
unfolding \<Sigma>9.map_comp0[symmetric] ddd9_leaf9 \<Lambda>9_natural
unfolding o_assoc F_map_comp[symmetric] leaf9_flat9 F_map_id id_o \<Lambda>9_Inr ..

lemma alg\<rho>9: "dtor_J o alg\<rho>9 = F_map eval9 o \<rho>9 o K9_map <id, dtor_J>"
unfolding dd9_K9_as_\<Sigma>\<Sigma>9[symmetric] o_assoc
unfolding o_assoc[symmetric] K9_as_\<Sigma>\<Sigma>9_natural
unfolding o_assoc eval9 alg\<rho>9_def ..

lemma flat9_embL9: "flat9 o embL9 o \<Sigma>\<Sigma>8_map embL9 = embL9 o flat8" (is "?L = ?R")
proof-
  have "?L = ext8 (\<oo>\<pp>9 o Abs_\<Sigma>9 o Inl) embL9"
  proof(rule ext8_unique)
    show "flat9 \<circ> embL9 \<circ> \<Sigma>\<Sigma>8_map embL9 \<circ> leaf8 = embL9"
    unfolding o_assoc[symmetric] unfolding leaf8_natural
    unfolding o_assoc apply(subst o_assoc[symmetric])
    apply(subst embL9_def) unfolding ext8_comp_leaf8 flat9_leaf9 id_o ..
  next
    show "flat9 \<circ> embL9 \<circ> \<Sigma>\<Sigma>8_map embL9 \<circ> \<oo>\<pp>8 = \<oo>\<pp>9 \<circ> Abs_\<Sigma>9 \<circ> Inl \<circ> \<Sigma>8_map (flat9 \<circ> embL9 \<circ> \<Sigma>\<Sigma>8_map embL9)"
    apply(subst o_assoc[symmetric]) unfolding embL9_natural
    unfolding o_assoc apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric],
                            subst o_assoc[symmetric])
    unfolding embL9_def unfolding ext8_commute unfolding embL9_def[symmetric]
    unfolding o_assoc apply(subst o_assoc[symmetric])
    unfolding \<oo>\<pp>9_natural[symmetric]
    unfolding o_assoc apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
    unfolding map_sum_Inl Abs_\<Sigma>9_natural
    unfolding o_assoc[symmetric] map_sum_Inl \<Sigma>8.map_comp0[symmetric] embL9_natural[symmetric]
    apply(rule sym) apply(subst \<Sigma>8.map_comp0) unfolding o_assoc
    unfolding flat9_def unfolding ext9_commute
    apply(rule sym) apply(subst o_assoc[symmetric])
    unfolding Abs_\<Sigma>9_natural unfolding o_assoc[symmetric] map_sum_Inl \<oo>\<pp>9_natural[symmetric] ..
  qed
  also have "... = ?R"
  proof(rule sym, rule ext8_unique)
    show "embL9 \<circ> flat8 \<circ> leaf8 = embL9"
    unfolding o_assoc[symmetric] flat8_leaf8 o_id ..
  next
    show "embL9 \<circ> flat8 \<circ> \<oo>\<pp>8 = \<oo>\<pp>9 \<circ> Abs_\<Sigma>9 \<circ> Inl \<circ> \<Sigma>8_map (embL9 \<circ> flat8)"
    unfolding flat8_def o_assoc[symmetric] ext8_commute
    unfolding o_assoc
    apply(subst embL9_def) unfolding ext8_commute apply(subst embL9_def[symmetric])
    unfolding \<Sigma>8.map_comp0 o_assoc ..
  qed
  finally show ?thesis .
qed

lemma ddd9_embL9: "ddd9 \<circ> embL9 = (embL9 ** F_map embL9) \<circ> ddd8" (is "?L = ?R")
proof-
  have "?L = ext8 <\<oo>\<pp>9 o Abs_\<Sigma>9 o Inl o \<Sigma>8_map fst, F_map (flat9 o embL9) o \<Lambda>8> (leaf9 ** F_map leaf9)"
  proof(rule ext8_unique)
    show "ddd9 \<circ> embL9 \<circ> leaf8 = leaf9 ** F_map leaf9"
    apply(rule fst_snd_cong)
    unfolding fst_comp_map_prod snd_comp_map_prod
    unfolding  embL9_def
    apply (subst (3) o_assoc[symmetric]) defer apply (subst (3) o_assoc[symmetric])
    unfolding ext8_comp_leaf8
    unfolding ddd9_def ext9_comp_leaf9 fst_comp_map_prod snd_comp_map_prod by(rule refl, rule refl)
  next
    show "ddd9 \<circ> embL9 \<circ> \<oo>\<pp>8 =
          <\<oo>\<pp>9 \<circ> Abs_\<Sigma>9 \<circ> Inl \<circ> \<Sigma>8_map fst , F_map (flat9 \<circ> embL9) \<circ> \<Lambda>8> \<circ> \<Sigma>8_map (ddd9 \<circ> embL9)" (is "?A = ?B")
    proof(rule fst_snd_cong)
      show "fst o ?A = fst o ?B"
      unfolding o_assoc fst_convol unfolding o_assoc[symmetric] \<Sigma>8.map_comp0[symmetric]
      unfolding o_assoc
      apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
      apply(subst embL9_def) unfolding ext8_commute apply(subst embL9_def[symmetric])
      unfolding o_assoc apply(subst o_assoc[symmetric])
      apply(subst ddd9_def) unfolding ext9_commute apply(subst ddd9_def[symmetric])
      unfolding o_assoc fst_convol
      apply(subst o_assoc[symmetric]) unfolding \<Sigma>9.map_comp0[symmetric]
      apply(subst o_assoc[symmetric]) unfolding Abs_\<Sigma>9_natural map_sum_Inl o_assoc[symmetric]
      unfolding \<Sigma>8.map_comp0[symmetric] o_assoc ..
    next
      show "snd o ?A = snd o ?B"
      unfolding o_assoc snd_convol unfolding o_assoc[symmetric]
      apply(subst embL9_def) unfolding ext8_commute apply(subst embL9_def[symmetric])
      unfolding o_assoc apply(subst o_assoc[symmetric], subst o_assoc[symmetric])
      apply(subst ddd9_def) unfolding ext9_commute apply(subst ddd9_def[symmetric])
      unfolding o_assoc snd_convol
      unfolding o_assoc apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
      unfolding Abs_\<Sigma>9_natural map_sum_Inl o_assoc[symmetric]
      unfolding o_assoc apply(subst o_assoc[symmetric], subst o_assoc[symmetric])
      unfolding \<Lambda>9_Inl unfolding \<Sigma>8.map_comp0 F_map_comp o_assoc ..
    qed
  qed
  also have "... = ?R"
  proof(rule sym, rule ext8_unique)
    show "(embL9 ** F_map embL9) \<circ> ddd8 \<circ> leaf8 = leaf9 ** F_map leaf9"
    unfolding o_assoc apply(subst o_assoc[symmetric])
    apply(subst ddd8_def) unfolding ext8_comp_leaf8
    unfolding map_prod.comp unfolding F_map_comp[symmetric]
    apply(subst embL9_def, subst embL9_def) unfolding ext8_comp_leaf8 ..
  next
    show "embL9 ** F_map embL9 \<circ> ddd8 \<circ> \<oo>\<pp>8 =
          <\<oo>\<pp>9 \<circ> Abs_\<Sigma>9 \<circ> Inl \<circ> \<Sigma>8_map fst , F_map (flat9 \<circ> embL9) \<circ> \<Lambda>8> \<circ> \<Sigma>8_map (embL9 ** F_map embL9 \<circ> ddd8)"
    (is "?A = ?B") proof(rule fst_snd_cong)
      show "fst o ?A = fst o ?B"
      unfolding o_assoc fst_convol fst_comp_map_prod
      unfolding o_assoc[symmetric] \<Sigma>8.map_comp0[symmetric] unfolding o_assoc unfolding fst_comp_map_prod
      unfolding o_assoc apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
      apply(subst ddd8_def) unfolding ext8_commute apply(subst ddd8_def[symmetric])
      unfolding o_assoc fst_convol
      apply(subst embL9_def) unfolding ext8_commute apply(subst embL9_def[symmetric])
      unfolding \<Sigma>8.map_comp0 o_assoc ..
    next
      show "snd o ?A = snd o ?B"
      unfolding o_assoc snd_convol snd_comp_map_prod
      unfolding o_assoc apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
      apply(subst ddd8_def) unfolding ext8_commute apply(subst ddd8_def[symmetric])
      unfolding o_assoc apply(subst o_assoc[symmetric]) unfolding snd_convol
      unfolding o_assoc F_map_comp[symmetric]
      unfolding flat9_embL9[symmetric]
      unfolding F_map_comp
      unfolding o_assoc apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
      unfolding \<Lambda>8_natural[symmetric]
      unfolding o_assoc \<Sigma>8.map_comp0 ..
    qed
  qed
  finally show ?thesis .
qed

lemma dd9_embL9: "dd9 \<circ> embL9 = F_map embL9 \<circ> dd8"
unfolding dd9_def dd8_def o_assoc[symmetric] ddd9_embL9 by auto

lemma F_map_embL9_\<Sigma>\<Sigma>8_map:
"F_map embL9 \<circ> dd8 \<circ> \<Sigma>\<Sigma>8_map <id , dtor_J> =
 dd9 \<circ> \<Sigma>\<Sigma>9_map <id , dtor_J> \<circ> embL9"
unfolding o_assoc[symmetric] unfolding embL9_natural[symmetric]
unfolding o_assoc dd9_embL9 ..

lemma eval9_embL9: "eval9 o embL9 = eval8"
unfolding eval8_def apply(rule J.dtor_unfold_unique)
unfolding eval9_def unfolding o_assoc
unfolding dtor_unfold_J_pointfree
unfolding F_map_comp
apply(subst o_assoc[symmetric], subst o_assoc[symmetric])
unfolding F_map_embL9_\<Sigma>\<Sigma>8_map o_assoc ..

theorem alg\<Lambda>9_alg\<Lambda>8_alg\<rho>9:
"alg\<Lambda>9 o Abs_\<Sigma>9 = case_sum alg\<Lambda>8 alg\<rho>9" (is "?L = ?R")
proof(rule sum_comp_cases)
  show "?L o Inl = ?R o Inl"
  unfolding case_sum_o_inj apply(subst dtor_J_o_inj[symmetric])
  unfolding o_assoc dtor_J_alg\<Lambda>9 unfolding Abs_\<Sigma>9_natural o_assoc[symmetric] map_sum_Inl
  unfolding o_assoc apply(subst o_assoc[symmetric], subst o_assoc[symmetric]) unfolding \<Lambda>9_Inl
  unfolding o_assoc F_map_comp[symmetric] eval9_embL9 dtor_J_alg\<Lambda>8 ..
next
  show "?L o Inr = ?R o Inr"
  unfolding alg\<rho>9_def case_sum_o_inj alg\<Lambda>9_def K9_as_\<Sigma>\<Sigma>9_def o_assoc ..
qed

theorem alg\<Lambda>9_Inl: "alg\<Lambda>9 (Abs_\<Sigma>9 (Inl x)) = alg\<Lambda>8 x" (is "?L = ?R")
unfolding o_eq_dest_lhs[OF alg\<Lambda>9_alg\<Lambda>8_alg\<rho>9] by simp

lemma alg\<Lambda>9_Inl_pointfree: "alg\<Lambda>9 o Abs_\<Sigma>9 o Inl = alg\<Lambda>8"
unfolding o_def fun_eq_iff alg\<Lambda>9_Inl by simp

theorem alg\<Lambda>9_Inr: "alg\<Lambda>9 (Abs_\<Sigma>9 (Inr x)) = alg\<rho>9 x" (is "?L = ?R")
unfolding o_eq_dest_lhs[OF alg\<Lambda>9_alg\<Lambda>8_alg\<rho>9] by simp



subsection{* Up-to corecursor with guard not necessarily at the top *}

definition ff9 :: "'a F \<Rightarrow> 'a \<Sigma>9" where "ff9 \<equiv> Abs_\<Sigma>9 o Inl o ff8"

lemma alg\<Lambda>9_ff9: "alg\<Lambda>9 \<circ> ff9 = ctor_J"
unfolding ff9_def o_assoc alg\<Lambda>9_Inl_pointfree alg\<Lambda>8_ff8 ..

lemma ff9_transfer[transfer_rule]: "(F_rel R ===> \<Sigma>9_rel R) ff9 ff9"
unfolding ff9_def by transfer_prover

lemma ff9_natural: "\<Sigma>9_map f o ff9 = ff9 o F_map f"
using ff9_transfer[of "BNF_Def.Grp UNIV f"]
unfolding \<Sigma>9.rel_Grp F_rel_Grp
unfolding Grp_def rel_fun_def by auto

definition gg9 :: "'a \<Sigma>\<Sigma>9 F \<Rightarrow> 'a \<Sigma>\<Sigma>9" where
"gg9 \<equiv> \<oo>\<pp>9 o ff9"

lemma eval9_gg9: "eval9 o gg9 = ctor_J o F_map eval9"
unfolding gg9_def
unfolding o_assoc unfolding eval9_comp_\<oo>\<pp>9
unfolding o_assoc[symmetric] ff9_natural
unfolding o_assoc alg\<Lambda>9_ff9 ..

lemma gg9_transfer[transfer_rule]: "(F_rel (\<Sigma>\<Sigma>9_rel R) ===> \<Sigma>\<Sigma>9_rel R) gg9 gg9"
unfolding gg9_def by transfer_prover

lemma gg9_natural: "\<Sigma>\<Sigma>9_map f o gg9 = gg9 o F_map (\<Sigma>\<Sigma>9_map f)"
using gg9_transfer[of "BNF_Def.Grp UNIV f"]
unfolding \<Sigma>\<Sigma>9.rel_Grp F_rel_Grp
unfolding Grp_def rel_fun_def by auto

definition unfoldUU9 :: "('a \<Rightarrow> 'a \<Sigma>\<Sigma>9 F \<Sigma>\<Sigma>9) \<Rightarrow> 'a \<Rightarrow> J" where
"unfoldUU9 s \<equiv> unfoldU9 (F_map flat9 o dd9 o \<Sigma>\<Sigma>9_map <gg9, id> o s)"

theorem unfoldUU9:
"unfoldUU9 s =
 eval9 o \<Sigma>\<Sigma>9_map (ctor_J o F_map eval9 o F_map (\<Sigma>\<Sigma>9_map (unfoldUU9 s))) o s"
unfolding unfoldUU9_def apply(subst unfoldU9_ctor_J_pointfree[symmetric]) unfolding unfoldUU9_def[symmetric]
unfolding extdd9_def F_map_comp[symmetric] o_assoc
apply(subst o_assoc[symmetric]) unfolding F_map_comp[symmetric]
apply(subst o_assoc[symmetric]) unfolding flat9_natural[symmetric]
apply(subst o_assoc) unfolding eval9_flat9
unfolding F_map_comp
apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
unfolding dd9_natural[symmetric]
unfolding o_assoc apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
unfolding dd9_natural[symmetric]
unfolding o_assoc[symmetric] \<Sigma>\<Sigma>9.map_comp0[symmetric]
unfolding o_assoc eval9_gg9 unfolding \<Sigma>\<Sigma>9.map_comp0 o_assoc
apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric],
      subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
unfolding \<Sigma>\<Sigma>9.map_comp0[symmetric]
apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
unfolding \<Sigma>\<Sigma>9.map_comp0[symmetric] map_prod.comp map_prod_o_convol o_id F_map_comp[symmetric]
apply(rule sym) unfolding o_assoc
apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
unfolding \<Sigma>\<Sigma>9.map_comp0[symmetric] F_map_comp[symmetric] o_assoc[symmetric] gg9_natural
unfolding o_assoc eval9_gg9
apply(rule sym)
apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
unfolding F_map_comp[symmetric] convol_comp_id2 convol_ctor_J_dtor_J
          \<Sigma>\<Sigma>9.map_comp0 o_assoc eval9 ctor_dtor_J_pointfree id_o ..

theorem unfoldUU9_unique:
assumes f: "f = eval9 o \<Sigma>\<Sigma>9_map (ctor_J o F_map eval9 o F_map (\<Sigma>\<Sigma>9_map f)) o s"
shows "f = unfoldUU9 s"
unfolding unfoldUU9_def apply(rule unfoldU9_unique)
apply(rule sym) apply(subst f) unfolding extdd9_def
unfolding o_assoc
apply(subst eval9_def) unfolding dtor_unfold_J_pointfree apply(subst eval9_def[symmetric])
unfolding o_assoc
apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
unfolding o_assoc \<Sigma>\<Sigma>9.map_comp0[symmetric]  convol_o id_o dtor_J_ctor_pointfree F_map_comp[symmetric]
unfolding o_assoc[symmetric] flat9_natural[symmetric]
unfolding o_assoc eval9_flat9 unfolding o_assoc[symmetric] unfolding F_map_comp
apply(rule sym) apply(subst F_map_comp[symmetric], subst \<Sigma>\<Sigma>9.map_comp0[symmetric])
unfolding o_assoc apply(subst o_assoc[symmetric])
unfolding dd9_natural[symmetric]
unfolding o_assoc[symmetric] \<Sigma>\<Sigma>9.map_comp0[symmetric] map_prod_o_convol o_id
unfolding o_assoc[symmetric] gg9_natural
unfolding o_assoc eval9_gg9 F_map_comp ..

(* corecursion: *)
definition corecUU9 :: "('a \<Rightarrow> (J + 'a) \<Sigma>\<Sigma>9 F \<Sigma>\<Sigma>9) \<Rightarrow> 'a \<Rightarrow> J" where
"corecUU9 s \<equiv>
 unfoldUU9 (case_sum (leaf9 o dd9 o leaf9 o <Inl , F_map Inl \<circ> dtor_J>) s) o Inr"

lemma unfoldUU9_Inl:
"unfoldUU9 (case_sum (leaf9 \<circ> dd9 \<circ> leaf9 \<circ> <Inl , F_map Inl \<circ> dtor_J>) s) \<circ> Inl = id"
(is "?L = ?R")
proof-
  have "?L = unfoldUU9 (leaf9 o dd9 o leaf9 o <id, dtor_J>)"
  apply(rule unfoldUU9_unique)
  apply(subst unfoldUU9)
  unfolding o_assoc[symmetric] case_sum_o_inj snd_convol
  unfolding F_map_comp \<Sigma>\<Sigma>9.map_comp0
  unfolding o_assoc
  apply(rule sym)
  unfolding o_assoc
  apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric],
              subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
  apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric],
              subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric],
              subst o_assoc[symmetric])
  unfolding leaf9_natural apply(subst o_assoc[symmetric])
  apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric],
              subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
  unfolding dd9_natural[symmetric]
  apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric],
              subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
  apply(subst o_assoc[symmetric], subst o_assoc[symmetric])
  unfolding leaf9_natural
  unfolding o_assoc[symmetric] map_prod_o_convol o_id ..
  also have "... = ?R"
  apply(rule sym, rule unfoldUU9_unique)
  unfolding \<Sigma>\<Sigma>9.map_id0 F_map_id o_id
  unfolding o_assoc
  apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric],
              subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
  unfolding dd9_leaf9
  unfolding o_assoc[symmetric] snd_convol
  unfolding o_assoc
  apply(subst o_assoc[symmetric])
  unfolding leaf9_natural unfolding o_assoc eval9_leaf9 id_o
  apply(subst o_assoc[symmetric])
  unfolding F_map_comp[symmetric] eval9_leaf9 F_map_id o_id ctor_dtor_J_pointfree ..
  finally show ?thesis .
qed

theorem corecUU9_pointfree:
"corecUU9 s =
 eval9 o \<Sigma>\<Sigma>9_map (ctor_J o F_map eval9 o F_map (\<Sigma>\<Sigma>9_map (case_sum id (corecUU9 s)))) o s"
unfolding corecUU9_def
apply(subst unfoldUU9)
unfolding o_assoc[symmetric] unfolding case_sum_o_inj
apply(subst unfoldUU9_Inl[symmetric, of s])
unfolding o_assoc case_sum_Inl_Inr_L extdd9_def ..

theorem corecUU9_unique:
  assumes f: "f = eval9 o \<Sigma>\<Sigma>9_map (ctor_J o F_map eval9 o F_map (\<Sigma>\<Sigma>9_map (case_sum id f))) o s"
  shows "f = corecUU9 s"
  unfolding corecUU9_def
  apply(rule eq_o_InrI[OF unfoldUU9_Inl unfoldUU9_unique])
  apply (subst f)
  apply (auto simp: fun_eq_iff eval9_leaf9' pre_J.map_comp o_eq_dest[OF dd9_leaf9] convol_def
    leaf9_natural o_assoc case_sum_o_inj(1) eval9_leaf9 pre_J.map_id J.ctor_dtor split: sum.splits)
  done

theorem corecUU9:
"corecUU9 s a =
 eval9 (\<Sigma>\<Sigma>9_map (ctor_J o F_map eval9 o F_map (\<Sigma>\<Sigma>9_map (case_sum id (corecUU9 s)))) (s a))"
using corecUU9_pointfree unfolding o_def fun_eq_iff by(rule allE)

end