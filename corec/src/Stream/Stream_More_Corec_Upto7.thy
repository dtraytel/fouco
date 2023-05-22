header {* More on corecursion and coinduction up to *}

theory Stream_More_Corec_Upto7
imports Stream_Corec_Upto7
begin


subsection{* A natural-transformation-based version of the up-to corecursion principle *}

definition alg\<rho>7 :: "J K7 \<Rightarrow> J" where "alg\<rho>7 \<equiv> eval7 o K7_as_\<Sigma>\<Sigma>7"

lemma dd7_K7_as_\<Sigma>\<Sigma>7:
"dd7 o K7_as_\<Sigma>\<Sigma>7 = \<rho>7"
unfolding K7_as_\<Sigma>\<Sigma>7_def dd7_def
unfolding o_assoc apply(subst o_assoc[symmetric])
unfolding ddd7_\<oo>\<pp>7 unfolding o_assoc snd_convol
unfolding o_assoc apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
unfolding \<Sigma>7.map_comp0[symmetric] ddd7_leaf7 \<Lambda>7_natural
unfolding o_assoc F_map_comp[symmetric] leaf7_flat7 F_map_id id_o \<Lambda>7_Inr ..

lemma alg\<rho>7: "dtor_J o alg\<rho>7 = F_map eval7 o \<rho>7 o K7_map <id, dtor_J>"
unfolding dd7_K7_as_\<Sigma>\<Sigma>7[symmetric] o_assoc
unfolding o_assoc[symmetric] K7_as_\<Sigma>\<Sigma>7_natural
unfolding o_assoc eval7 alg\<rho>7_def ..

lemma flat7_embL7: "flat7 o embL7 o \<Sigma>\<Sigma>6_map embL7 = embL7 o flat6" (is "?L = ?R")
proof-
  have "?L = ext6 (\<oo>\<pp>7 o Abs_\<Sigma>7 o Inl) embL7"
  proof(rule ext6_unique)
    show "flat7 \<circ> embL7 \<circ> \<Sigma>\<Sigma>6_map embL7 \<circ> leaf6 = embL7"
    unfolding o_assoc[symmetric] unfolding leaf6_natural
    unfolding o_assoc apply(subst o_assoc[symmetric])
    apply(subst embL7_def) unfolding ext6_comp_leaf6 flat7_leaf7 id_o ..
  next
    show "flat7 \<circ> embL7 \<circ> \<Sigma>\<Sigma>6_map embL7 \<circ> \<oo>\<pp>6 = \<oo>\<pp>7 \<circ> Abs_\<Sigma>7 \<circ> Inl \<circ> \<Sigma>6_map (flat7 \<circ> embL7 \<circ> \<Sigma>\<Sigma>6_map embL7)"
    apply(subst o_assoc[symmetric]) unfolding embL7_natural
    unfolding o_assoc apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric],
                            subst o_assoc[symmetric])
    unfolding embL7_def unfolding ext6_commute unfolding embL7_def[symmetric]
    unfolding o_assoc apply(subst o_assoc[symmetric])
    unfolding \<oo>\<pp>7_natural[symmetric]
    unfolding o_assoc apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
    unfolding map_sum_Inl Abs_\<Sigma>7_natural
    unfolding o_assoc[symmetric] map_sum_Inl \<Sigma>6.map_comp0[symmetric] embL7_natural[symmetric]
    apply(rule sym) apply(subst \<Sigma>6.map_comp0) unfolding o_assoc
    unfolding flat7_def unfolding ext7_commute
    apply(rule sym) apply(subst o_assoc[symmetric])
    unfolding Abs_\<Sigma>7_natural unfolding o_assoc[symmetric] map_sum_Inl \<oo>\<pp>7_natural[symmetric] ..
  qed
  also have "... = ?R"
  proof(rule sym, rule ext6_unique)
    show "embL7 \<circ> flat6 \<circ> leaf6 = embL7"
    unfolding o_assoc[symmetric] flat6_leaf6 o_id ..
  next
    show "embL7 \<circ> flat6 \<circ> \<oo>\<pp>6 = \<oo>\<pp>7 \<circ> Abs_\<Sigma>7 \<circ> Inl \<circ> \<Sigma>6_map (embL7 \<circ> flat6)"
    unfolding flat6_def o_assoc[symmetric] ext6_commute
    unfolding o_assoc
    apply(subst embL7_def) unfolding ext6_commute apply(subst embL7_def[symmetric])
    unfolding \<Sigma>6.map_comp0 o_assoc ..
  qed
  finally show ?thesis .
qed

lemma ddd7_embL7: "ddd7 \<circ> embL7 = (embL7 ** F_map embL7) \<circ> ddd6" (is "?L = ?R")
proof-
  have "?L = ext6 <\<oo>\<pp>7 o Abs_\<Sigma>7 o Inl o \<Sigma>6_map fst, F_map (flat7 o embL7) o \<Lambda>6> (leaf7 ** F_map leaf7)"
  proof(rule ext6_unique)
    show "ddd7 \<circ> embL7 \<circ> leaf6 = leaf7 ** F_map leaf7"
    apply(rule fst_snd_cong)
    unfolding fst_comp_map_prod snd_comp_map_prod
    unfolding  embL7_def
    apply (subst (3) o_assoc[symmetric]) defer apply (subst (3) o_assoc[symmetric])
    unfolding ext6_comp_leaf6
    unfolding ddd7_def ext7_comp_leaf7 fst_comp_map_prod snd_comp_map_prod by(rule refl, rule refl)
  next
    show "ddd7 \<circ> embL7 \<circ> \<oo>\<pp>6 =
          <\<oo>\<pp>7 \<circ> Abs_\<Sigma>7 \<circ> Inl \<circ> \<Sigma>6_map fst , F_map (flat7 \<circ> embL7) \<circ> \<Lambda>6> \<circ> \<Sigma>6_map (ddd7 \<circ> embL7)" (is "?A = ?B")
    proof(rule fst_snd_cong)
      show "fst o ?A = fst o ?B"
      unfolding o_assoc fst_convol unfolding o_assoc[symmetric] \<Sigma>6.map_comp0[symmetric]
      unfolding o_assoc
      apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
      apply(subst embL7_def) unfolding ext6_commute apply(subst embL7_def[symmetric])
      unfolding o_assoc apply(subst o_assoc[symmetric])
      apply(subst ddd7_def) unfolding ext7_commute apply(subst ddd7_def[symmetric])
      unfolding o_assoc fst_convol
      apply(subst o_assoc[symmetric]) unfolding \<Sigma>7.map_comp0[symmetric]
      apply(subst o_assoc[symmetric]) unfolding Abs_\<Sigma>7_natural map_sum_Inl o_assoc[symmetric]
      unfolding \<Sigma>6.map_comp0[symmetric] o_assoc ..
    next
      show "snd o ?A = snd o ?B"
      unfolding o_assoc snd_convol unfolding o_assoc[symmetric]
      apply(subst embL7_def) unfolding ext6_commute apply(subst embL7_def[symmetric])
      unfolding o_assoc apply(subst o_assoc[symmetric], subst o_assoc[symmetric])
      apply(subst ddd7_def) unfolding ext7_commute apply(subst ddd7_def[symmetric])
      unfolding o_assoc snd_convol
      unfolding o_assoc apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
      unfolding Abs_\<Sigma>7_natural map_sum_Inl o_assoc[symmetric]
      unfolding o_assoc apply(subst o_assoc[symmetric], subst o_assoc[symmetric])
      unfolding \<Lambda>7_Inl unfolding \<Sigma>6.map_comp0 F_map_comp o_assoc ..
    qed
  qed
  also have "... = ?R"
  proof(rule sym, rule ext6_unique)
    show "(embL7 ** F_map embL7) \<circ> ddd6 \<circ> leaf6 = leaf7 ** F_map leaf7"
    unfolding o_assoc apply(subst o_assoc[symmetric])
    apply(subst ddd6_def) unfolding ext6_comp_leaf6
    unfolding map_prod.comp unfolding F_map_comp[symmetric]
    apply(subst embL7_def, subst embL7_def) unfolding ext6_comp_leaf6 ..
  next
    show "embL7 ** F_map embL7 \<circ> ddd6 \<circ> \<oo>\<pp>6 =
          <\<oo>\<pp>7 \<circ> Abs_\<Sigma>7 \<circ> Inl \<circ> \<Sigma>6_map fst , F_map (flat7 \<circ> embL7) \<circ> \<Lambda>6> \<circ> \<Sigma>6_map (embL7 ** F_map embL7 \<circ> ddd6)"
    (is "?A = ?B") proof(rule fst_snd_cong)
      show "fst o ?A = fst o ?B"
      unfolding o_assoc fst_convol fst_comp_map_prod
      unfolding o_assoc[symmetric] \<Sigma>6.map_comp0[symmetric] unfolding o_assoc unfolding fst_comp_map_prod
      unfolding o_assoc apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
      apply(subst ddd6_def) unfolding ext6_commute apply(subst ddd6_def[symmetric])
      unfolding o_assoc fst_convol
      apply(subst embL7_def) unfolding ext6_commute apply(subst embL7_def[symmetric])
      unfolding \<Sigma>6.map_comp0 o_assoc ..
    next
      show "snd o ?A = snd o ?B"
      unfolding o_assoc snd_convol snd_comp_map_prod
      unfolding o_assoc apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
      apply(subst ddd6_def) unfolding ext6_commute apply(subst ddd6_def[symmetric])
      unfolding o_assoc apply(subst o_assoc[symmetric]) unfolding snd_convol
      unfolding o_assoc F_map_comp[symmetric]
      unfolding flat7_embL7[symmetric]
      unfolding F_map_comp
      unfolding o_assoc apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
      unfolding \<Lambda>6_natural[symmetric]
      unfolding o_assoc \<Sigma>6.map_comp0 ..
    qed
  qed
  finally show ?thesis .
qed

lemma dd7_embL7: "dd7 \<circ> embL7 = F_map embL7 \<circ> dd6"
unfolding dd7_def dd6_def o_assoc[symmetric] ddd7_embL7 by auto

lemma F_map_embL7_\<Sigma>\<Sigma>6_map:
"F_map embL7 \<circ> dd6 \<circ> \<Sigma>\<Sigma>6_map <id , dtor_J> =
 dd7 \<circ> \<Sigma>\<Sigma>7_map <id , dtor_J> \<circ> embL7"
unfolding o_assoc[symmetric] unfolding embL7_natural[symmetric]
unfolding o_assoc dd7_embL7 ..

lemma eval7_embL7: "eval7 o embL7 = eval6"
unfolding eval6_def apply(rule J.dtor_unfold_unique)
unfolding eval7_def unfolding o_assoc
unfolding dtor_unfold_J_pointfree
unfolding F_map_comp
apply(subst o_assoc[symmetric], subst o_assoc[symmetric])
unfolding F_map_embL7_\<Sigma>\<Sigma>6_map o_assoc ..

theorem alg\<Lambda>7_alg\<Lambda>6_alg\<rho>7:
"alg\<Lambda>7 o Abs_\<Sigma>7 = case_sum alg\<Lambda>6 alg\<rho>7" (is "?L = ?R")
proof(rule sum_comp_cases)
  show "?L o Inl = ?R o Inl"
  unfolding case_sum_o_inj apply(subst dtor_J_o_inj[symmetric])
  unfolding o_assoc dtor_J_alg\<Lambda>7 unfolding Abs_\<Sigma>7_natural o_assoc[symmetric] map_sum_Inl
  unfolding o_assoc apply(subst o_assoc[symmetric], subst o_assoc[symmetric]) unfolding \<Lambda>7_Inl
  unfolding o_assoc F_map_comp[symmetric] eval7_embL7 dtor_J_alg\<Lambda>6 ..
next
  show "?L o Inr = ?R o Inr"
  unfolding alg\<rho>7_def case_sum_o_inj alg\<Lambda>7_def K7_as_\<Sigma>\<Sigma>7_def o_assoc ..
qed

theorem alg\<Lambda>7_Inl: "alg\<Lambda>7 (Abs_\<Sigma>7 (Inl x)) = alg\<Lambda>6 x" (is "?L = ?R")
unfolding o_eq_dest_lhs[OF alg\<Lambda>7_alg\<Lambda>6_alg\<rho>7] by simp

lemma alg\<Lambda>7_Inl_pointfree: "alg\<Lambda>7 o Abs_\<Sigma>7 o Inl = alg\<Lambda>6"
unfolding o_def fun_eq_iff alg\<Lambda>7_Inl by simp

theorem alg\<Lambda>7_Inr: "alg\<Lambda>7 (Abs_\<Sigma>7 (Inr x)) = alg\<rho>7 x" (is "?L = ?R")
unfolding o_eq_dest_lhs[OF alg\<Lambda>7_alg\<Lambda>6_alg\<rho>7] by simp



subsection{* Up-to corecursor with guard not necessarily at the top *}

definition ff7 :: "'a F \<Rightarrow> 'a \<Sigma>7" where "ff7 \<equiv> Abs_\<Sigma>7 o Inl o ff6"

lemma alg\<Lambda>7_ff7: "alg\<Lambda>7 \<circ> ff7 = ctor_J"
unfolding ff7_def o_assoc alg\<Lambda>7_Inl_pointfree alg\<Lambda>6_ff6 ..

lemma ff7_transfer[transfer_rule]: "(F_rel R ===> \<Sigma>7_rel R) ff7 ff7"
unfolding ff7_def by transfer_prover

lemma ff7_natural: "\<Sigma>7_map f o ff7 = ff7 o F_map f"
using ff7_transfer[of "BNF_Def.Grp UNIV f"]
unfolding \<Sigma>7.rel_Grp F_rel_Grp
unfolding Grp_def rel_fun_def by auto

definition gg7 :: "'a \<Sigma>\<Sigma>7 F \<Rightarrow> 'a \<Sigma>\<Sigma>7" where
"gg7 \<equiv> \<oo>\<pp>7 o ff7"

lemma eval7_gg7: "eval7 o gg7 = ctor_J o F_map eval7"
unfolding gg7_def
unfolding o_assoc unfolding eval7_comp_\<oo>\<pp>7
unfolding o_assoc[symmetric] ff7_natural
unfolding o_assoc alg\<Lambda>7_ff7 ..

lemma gg7_transfer[transfer_rule]: "(F_rel (\<Sigma>\<Sigma>7_rel R) ===> \<Sigma>\<Sigma>7_rel R) gg7 gg7"
unfolding gg7_def by transfer_prover

lemma gg7_natural: "\<Sigma>\<Sigma>7_map f o gg7 = gg7 o F_map (\<Sigma>\<Sigma>7_map f)"
using gg7_transfer[of "BNF_Def.Grp UNIV f"]
unfolding \<Sigma>\<Sigma>7.rel_Grp F_rel_Grp
unfolding Grp_def rel_fun_def by auto

definition unfoldUU7 :: "('a \<Rightarrow> 'a \<Sigma>\<Sigma>7 F \<Sigma>\<Sigma>7) \<Rightarrow> 'a \<Rightarrow> J" where
"unfoldUU7 s \<equiv> unfoldU7 (F_map flat7 o dd7 o \<Sigma>\<Sigma>7_map <gg7, id> o s)"

theorem unfoldUU7:
"unfoldUU7 s =
 eval7 o \<Sigma>\<Sigma>7_map (ctor_J o F_map eval7 o F_map (\<Sigma>\<Sigma>7_map (unfoldUU7 s))) o s"
unfolding unfoldUU7_def apply(subst unfoldU7_ctor_J_pointfree[symmetric]) unfolding unfoldUU7_def[symmetric]
unfolding extdd7_def F_map_comp[symmetric] o_assoc
apply(subst o_assoc[symmetric]) unfolding F_map_comp[symmetric]
apply(subst o_assoc[symmetric]) unfolding flat7_natural[symmetric]
apply(subst o_assoc) unfolding eval7_flat7
unfolding F_map_comp
apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
unfolding dd7_natural[symmetric]
unfolding o_assoc apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
unfolding dd7_natural[symmetric]
unfolding o_assoc[symmetric] \<Sigma>\<Sigma>7.map_comp0[symmetric]
unfolding o_assoc eval7_gg7 unfolding \<Sigma>\<Sigma>7.map_comp0 o_assoc
apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric],
      subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
unfolding \<Sigma>\<Sigma>7.map_comp0[symmetric]
apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
unfolding \<Sigma>\<Sigma>7.map_comp0[symmetric] map_prod.comp map_prod_o_convol o_id F_map_comp[symmetric]
apply(rule sym) unfolding o_assoc
apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
unfolding \<Sigma>\<Sigma>7.map_comp0[symmetric] F_map_comp[symmetric] o_assoc[symmetric] gg7_natural
unfolding o_assoc eval7_gg7
apply(rule sym)
apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
unfolding F_map_comp[symmetric] convol_comp_id2 convol_ctor_J_dtor_J
          \<Sigma>\<Sigma>7.map_comp0 o_assoc eval7 ctor_dtor_J_pointfree id_o ..

theorem unfoldUU7_unique:
assumes f: "f = eval7 o \<Sigma>\<Sigma>7_map (ctor_J o F_map eval7 o F_map (\<Sigma>\<Sigma>7_map f)) o s"
shows "f = unfoldUU7 s"
unfolding unfoldUU7_def apply(rule unfoldU7_unique)
apply(rule sym) apply(subst f) unfolding extdd7_def
unfolding o_assoc
apply(subst eval7_def) unfolding dtor_unfold_J_pointfree apply(subst eval7_def[symmetric])
unfolding o_assoc
apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
unfolding o_assoc \<Sigma>\<Sigma>7.map_comp0[symmetric]  convol_o id_o dtor_J_ctor_pointfree F_map_comp[symmetric]
unfolding o_assoc[symmetric] flat7_natural[symmetric]
unfolding o_assoc eval7_flat7 unfolding o_assoc[symmetric] unfolding F_map_comp
apply(rule sym) apply(subst F_map_comp[symmetric], subst \<Sigma>\<Sigma>7.map_comp0[symmetric])
unfolding o_assoc apply(subst o_assoc[symmetric])
unfolding dd7_natural[symmetric]
unfolding o_assoc[symmetric] \<Sigma>\<Sigma>7.map_comp0[symmetric] map_prod_o_convol o_id
unfolding o_assoc[symmetric] gg7_natural
unfolding o_assoc eval7_gg7 F_map_comp ..

(* corecursion: *)
definition corecUU7 :: "('a \<Rightarrow> (J + 'a) \<Sigma>\<Sigma>7 F \<Sigma>\<Sigma>7) \<Rightarrow> 'a \<Rightarrow> J" where
"corecUU7 s \<equiv>
 unfoldUU7 (case_sum (leaf7 o dd7 o leaf7 o <Inl , F_map Inl \<circ> dtor_J>) s) o Inr"

lemma unfoldUU7_Inl:
"unfoldUU7 (case_sum (leaf7 \<circ> dd7 \<circ> leaf7 \<circ> <Inl , F_map Inl \<circ> dtor_J>) s) \<circ> Inl = id"
(is "?L = ?R")
proof-
  have "?L = unfoldUU7 (leaf7 o dd7 o leaf7 o <id, dtor_J>)"
  apply(rule unfoldUU7_unique)
  apply(subst unfoldUU7)
  unfolding o_assoc[symmetric] case_sum_o_inj snd_convol
  unfolding F_map_comp \<Sigma>\<Sigma>7.map_comp0
  unfolding o_assoc
  apply(rule sym)
  unfolding o_assoc
  apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric],
              subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
  apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric],
              subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric],
              subst o_assoc[symmetric])
  unfolding leaf7_natural apply(subst o_assoc[symmetric])
  apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric],
              subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
  unfolding dd7_natural[symmetric]
  apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric],
              subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
  apply(subst o_assoc[symmetric], subst o_assoc[symmetric])
  unfolding leaf7_natural
  unfolding o_assoc[symmetric] map_prod_o_convol o_id ..
  also have "... = ?R"
  apply(rule sym, rule unfoldUU7_unique)
  unfolding \<Sigma>\<Sigma>7.map_id0 F_map_id o_id
  unfolding o_assoc
  apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric],
              subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
  unfolding dd7_leaf7
  unfolding o_assoc[symmetric] snd_convol
  unfolding o_assoc
  apply(subst o_assoc[symmetric])
  unfolding leaf7_natural unfolding o_assoc eval7_leaf7 id_o
  apply(subst o_assoc[symmetric])
  unfolding F_map_comp[symmetric] eval7_leaf7 F_map_id o_id ctor_dtor_J_pointfree ..
  finally show ?thesis .
qed

theorem corecUU7_pointfree:
"corecUU7 s =
 eval7 o \<Sigma>\<Sigma>7_map (ctor_J o F_map eval7 o F_map (\<Sigma>\<Sigma>7_map (case_sum id (corecUU7 s)))) o s"
unfolding corecUU7_def
apply(subst unfoldUU7)
unfolding o_assoc[symmetric] unfolding case_sum_o_inj
apply(subst unfoldUU7_Inl[symmetric, of s])
unfolding o_assoc case_sum_Inl_Inr_L extdd7_def ..

theorem corecUU7_unique:
  assumes f: "f = eval7 o \<Sigma>\<Sigma>7_map (ctor_J o F_map eval7 o F_map (\<Sigma>\<Sigma>7_map (case_sum id f))) o s"
  shows "f = corecUU7 s"
  unfolding corecUU7_def
  apply(rule eq_o_InrI[OF unfoldUU7_Inl unfoldUU7_unique])
  apply (subst f)
  apply (auto simp: fun_eq_iff eval7_leaf7' pre_J.map_comp o_eq_dest[OF dd7_leaf7] convol_def
    leaf7_natural o_assoc case_sum_o_inj(1) eval7_leaf7 pre_J.map_id J.ctor_dtor split: sum.splits)
  done

theorem corecUU7:
"corecUU7 s a =
 eval7 (\<Sigma>\<Sigma>7_map (ctor_J o F_map eval7 o F_map (\<Sigma>\<Sigma>7_map (case_sum id (corecUU7 s)))) (s a))"
using corecUU7_pointfree unfolding o_def fun_eq_iff by(rule allE)

end