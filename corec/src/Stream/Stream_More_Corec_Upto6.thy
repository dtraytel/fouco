header {* More on corecursion and coinduction up to *}

theory Stream_More_Corec_Upto6
imports Stream_Corec_Upto6
begin


subsection{* A natural-transformation-based version of the up-to corecursion principle *}

definition alg\<rho>6 :: "J K6 \<Rightarrow> J" where "alg\<rho>6 \<equiv> eval6 o K6_as_\<Sigma>\<Sigma>6"

lemma dd6_K6_as_\<Sigma>\<Sigma>6:
"dd6 o K6_as_\<Sigma>\<Sigma>6 = \<rho>6"
unfolding K6_as_\<Sigma>\<Sigma>6_def dd6_def
unfolding o_assoc apply(subst o_assoc[symmetric])
unfolding ddd6_\<oo>\<pp>6 unfolding o_assoc snd_convol
unfolding o_assoc apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
unfolding \<Sigma>6.map_comp0[symmetric] ddd6_leaf6 \<Lambda>6_natural
unfolding o_assoc F_map_comp[symmetric] leaf6_flat6 F_map_id id_o \<Lambda>6_Inr ..

lemma alg\<rho>6: "dtor_J o alg\<rho>6 = F_map eval6 o \<rho>6 o K6_map <id, dtor_J>"
unfolding dd6_K6_as_\<Sigma>\<Sigma>6[symmetric] o_assoc
unfolding o_assoc[symmetric] K6_as_\<Sigma>\<Sigma>6_natural
unfolding o_assoc eval6 alg\<rho>6_def ..

lemma flat6_embL6: "flat6 o embL6 o \<Sigma>\<Sigma>5_map embL6 = embL6 o flat5" (is "?L = ?R")
proof-
  have "?L = ext5 (\<oo>\<pp>6 o Abs_\<Sigma>6 o Inl) embL6"
  proof(rule ext5_unique)
    show "flat6 \<circ> embL6 \<circ> \<Sigma>\<Sigma>5_map embL6 \<circ> leaf5 = embL6"
    unfolding o_assoc[symmetric] unfolding leaf5_natural
    unfolding o_assoc apply(subst o_assoc[symmetric])
    apply(subst embL6_def) unfolding ext5_comp_leaf5 flat6_leaf6 id_o ..
  next
    show "flat6 \<circ> embL6 \<circ> \<Sigma>\<Sigma>5_map embL6 \<circ> \<oo>\<pp>5 = \<oo>\<pp>6 \<circ> Abs_\<Sigma>6 \<circ> Inl \<circ> \<Sigma>5_map (flat6 \<circ> embL6 \<circ> \<Sigma>\<Sigma>5_map embL6)"
    apply(subst o_assoc[symmetric]) unfolding embL6_natural
    unfolding o_assoc apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric],
                            subst o_assoc[symmetric])
    unfolding embL6_def unfolding ext5_commute unfolding embL6_def[symmetric]
    unfolding o_assoc apply(subst o_assoc[symmetric])
    unfolding \<oo>\<pp>6_natural[symmetric]
    unfolding o_assoc apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
    unfolding map_sum_Inl Abs_\<Sigma>6_natural
    unfolding o_assoc[symmetric] map_sum_Inl \<Sigma>5.map_comp0[symmetric] embL6_natural[symmetric]
    apply(rule sym) apply(subst \<Sigma>5.map_comp0) unfolding o_assoc
    unfolding flat6_def unfolding ext6_commute
    apply(rule sym) apply(subst o_assoc[symmetric])
    unfolding Abs_\<Sigma>6_natural unfolding o_assoc[symmetric] map_sum_Inl \<oo>\<pp>6_natural[symmetric] ..
  qed
  also have "... = ?R"
  proof(rule sym, rule ext5_unique)
    show "embL6 \<circ> flat5 \<circ> leaf5 = embL6"
    unfolding o_assoc[symmetric] flat5_leaf5 o_id ..
  next
    show "embL6 \<circ> flat5 \<circ> \<oo>\<pp>5 = \<oo>\<pp>6 \<circ> Abs_\<Sigma>6 \<circ> Inl \<circ> \<Sigma>5_map (embL6 \<circ> flat5)"
    unfolding flat5_def o_assoc[symmetric] ext5_commute
    unfolding o_assoc
    apply(subst embL6_def) unfolding ext5_commute apply(subst embL6_def[symmetric])
    unfolding \<Sigma>5.map_comp0 o_assoc ..
  qed
  finally show ?thesis .
qed

lemma ddd6_embL6: "ddd6 \<circ> embL6 = (embL6 ** F_map embL6) \<circ> ddd5" (is "?L = ?R")
proof-
  have "?L = ext5 <\<oo>\<pp>6 o Abs_\<Sigma>6 o Inl o \<Sigma>5_map fst, F_map (flat6 o embL6) o \<Lambda>5> (leaf6 ** F_map leaf6)"
  proof(rule ext5_unique)
    show "ddd6 \<circ> embL6 \<circ> leaf5 = leaf6 ** F_map leaf6"
    apply(rule fst_snd_cong)
    unfolding fst_comp_map_prod snd_comp_map_prod
    unfolding  embL6_def
    apply (subst (3) o_assoc[symmetric]) defer apply (subst (3) o_assoc[symmetric])
    unfolding ext5_comp_leaf5
    unfolding ddd6_def ext6_comp_leaf6 fst_comp_map_prod snd_comp_map_prod by(rule refl, rule refl)
  next
    show "ddd6 \<circ> embL6 \<circ> \<oo>\<pp>5 =
          <\<oo>\<pp>6 \<circ> Abs_\<Sigma>6 \<circ> Inl \<circ> \<Sigma>5_map fst , F_map (flat6 \<circ> embL6) \<circ> \<Lambda>5> \<circ> \<Sigma>5_map (ddd6 \<circ> embL6)" (is "?A = ?B")
    proof(rule fst_snd_cong)
      show "fst o ?A = fst o ?B"
      unfolding o_assoc fst_convol unfolding o_assoc[symmetric] \<Sigma>5.map_comp0[symmetric]
      unfolding o_assoc
      apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
      apply(subst embL6_def) unfolding ext5_commute apply(subst embL6_def[symmetric])
      unfolding o_assoc apply(subst o_assoc[symmetric])
      apply(subst ddd6_def) unfolding ext6_commute apply(subst ddd6_def[symmetric])
      unfolding o_assoc fst_convol
      apply(subst o_assoc[symmetric]) unfolding \<Sigma>6.map_comp0[symmetric]
      apply(subst o_assoc[symmetric]) unfolding Abs_\<Sigma>6_natural map_sum_Inl o_assoc[symmetric]
      unfolding \<Sigma>5.map_comp0[symmetric] o_assoc ..
    next
      show "snd o ?A = snd o ?B"
      unfolding o_assoc snd_convol unfolding o_assoc[symmetric]
      apply(subst embL6_def) unfolding ext5_commute apply(subst embL6_def[symmetric])
      unfolding o_assoc apply(subst o_assoc[symmetric], subst o_assoc[symmetric])
      apply(subst ddd6_def) unfolding ext6_commute apply(subst ddd6_def[symmetric])
      unfolding o_assoc snd_convol
      unfolding o_assoc apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
      unfolding Abs_\<Sigma>6_natural map_sum_Inl o_assoc[symmetric]
      unfolding o_assoc apply(subst o_assoc[symmetric], subst o_assoc[symmetric])
      unfolding \<Lambda>6_Inl unfolding \<Sigma>5.map_comp0 F_map_comp o_assoc ..
    qed
  qed
  also have "... = ?R"
  proof(rule sym, rule ext5_unique)
    show "(embL6 ** F_map embL6) \<circ> ddd5 \<circ> leaf5 = leaf6 ** F_map leaf6"
    unfolding o_assoc apply(subst o_assoc[symmetric])
    apply(subst ddd5_def) unfolding ext5_comp_leaf5
    unfolding map_prod.comp unfolding F_map_comp[symmetric]
    apply(subst embL6_def, subst embL6_def) unfolding ext5_comp_leaf5 ..
  next
    show "embL6 ** F_map embL6 \<circ> ddd5 \<circ> \<oo>\<pp>5 =
          <\<oo>\<pp>6 \<circ> Abs_\<Sigma>6 \<circ> Inl \<circ> \<Sigma>5_map fst , F_map (flat6 \<circ> embL6) \<circ> \<Lambda>5> \<circ> \<Sigma>5_map (embL6 ** F_map embL6 \<circ> ddd5)"
    (is "?A = ?B") proof(rule fst_snd_cong)
      show "fst o ?A = fst o ?B"
      unfolding o_assoc fst_convol fst_comp_map_prod
      unfolding o_assoc[symmetric] \<Sigma>5.map_comp0[symmetric] unfolding o_assoc unfolding fst_comp_map_prod
      unfolding o_assoc apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
      apply(subst ddd5_def) unfolding ext5_commute apply(subst ddd5_def[symmetric])
      unfolding o_assoc fst_convol
      apply(subst embL6_def) unfolding ext5_commute apply(subst embL6_def[symmetric])
      unfolding \<Sigma>5.map_comp0 o_assoc ..
    next
      show "snd o ?A = snd o ?B"
      unfolding o_assoc snd_convol snd_comp_map_prod
      unfolding o_assoc apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
      apply(subst ddd5_def) unfolding ext5_commute apply(subst ddd5_def[symmetric])
      unfolding o_assoc apply(subst o_assoc[symmetric]) unfolding snd_convol
      unfolding o_assoc F_map_comp[symmetric]
      unfolding flat6_embL6[symmetric]
      unfolding F_map_comp
      unfolding o_assoc apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
      unfolding \<Lambda>5_natural[symmetric]
      unfolding o_assoc \<Sigma>5.map_comp0 ..
    qed
  qed
  finally show ?thesis .
qed

lemma dd6_embL6: "dd6 \<circ> embL6 = F_map embL6 \<circ> dd5"
unfolding dd6_def dd5_def o_assoc[symmetric] ddd6_embL6 by auto

lemma F_map_embL6_\<Sigma>\<Sigma>5_map:
"F_map embL6 \<circ> dd5 \<circ> \<Sigma>\<Sigma>5_map <id , dtor_J> =
 dd6 \<circ> \<Sigma>\<Sigma>6_map <id , dtor_J> \<circ> embL6"
unfolding o_assoc[symmetric] unfolding embL6_natural[symmetric]
unfolding o_assoc dd6_embL6 ..

lemma eval6_embL6: "eval6 o embL6 = eval5"
unfolding eval5_def apply(rule J.dtor_unfold_unique)
unfolding eval6_def unfolding o_assoc
unfolding dtor_unfold_J_pointfree
unfolding F_map_comp
apply(subst o_assoc[symmetric], subst o_assoc[symmetric])
unfolding F_map_embL6_\<Sigma>\<Sigma>5_map o_assoc ..

theorem alg\<Lambda>6_alg\<Lambda>5_alg\<rho>6:
"alg\<Lambda>6 o Abs_\<Sigma>6 = case_sum alg\<Lambda>5 alg\<rho>6" (is "?L = ?R")
proof(rule sum_comp_cases)
  show "?L o Inl = ?R o Inl"
  unfolding case_sum_o_inj apply(subst dtor_J_o_inj[symmetric])
  unfolding o_assoc dtor_J_alg\<Lambda>6 unfolding Abs_\<Sigma>6_natural o_assoc[symmetric] map_sum_Inl
  unfolding o_assoc apply(subst o_assoc[symmetric], subst o_assoc[symmetric]) unfolding \<Lambda>6_Inl
  unfolding o_assoc F_map_comp[symmetric] eval6_embL6 dtor_J_alg\<Lambda>5 ..
next
  show "?L o Inr = ?R o Inr"
  unfolding alg\<rho>6_def case_sum_o_inj alg\<Lambda>6_def K6_as_\<Sigma>\<Sigma>6_def o_assoc ..
qed

theorem alg\<Lambda>6_Inl: "alg\<Lambda>6 (Abs_\<Sigma>6 (Inl x)) = alg\<Lambda>5 x" (is "?L = ?R")
unfolding o_eq_dest_lhs[OF alg\<Lambda>6_alg\<Lambda>5_alg\<rho>6] by simp

lemma alg\<Lambda>6_Inl_pointfree: "alg\<Lambda>6 o Abs_\<Sigma>6 o Inl = alg\<Lambda>5"
unfolding o_def fun_eq_iff alg\<Lambda>6_Inl by simp

theorem alg\<Lambda>6_Inr: "alg\<Lambda>6 (Abs_\<Sigma>6 (Inr x)) = alg\<rho>6 x" (is "?L = ?R")
unfolding o_eq_dest_lhs[OF alg\<Lambda>6_alg\<Lambda>5_alg\<rho>6] by simp



subsection{* Up-to corecursor with guard not necessarily at the top *}

definition ff6 :: "'a F \<Rightarrow> 'a \<Sigma>6" where "ff6 \<equiv> Abs_\<Sigma>6 o Inl o ff5"

lemma alg\<Lambda>6_ff6: "alg\<Lambda>6 \<circ> ff6 = ctor_J"
unfolding ff6_def o_assoc alg\<Lambda>6_Inl_pointfree alg\<Lambda>5_ff5 ..

lemma ff6_transfer[transfer_rule]: "(F_rel R ===> \<Sigma>6_rel R) ff6 ff6"
unfolding ff6_def by transfer_prover

lemma ff6_natural: "\<Sigma>6_map f o ff6 = ff6 o F_map f"
using ff6_transfer[of "BNF_Def.Grp UNIV f"]
unfolding \<Sigma>6.rel_Grp F_rel_Grp
unfolding Grp_def rel_fun_def by auto

definition gg6 :: "'a \<Sigma>\<Sigma>6 F \<Rightarrow> 'a \<Sigma>\<Sigma>6" where
"gg6 \<equiv> \<oo>\<pp>6 o ff6"

lemma eval6_gg6: "eval6 o gg6 = ctor_J o F_map eval6"
unfolding gg6_def
unfolding o_assoc unfolding eval6_comp_\<oo>\<pp>6
unfolding o_assoc[symmetric] ff6_natural
unfolding o_assoc alg\<Lambda>6_ff6 ..

lemma gg6_transfer[transfer_rule]: "(F_rel (\<Sigma>\<Sigma>6_rel R) ===> \<Sigma>\<Sigma>6_rel R) gg6 gg6"
unfolding gg6_def by transfer_prover

lemma gg6_natural: "\<Sigma>\<Sigma>6_map f o gg6 = gg6 o F_map (\<Sigma>\<Sigma>6_map f)"
using gg6_transfer[of "BNF_Def.Grp UNIV f"]
unfolding \<Sigma>\<Sigma>6.rel_Grp F_rel_Grp
unfolding Grp_def rel_fun_def by auto

definition unfoldUU6 :: "('a \<Rightarrow> 'a \<Sigma>\<Sigma>6 F \<Sigma>\<Sigma>6) \<Rightarrow> 'a \<Rightarrow> J" where
"unfoldUU6 s \<equiv> unfoldU6 (F_map flat6 o dd6 o \<Sigma>\<Sigma>6_map <gg6, id> o s)"

theorem unfoldUU6:
"unfoldUU6 s =
 eval6 o \<Sigma>\<Sigma>6_map (ctor_J o F_map eval6 o F_map (\<Sigma>\<Sigma>6_map (unfoldUU6 s))) o s"
unfolding unfoldUU6_def apply(subst unfoldU6_ctor_J_pointfree[symmetric]) unfolding unfoldUU6_def[symmetric]
unfolding extdd6_def F_map_comp[symmetric] o_assoc
apply(subst o_assoc[symmetric]) unfolding F_map_comp[symmetric]
apply(subst o_assoc[symmetric]) unfolding flat6_natural[symmetric]
apply(subst o_assoc) unfolding eval6_flat6
unfolding F_map_comp
apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
unfolding dd6_natural[symmetric]
unfolding o_assoc apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
unfolding dd6_natural[symmetric]
unfolding o_assoc[symmetric] \<Sigma>\<Sigma>6.map_comp0[symmetric]
unfolding o_assoc eval6_gg6 unfolding \<Sigma>\<Sigma>6.map_comp0 o_assoc
apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric],
      subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
unfolding \<Sigma>\<Sigma>6.map_comp0[symmetric]
apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
unfolding \<Sigma>\<Sigma>6.map_comp0[symmetric] map_prod.comp map_prod_o_convol o_id F_map_comp[symmetric]
apply(rule sym) unfolding o_assoc
apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
unfolding \<Sigma>\<Sigma>6.map_comp0[symmetric] F_map_comp[symmetric] o_assoc[symmetric] gg6_natural
unfolding o_assoc eval6_gg6
apply(rule sym)
apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
unfolding F_map_comp[symmetric] convol_comp_id2 convol_ctor_J_dtor_J
          \<Sigma>\<Sigma>6.map_comp0 o_assoc eval6 ctor_dtor_J_pointfree id_o ..

theorem unfoldUU6_unique:
assumes f: "f = eval6 o \<Sigma>\<Sigma>6_map (ctor_J o F_map eval6 o F_map (\<Sigma>\<Sigma>6_map f)) o s"
shows "f = unfoldUU6 s"
unfolding unfoldUU6_def apply(rule unfoldU6_unique)
apply(rule sym) apply(subst f) unfolding extdd6_def
unfolding o_assoc
apply(subst eval6_def) unfolding dtor_unfold_J_pointfree apply(subst eval6_def[symmetric])
unfolding o_assoc
apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
unfolding o_assoc \<Sigma>\<Sigma>6.map_comp0[symmetric]  convol_o id_o dtor_J_ctor_pointfree F_map_comp[symmetric]
unfolding o_assoc[symmetric] flat6_natural[symmetric]
unfolding o_assoc eval6_flat6 unfolding o_assoc[symmetric] unfolding F_map_comp
apply(rule sym) apply(subst F_map_comp[symmetric], subst \<Sigma>\<Sigma>6.map_comp0[symmetric])
unfolding o_assoc apply(subst o_assoc[symmetric])
unfolding dd6_natural[symmetric]
unfolding o_assoc[symmetric] \<Sigma>\<Sigma>6.map_comp0[symmetric] map_prod_o_convol o_id
unfolding o_assoc[symmetric] gg6_natural
unfolding o_assoc eval6_gg6 F_map_comp ..

(* corecursion: *)
definition corecUU6 :: "('a \<Rightarrow> (J + 'a) \<Sigma>\<Sigma>6 F \<Sigma>\<Sigma>6) \<Rightarrow> 'a \<Rightarrow> J" where
"corecUU6 s \<equiv>
 unfoldUU6 (case_sum (leaf6 o dd6 o leaf6 o <Inl , F_map Inl \<circ> dtor_J>) s) o Inr"

lemma unfoldUU6_Inl:
"unfoldUU6 (case_sum (leaf6 \<circ> dd6 \<circ> leaf6 \<circ> <Inl , F_map Inl \<circ> dtor_J>) s) \<circ> Inl = id"
(is "?L = ?R")
proof-
  have "?L = unfoldUU6 (leaf6 o dd6 o leaf6 o <id, dtor_J>)"
  apply(rule unfoldUU6_unique)
  apply(subst unfoldUU6)
  unfolding o_assoc[symmetric] case_sum_o_inj snd_convol
  unfolding F_map_comp \<Sigma>\<Sigma>6.map_comp0
  unfolding o_assoc
  apply(rule sym)
  unfolding o_assoc
  apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric],
              subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
  apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric],
              subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric],
              subst o_assoc[symmetric])
  unfolding leaf6_natural apply(subst o_assoc[symmetric])
  apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric],
              subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
  unfolding dd6_natural[symmetric]
  apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric],
              subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
  apply(subst o_assoc[symmetric], subst o_assoc[symmetric])
  unfolding leaf6_natural
  unfolding o_assoc[symmetric] map_prod_o_convol o_id ..
  also have "... = ?R"
  apply(rule sym, rule unfoldUU6_unique)
  unfolding \<Sigma>\<Sigma>6.map_id0 F_map_id o_id
  unfolding o_assoc
  apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric],
              subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
  unfolding dd6_leaf6
  unfolding o_assoc[symmetric] snd_convol
  unfolding o_assoc
  apply(subst o_assoc[symmetric])
  unfolding leaf6_natural unfolding o_assoc eval6_leaf6 id_o
  apply(subst o_assoc[symmetric])
  unfolding F_map_comp[symmetric] eval6_leaf6 F_map_id o_id ctor_dtor_J_pointfree ..
  finally show ?thesis .
qed

theorem corecUU6_pointfree:
"corecUU6 s =
 eval6 o \<Sigma>\<Sigma>6_map (ctor_J o F_map eval6 o F_map (\<Sigma>\<Sigma>6_map (case_sum id (corecUU6 s)))) o s"
unfolding corecUU6_def
apply(subst unfoldUU6)
unfolding o_assoc[symmetric] unfolding case_sum_o_inj
apply(subst unfoldUU6_Inl[symmetric, of s])
unfolding o_assoc case_sum_Inl_Inr_L extdd6_def ..

theorem corecUU6_unique:
  assumes f: "f = eval6 o \<Sigma>\<Sigma>6_map (ctor_J o F_map eval6 o F_map (\<Sigma>\<Sigma>6_map (case_sum id f))) o s"
  shows "f = corecUU6 s"
  unfolding corecUU6_def
  apply(rule eq_o_InrI[OF unfoldUU6_Inl unfoldUU6_unique])
  apply (subst f)
  apply (auto simp: fun_eq_iff eval6_leaf6' pre_J.map_comp o_eq_dest[OF dd6_leaf6] convol_def
    leaf6_natural o_assoc case_sum_o_inj(1) eval6_leaf6 pre_J.map_id J.ctor_dtor split: sum.splits)
  done

theorem corecUU6:
"corecUU6 s a =
 eval6 (\<Sigma>\<Sigma>6_map (ctor_J o F_map eval6 o F_map (\<Sigma>\<Sigma>6_map (case_sum id (corecUU6 s)))) (s a))"
using corecUU6_pointfree unfolding o_def fun_eq_iff by(rule allE)

end