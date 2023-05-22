header {* More on corecursion and coinduction up to *}

theory Stream_More_Corec_Upto4
imports Stream_Corec_Upto4
begin


subsection{* A natural-transformation-based version of the up-to corecursion principle *}

definition alg\<rho>4 :: "J K4 \<Rightarrow> J" where "alg\<rho>4 \<equiv> eval4 o K4_as_\<Sigma>\<Sigma>4"

lemma dd4_K4_as_\<Sigma>\<Sigma>4:
"dd4 o K4_as_\<Sigma>\<Sigma>4 = \<rho>4"
unfolding K4_as_\<Sigma>\<Sigma>4_def dd4_def
unfolding o_assoc apply(subst o_assoc[symmetric])
unfolding ddd4_\<oo>\<pp>4 unfolding o_assoc snd_convol
unfolding o_assoc apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
unfolding \<Sigma>4.map_comp0[symmetric] ddd4_leaf4 \<Lambda>4_natural
unfolding o_assoc F_map_comp[symmetric] leaf4_flat4 F_map_id id_o \<Lambda>4_Inr ..

lemma alg\<rho>4: "dtor_J o alg\<rho>4 = F_map eval4 o \<rho>4 o K4_map <id, dtor_J>"
unfolding dd4_K4_as_\<Sigma>\<Sigma>4[symmetric] o_assoc
unfolding o_assoc[symmetric] K4_as_\<Sigma>\<Sigma>4_natural
unfolding o_assoc eval4 alg\<rho>4_def ..

lemma flat4_embL4: "flat4 o embL4 o \<Sigma>\<Sigma>3_map embL4 = embL4 o flat3" (is "?L = ?R")
proof-
  have "?L = ext3 (\<oo>\<pp>4 o Abs_\<Sigma>4 o Inl) embL4"
  proof(rule ext3_unique)
    show "flat4 \<circ> embL4 \<circ> \<Sigma>\<Sigma>3_map embL4 \<circ> leaf3 = embL4"
    unfolding o_assoc[symmetric] unfolding leaf3_natural
    unfolding o_assoc apply(subst o_assoc[symmetric])
    apply(subst embL4_def) unfolding ext3_comp_leaf3 flat4_leaf4 id_o ..
  next
    show "flat4 \<circ> embL4 \<circ> \<Sigma>\<Sigma>3_map embL4 \<circ> \<oo>\<pp>3 = \<oo>\<pp>4 \<circ> Abs_\<Sigma>4 \<circ> Inl \<circ> \<Sigma>3_map (flat4 \<circ> embL4 \<circ> \<Sigma>\<Sigma>3_map embL4)"
    apply(subst o_assoc[symmetric]) unfolding embL4_natural
    unfolding o_assoc apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric],
                            subst o_assoc[symmetric])
    unfolding embL4_def unfolding ext3_commute unfolding embL4_def[symmetric]
    unfolding o_assoc apply(subst o_assoc[symmetric])
    unfolding \<oo>\<pp>4_natural[symmetric]
    unfolding o_assoc apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
    unfolding map_sum_Inl Abs_\<Sigma>4_natural
    unfolding o_assoc[symmetric] map_sum_Inl \<Sigma>3.map_comp0[symmetric] embL4_natural[symmetric]
    apply(rule sym) apply(subst \<Sigma>3.map_comp0) unfolding o_assoc
    unfolding flat4_def unfolding ext4_commute
    apply(rule sym) apply(subst o_assoc[symmetric])
    unfolding Abs_\<Sigma>4_natural unfolding o_assoc[symmetric] map_sum_Inl \<oo>\<pp>4_natural[symmetric] ..
  qed
  also have "... = ?R"
  proof(rule sym, rule ext3_unique)
    show "embL4 \<circ> flat3 \<circ> leaf3 = embL4"
    unfolding o_assoc[symmetric] flat3_leaf3 o_id ..
  next
    show "embL4 \<circ> flat3 \<circ> \<oo>\<pp>3 = \<oo>\<pp>4 \<circ> Abs_\<Sigma>4 \<circ> Inl \<circ> \<Sigma>3_map (embL4 \<circ> flat3)"
    unfolding flat3_def o_assoc[symmetric] ext3_commute
    unfolding o_assoc
    apply(subst embL4_def) unfolding ext3_commute apply(subst embL4_def[symmetric])
    unfolding \<Sigma>3.map_comp0 o_assoc ..
  qed
  finally show ?thesis .
qed

lemma ddd4_embL4: "ddd4 \<circ> embL4 = (embL4 ** F_map embL4) \<circ> ddd3" (is "?L = ?R")
proof-
  have "?L = ext3 <\<oo>\<pp>4 o Abs_\<Sigma>4 o Inl o \<Sigma>3_map fst, F_map (flat4 o embL4) o \<Lambda>3> (leaf4 ** F_map leaf4)"
  proof(rule ext3_unique)
    show "ddd4 \<circ> embL4 \<circ> leaf3 = leaf4 ** F_map leaf4"
    apply(rule fst_snd_cong)
    unfolding fst_comp_map_prod snd_comp_map_prod
    unfolding  embL4_def
    apply (subst (3) o_assoc[symmetric]) defer apply (subst (3) o_assoc[symmetric])
    unfolding ext3_comp_leaf3
    unfolding ddd4_def ext4_comp_leaf4 fst_comp_map_prod snd_comp_map_prod by(rule refl, rule refl)
  next
    show "ddd4 \<circ> embL4 \<circ> \<oo>\<pp>3 =
          <\<oo>\<pp>4 \<circ> Abs_\<Sigma>4 \<circ> Inl \<circ> \<Sigma>3_map fst , F_map (flat4 \<circ> embL4) \<circ> \<Lambda>3> \<circ> \<Sigma>3_map (ddd4 \<circ> embL4)" (is "?A = ?B")
    proof(rule fst_snd_cong)
      show "fst o ?A = fst o ?B"
      unfolding o_assoc fst_convol unfolding o_assoc[symmetric] \<Sigma>3.map_comp0[symmetric]
      unfolding o_assoc
      apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
      apply(subst embL4_def) unfolding ext3_commute apply(subst embL4_def[symmetric])
      unfolding o_assoc apply(subst o_assoc[symmetric])
      apply(subst ddd4_def) unfolding ext4_commute apply(subst ddd4_def[symmetric])
      unfolding o_assoc fst_convol
      apply(subst o_assoc[symmetric]) unfolding \<Sigma>4.map_comp0[symmetric]
      apply(subst o_assoc[symmetric]) unfolding Abs_\<Sigma>4_natural map_sum_Inl o_assoc[symmetric]
      unfolding \<Sigma>3.map_comp0[symmetric] o_assoc ..
    next
      show "snd o ?A = snd o ?B"
      unfolding o_assoc snd_convol unfolding o_assoc[symmetric]
      apply(subst embL4_def) unfolding ext3_commute apply(subst embL4_def[symmetric])
      unfolding o_assoc apply(subst o_assoc[symmetric], subst o_assoc[symmetric])
      apply(subst ddd4_def) unfolding ext4_commute apply(subst ddd4_def[symmetric])
      unfolding o_assoc snd_convol
      unfolding o_assoc apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
      unfolding Abs_\<Sigma>4_natural map_sum_Inl o_assoc[symmetric]
      unfolding o_assoc apply(subst o_assoc[symmetric], subst o_assoc[symmetric])
      unfolding \<Lambda>4_Inl unfolding \<Sigma>3.map_comp0 F_map_comp o_assoc ..
    qed
  qed
  also have "... = ?R"
  proof(rule sym, rule ext3_unique)
    show "(embL4 ** F_map embL4) \<circ> ddd3 \<circ> leaf3 = leaf4 ** F_map leaf4"
    unfolding o_assoc apply(subst o_assoc[symmetric])
    apply(subst ddd3_def) unfolding ext3_comp_leaf3
    unfolding map_prod.comp unfolding F_map_comp[symmetric]
    apply(subst embL4_def, subst embL4_def) unfolding ext3_comp_leaf3 ..
  next
    show "embL4 ** F_map embL4 \<circ> ddd3 \<circ> \<oo>\<pp>3 =
          <\<oo>\<pp>4 \<circ> Abs_\<Sigma>4 \<circ> Inl \<circ> \<Sigma>3_map fst , F_map (flat4 \<circ> embL4) \<circ> \<Lambda>3> \<circ> \<Sigma>3_map (embL4 ** F_map embL4 \<circ> ddd3)"
    (is "?A = ?B") proof(rule fst_snd_cong)
      show "fst o ?A = fst o ?B"
      unfolding o_assoc fst_convol fst_comp_map_prod
      unfolding o_assoc[symmetric] \<Sigma>3.map_comp0[symmetric] unfolding o_assoc unfolding fst_comp_map_prod
      unfolding o_assoc apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
      apply(subst ddd3_def) unfolding ext3_commute apply(subst ddd3_def[symmetric])
      unfolding o_assoc fst_convol
      apply(subst embL4_def) unfolding ext3_commute apply(subst embL4_def[symmetric])
      unfolding \<Sigma>3.map_comp0 o_assoc ..
    next
      show "snd o ?A = snd o ?B"
      unfolding o_assoc snd_convol snd_comp_map_prod
      unfolding o_assoc apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
      apply(subst ddd3_def) unfolding ext3_commute apply(subst ddd3_def[symmetric])
      unfolding o_assoc apply(subst o_assoc[symmetric]) unfolding snd_convol
      unfolding o_assoc F_map_comp[symmetric]
      unfolding flat4_embL4[symmetric]
      unfolding F_map_comp
      unfolding o_assoc apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
      unfolding \<Lambda>3_natural[symmetric]
      unfolding o_assoc \<Sigma>3.map_comp0 ..
    qed
  qed
  finally show ?thesis .
qed

lemma dd4_embL4: "dd4 \<circ> embL4 = F_map embL4 \<circ> dd3"
unfolding dd4_def dd3_def o_assoc[symmetric] ddd4_embL4 by auto

lemma F_map_embL4_\<Sigma>\<Sigma>3_map:
"F_map embL4 \<circ> dd3 \<circ> \<Sigma>\<Sigma>3_map <id , dtor_J> =
 dd4 \<circ> \<Sigma>\<Sigma>4_map <id , dtor_J> \<circ> embL4"
unfolding o_assoc[symmetric] unfolding embL4_natural[symmetric]
unfolding o_assoc dd4_embL4 ..

lemma eval4_embL4: "eval4 o embL4 = eval3"
unfolding eval3_def apply(rule J.dtor_unfold_unique)
unfolding eval4_def unfolding o_assoc
unfolding dtor_unfold_J_pointfree
unfolding F_map_comp
apply(subst o_assoc[symmetric], subst o_assoc[symmetric])
unfolding F_map_embL4_\<Sigma>\<Sigma>3_map o_assoc ..

theorem alg\<Lambda>4_alg\<Lambda>3_alg\<rho>4:
"alg\<Lambda>4 o Abs_\<Sigma>4 = case_sum alg\<Lambda>3 alg\<rho>4" (is "?L = ?R")
proof(rule sum_comp_cases)
  show "?L o Inl = ?R o Inl"
  unfolding case_sum_o_inj apply(subst dtor_J_o_inj[symmetric])
  unfolding o_assoc dtor_J_alg\<Lambda>4 unfolding Abs_\<Sigma>4_natural o_assoc[symmetric] map_sum_Inl
  unfolding o_assoc apply(subst o_assoc[symmetric], subst o_assoc[symmetric]) unfolding \<Lambda>4_Inl
  unfolding o_assoc F_map_comp[symmetric] eval4_embL4 dtor_J_alg\<Lambda>3 ..
next
  show "?L o Inr = ?R o Inr"
  unfolding alg\<rho>4_def case_sum_o_inj alg\<Lambda>4_def K4_as_\<Sigma>\<Sigma>4_def o_assoc ..
qed

theorem alg\<Lambda>4_Inl: "alg\<Lambda>4 (Abs_\<Sigma>4 (Inl x)) = alg\<Lambda>3 x" (is "?L = ?R")
unfolding o_eq_dest_lhs[OF alg\<Lambda>4_alg\<Lambda>3_alg\<rho>4] by simp

lemma alg\<Lambda>4_Inl_pointfree: "alg\<Lambda>4 o Abs_\<Sigma>4 o Inl = alg\<Lambda>3"
unfolding o_def fun_eq_iff alg\<Lambda>4_Inl by simp

theorem alg\<Lambda>4_Inr: "alg\<Lambda>4 (Abs_\<Sigma>4 (Inr x)) = alg\<rho>4 x" (is "?L = ?R")
unfolding o_eq_dest_lhs[OF alg\<Lambda>4_alg\<Lambda>3_alg\<rho>4] by simp



subsection{* Up-to corecursor with guard not necessarily at the top *}

definition ff4 :: "'a F \<Rightarrow> 'a \<Sigma>4" where "ff4 \<equiv> Abs_\<Sigma>4 o Inl o ff3"

lemma alg\<Lambda>4_ff4: "alg\<Lambda>4 \<circ> ff4 = ctor_J"
unfolding ff4_def o_assoc alg\<Lambda>4_Inl_pointfree alg\<Lambda>3_ff3 ..

lemma ff4_transfer[transfer_rule]: "(F_rel R ===> \<Sigma>4_rel R) ff4 ff4"
unfolding ff4_def by transfer_prover

lemma ff4_natural: "\<Sigma>4_map f o ff4 = ff4 o F_map f"
using ff4_transfer[of "BNF_Def.Grp UNIV f"]
unfolding \<Sigma>4.rel_Grp F_rel_Grp
unfolding Grp_def rel_fun_def by auto

definition gg4 :: "'a \<Sigma>\<Sigma>4 F \<Rightarrow> 'a \<Sigma>\<Sigma>4" where
"gg4 \<equiv> \<oo>\<pp>4 o ff4"

lemma eval4_gg4: "eval4 o gg4 = ctor_J o F_map eval4"
unfolding gg4_def
unfolding o_assoc unfolding eval4_comp_\<oo>\<pp>4
unfolding o_assoc[symmetric] ff4_natural
unfolding o_assoc alg\<Lambda>4_ff4 ..

lemma gg4_transfer[transfer_rule]: "(F_rel (\<Sigma>\<Sigma>4_rel R) ===> \<Sigma>\<Sigma>4_rel R) gg4 gg4"
unfolding gg4_def by transfer_prover

lemma gg4_natural: "\<Sigma>\<Sigma>4_map f o gg4 = gg4 o F_map (\<Sigma>\<Sigma>4_map f)"
using gg4_transfer[of "BNF_Def.Grp UNIV f"]
unfolding \<Sigma>\<Sigma>4.rel_Grp F_rel_Grp
unfolding Grp_def rel_fun_def by auto

definition unfoldUU4 :: "('a \<Rightarrow> 'a \<Sigma>\<Sigma>4 F \<Sigma>\<Sigma>4) \<Rightarrow> 'a \<Rightarrow> J" where
"unfoldUU4 s \<equiv> unfoldU4 (F_map flat4 o dd4 o \<Sigma>\<Sigma>4_map <gg4, id> o s)"

theorem unfoldUU4:
"unfoldUU4 s =
 eval4 o \<Sigma>\<Sigma>4_map (ctor_J o F_map eval4 o F_map (\<Sigma>\<Sigma>4_map (unfoldUU4 s))) o s"
unfolding unfoldUU4_def apply(subst unfoldU4_ctor_J_pointfree[symmetric]) unfolding unfoldUU4_def[symmetric]
unfolding extdd4_def F_map_comp[symmetric] o_assoc
apply(subst o_assoc[symmetric]) unfolding F_map_comp[symmetric]
apply(subst o_assoc[symmetric]) unfolding flat4_natural[symmetric]
apply(subst o_assoc) unfolding eval4_flat4
unfolding F_map_comp
apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
unfolding dd4_natural[symmetric]
unfolding o_assoc apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
unfolding dd4_natural[symmetric]
unfolding o_assoc[symmetric] \<Sigma>\<Sigma>4.map_comp0[symmetric]
unfolding o_assoc eval4_gg4 unfolding \<Sigma>\<Sigma>4.map_comp0 o_assoc
apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric],
      subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
unfolding \<Sigma>\<Sigma>4.map_comp0[symmetric]
apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
unfolding \<Sigma>\<Sigma>4.map_comp0[symmetric] map_prod.comp map_prod_o_convol o_id F_map_comp[symmetric]
apply(rule sym) unfolding o_assoc
apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
unfolding \<Sigma>\<Sigma>4.map_comp0[symmetric] F_map_comp[symmetric] o_assoc[symmetric] gg4_natural
unfolding o_assoc eval4_gg4
apply(rule sym)
apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
unfolding F_map_comp[symmetric] convol_comp_id2 convol_ctor_J_dtor_J
          \<Sigma>\<Sigma>4.map_comp0 o_assoc eval4 ctor_dtor_J_pointfree id_o ..

theorem unfoldUU4_unique:
assumes f: "f = eval4 o \<Sigma>\<Sigma>4_map (ctor_J o F_map eval4 o F_map (\<Sigma>\<Sigma>4_map f)) o s"
shows "f = unfoldUU4 s"
unfolding unfoldUU4_def apply(rule unfoldU4_unique)
apply(rule sym) apply(subst f) unfolding extdd4_def
unfolding o_assoc
apply(subst eval4_def) unfolding dtor_unfold_J_pointfree apply(subst eval4_def[symmetric])
unfolding o_assoc
apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
unfolding o_assoc \<Sigma>\<Sigma>4.map_comp0[symmetric]  convol_o id_o dtor_J_ctor_pointfree F_map_comp[symmetric]
unfolding o_assoc[symmetric] flat4_natural[symmetric]
unfolding o_assoc eval4_flat4 unfolding o_assoc[symmetric] unfolding F_map_comp
apply(rule sym) apply(subst F_map_comp[symmetric], subst \<Sigma>\<Sigma>4.map_comp0[symmetric])
unfolding o_assoc apply(subst o_assoc[symmetric])
unfolding dd4_natural[symmetric]
unfolding o_assoc[symmetric] \<Sigma>\<Sigma>4.map_comp0[symmetric] map_prod_o_convol o_id
unfolding o_assoc[symmetric] gg4_natural
unfolding o_assoc eval4_gg4 F_map_comp ..

(* corecursion: *)
definition corecUU4 :: "('a \<Rightarrow> (J + 'a) \<Sigma>\<Sigma>4 F \<Sigma>\<Sigma>4) \<Rightarrow> 'a \<Rightarrow> J" where
"corecUU4 s \<equiv>
 unfoldUU4 (case_sum (leaf4 o dd4 o leaf4 o <Inl , F_map Inl \<circ> dtor_J>) s) o Inr"

lemma unfoldUU4_Inl:
"unfoldUU4 (case_sum (leaf4 \<circ> dd4 \<circ> leaf4 \<circ> <Inl , F_map Inl \<circ> dtor_J>) s) \<circ> Inl = id"
(is "?L = ?R")
proof-
  have "?L = unfoldUU4 (leaf4 o dd4 o leaf4 o <id, dtor_J>)"
  apply(rule unfoldUU4_unique)
  apply(subst unfoldUU4)
  unfolding o_assoc[symmetric] case_sum_o_inj snd_convol
  unfolding F_map_comp \<Sigma>\<Sigma>4.map_comp0
  unfolding o_assoc
  apply(rule sym)
  unfolding o_assoc
  apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric],
              subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
  apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric],
              subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric],
              subst o_assoc[symmetric])
  unfolding leaf4_natural apply(subst o_assoc[symmetric])
  apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric],
              subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
  unfolding dd4_natural[symmetric]
  apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric],
              subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
  apply(subst o_assoc[symmetric], subst o_assoc[symmetric])
  unfolding leaf4_natural
  unfolding o_assoc[symmetric] map_prod_o_convol o_id ..
  also have "... = ?R"
  apply(rule sym, rule unfoldUU4_unique)
  unfolding \<Sigma>\<Sigma>4.map_id0 F_map_id o_id
  unfolding o_assoc
  apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric],
              subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
  unfolding dd4_leaf4
  unfolding o_assoc[symmetric] snd_convol
  unfolding o_assoc
  apply(subst o_assoc[symmetric])
  unfolding leaf4_natural unfolding o_assoc eval4_leaf4 id_o
  apply(subst o_assoc[symmetric])
  unfolding F_map_comp[symmetric] eval4_leaf4 F_map_id o_id ctor_dtor_J_pointfree ..
  finally show ?thesis .
qed

theorem corecUU4_pointfree:
"corecUU4 s =
 eval4 o \<Sigma>\<Sigma>4_map (ctor_J o F_map eval4 o F_map (\<Sigma>\<Sigma>4_map (case_sum id (corecUU4 s)))) o s"
unfolding corecUU4_def
apply(subst unfoldUU4)
unfolding o_assoc[symmetric] unfolding case_sum_o_inj
apply(subst unfoldUU4_Inl[symmetric, of s])
unfolding o_assoc case_sum_Inl_Inr_L extdd4_def ..

theorem corecUU4_unique:
  assumes f: "f = eval4 o \<Sigma>\<Sigma>4_map (ctor_J o F_map eval4 o F_map (\<Sigma>\<Sigma>4_map (case_sum id f))) o s"
  shows "f = corecUU4 s"
  unfolding corecUU4_def
  apply(rule eq_o_InrI[OF unfoldUU4_Inl unfoldUU4_unique])
  apply (subst f)
  apply (auto simp: fun_eq_iff eval4_leaf4' pre_J.map_comp o_eq_dest[OF dd4_leaf4] convol_def
    leaf4_natural o_assoc case_sum_o_inj(1) eval4_leaf4 pre_J.map_id J.ctor_dtor split: sum.splits)
  done

theorem corecUU4:
"corecUU4 s a =
 eval4 (\<Sigma>\<Sigma>4_map (ctor_J o F_map eval4 o F_map (\<Sigma>\<Sigma>4_map (case_sum id (corecUU4 s)))) (s a))"
using corecUU4_pointfree unfolding o_def fun_eq_iff by(rule allE)

end