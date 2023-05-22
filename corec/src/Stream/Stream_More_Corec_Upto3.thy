header {* More on corecursion and coinduction up to *}

theory Stream_More_Corec_Upto3
imports Stream_Corec_Upto3
begin


subsection{* A natural-transformation-based version of the up-to corecursion principle *}

definition alg\<rho>3 :: "J K3 \<Rightarrow> J" where "alg\<rho>3 \<equiv> eval3 o K3_as_\<Sigma>\<Sigma>3"

lemma dd3_K3_as_\<Sigma>\<Sigma>3:
"dd3 o K3_as_\<Sigma>\<Sigma>3 = \<rho>3"
unfolding K3_as_\<Sigma>\<Sigma>3_def dd3_def
unfolding o_assoc apply(subst o_assoc[symmetric])
unfolding ddd3_\<oo>\<pp>3 unfolding o_assoc snd_convol
unfolding o_assoc apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
unfolding \<Sigma>3.map_comp0[symmetric] ddd3_leaf3 \<Lambda>3_natural
unfolding o_assoc F_map_comp[symmetric] leaf3_flat3 F_map_id id_o \<Lambda>3_Inr ..

lemma alg\<rho>3: "dtor_J o alg\<rho>3 = F_map eval3 o \<rho>3 o K3_map <id, dtor_J>"
unfolding dd3_K3_as_\<Sigma>\<Sigma>3[symmetric] o_assoc
unfolding o_assoc[symmetric] K3_as_\<Sigma>\<Sigma>3_natural
unfolding o_assoc eval3 alg\<rho>3_def ..

lemma flat3_embL3: "flat3 o embL3 o \<Sigma>\<Sigma>2_map embL3 = embL3 o flat2" (is "?L = ?R")
proof-
  have "?L = ext2 (\<oo>\<pp>3 o Abs_\<Sigma>3 o Inl) embL3"
  proof(rule ext2_unique)
    show "flat3 \<circ> embL3 \<circ> \<Sigma>\<Sigma>2_map embL3 \<circ> leaf2 = embL3"
    unfolding o_assoc[symmetric] unfolding leaf2_natural
    unfolding o_assoc apply(subst o_assoc[symmetric])
    apply(subst embL3_def) unfolding ext2_comp_leaf2 flat3_leaf3 id_o ..
  next
    show "flat3 \<circ> embL3 \<circ> \<Sigma>\<Sigma>2_map embL3 \<circ> \<oo>\<pp>2 = \<oo>\<pp>3 \<circ> Abs_\<Sigma>3 \<circ> Inl \<circ> \<Sigma>2_map (flat3 \<circ> embL3 \<circ> \<Sigma>\<Sigma>2_map embL3)"
    apply(subst o_assoc[symmetric]) unfolding embL3_natural
    unfolding o_assoc apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric],
                            subst o_assoc[symmetric])
    unfolding embL3_def unfolding ext2_commute unfolding embL3_def[symmetric]
    unfolding o_assoc apply(subst o_assoc[symmetric])
    unfolding \<oo>\<pp>3_natural[symmetric]
    unfolding o_assoc apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
    unfolding map_sum_Inl Abs_\<Sigma>3_natural
    unfolding o_assoc[symmetric] map_sum_Inl \<Sigma>2.map_comp0[symmetric] embL3_natural[symmetric]
    apply(rule sym) apply(subst \<Sigma>2.map_comp0) unfolding o_assoc
    unfolding flat3_def unfolding ext3_commute
    apply(rule sym) apply(subst o_assoc[symmetric])
    unfolding Abs_\<Sigma>3_natural unfolding o_assoc[symmetric] map_sum_Inl \<oo>\<pp>3_natural[symmetric] ..
  qed
  also have "... = ?R"
  proof(rule sym, rule ext2_unique)
    show "embL3 \<circ> flat2 \<circ> leaf2 = embL3"
    unfolding o_assoc[symmetric] flat2_leaf2 o_id ..
  next
    show "embL3 \<circ> flat2 \<circ> \<oo>\<pp>2 = \<oo>\<pp>3 \<circ> Abs_\<Sigma>3 \<circ> Inl \<circ> \<Sigma>2_map (embL3 \<circ> flat2)"
    unfolding flat2_def o_assoc[symmetric] ext2_commute
    unfolding o_assoc
    apply(subst embL3_def) unfolding ext2_commute apply(subst embL3_def[symmetric])
    unfolding \<Sigma>2.map_comp0 o_assoc ..
  qed
  finally show ?thesis .
qed

lemma ddd3_embL3: "ddd3 \<circ> embL3 = (embL3 ** F_map embL3) \<circ> ddd2" (is "?L = ?R")
proof-
  have "?L = ext2 <\<oo>\<pp>3 o Abs_\<Sigma>3 o Inl o \<Sigma>2_map fst, F_map (flat3 o embL3) o \<Lambda>2> (leaf3 ** F_map leaf3)"
  proof(rule ext2_unique)
    show "ddd3 \<circ> embL3 \<circ> leaf2 = leaf3 ** F_map leaf3"
    apply(rule fst_snd_cong)
    unfolding fst_comp_map_prod snd_comp_map_prod
    unfolding  embL3_def
    apply (subst (3) o_assoc[symmetric]) defer apply (subst (3) o_assoc[symmetric])
    unfolding ext2_comp_leaf2
    unfolding ddd3_def ext3_comp_leaf3 fst_comp_map_prod snd_comp_map_prod by(rule refl, rule refl)
  next
    show "ddd3 \<circ> embL3 \<circ> \<oo>\<pp>2 =
          <\<oo>\<pp>3 \<circ> Abs_\<Sigma>3 \<circ> Inl \<circ> \<Sigma>2_map fst , F_map (flat3 \<circ> embL3) \<circ> \<Lambda>2> \<circ> \<Sigma>2_map (ddd3 \<circ> embL3)" (is "?A = ?B")
    proof(rule fst_snd_cong)
      show "fst o ?A = fst o ?B"
      unfolding o_assoc fst_convol unfolding o_assoc[symmetric] \<Sigma>2.map_comp0[symmetric]
      unfolding o_assoc
      apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
      apply(subst embL3_def) unfolding ext2_commute apply(subst embL3_def[symmetric])
      unfolding o_assoc apply(subst o_assoc[symmetric])
      apply(subst ddd3_def) unfolding ext3_commute apply(subst ddd3_def[symmetric])
      unfolding o_assoc fst_convol
      apply(subst o_assoc[symmetric]) unfolding \<Sigma>3.map_comp0[symmetric]
      apply(subst o_assoc[symmetric]) unfolding Abs_\<Sigma>3_natural map_sum_Inl o_assoc[symmetric]
      unfolding \<Sigma>2.map_comp0[symmetric] o_assoc ..
    next
      show "snd o ?A = snd o ?B"
      unfolding o_assoc snd_convol unfolding o_assoc[symmetric]
      apply(subst embL3_def) unfolding ext2_commute apply(subst embL3_def[symmetric])
      unfolding o_assoc apply(subst o_assoc[symmetric], subst o_assoc[symmetric])
      apply(subst ddd3_def) unfolding ext3_commute apply(subst ddd3_def[symmetric])
      unfolding o_assoc snd_convol
      unfolding o_assoc apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
      unfolding Abs_\<Sigma>3_natural map_sum_Inl o_assoc[symmetric]
      unfolding o_assoc apply(subst o_assoc[symmetric], subst o_assoc[symmetric])
      unfolding \<Lambda>3_Inl unfolding \<Sigma>2.map_comp0 F_map_comp o_assoc ..
    qed
  qed
  also have "... = ?R"
  proof(rule sym, rule ext2_unique)
    show "(embL3 ** F_map embL3) \<circ> ddd2 \<circ> leaf2 = leaf3 ** F_map leaf3"
    unfolding o_assoc apply(subst o_assoc[symmetric])
    apply(subst ddd2_def) unfolding ext2_comp_leaf2
    unfolding map_prod.comp unfolding F_map_comp[symmetric]
    apply(subst embL3_def, subst embL3_def) unfolding ext2_comp_leaf2 ..
  next
    show "embL3 ** F_map embL3 \<circ> ddd2 \<circ> \<oo>\<pp>2 =
          <\<oo>\<pp>3 \<circ> Abs_\<Sigma>3 \<circ> Inl \<circ> \<Sigma>2_map fst , F_map (flat3 \<circ> embL3) \<circ> \<Lambda>2> \<circ> \<Sigma>2_map (embL3 ** F_map embL3 \<circ> ddd2)"
    (is "?A = ?B") proof(rule fst_snd_cong)
      show "fst o ?A = fst o ?B"
      unfolding o_assoc fst_convol fst_comp_map_prod
      unfolding o_assoc[symmetric] \<Sigma>2.map_comp0[symmetric] unfolding o_assoc unfolding fst_comp_map_prod
      unfolding o_assoc apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
      apply(subst ddd2_def) unfolding ext2_commute apply(subst ddd2_def[symmetric])
      unfolding o_assoc fst_convol
      apply(subst embL3_def) unfolding ext2_commute apply(subst embL3_def[symmetric])
      unfolding \<Sigma>2.map_comp0 o_assoc ..
    next
      show "snd o ?A = snd o ?B"
      unfolding o_assoc snd_convol snd_comp_map_prod
      unfolding o_assoc apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
      apply(subst ddd2_def) unfolding ext2_commute apply(subst ddd2_def[symmetric])
      unfolding o_assoc apply(subst o_assoc[symmetric]) unfolding snd_convol
      unfolding o_assoc F_map_comp[symmetric]
      unfolding flat3_embL3[symmetric]
      unfolding F_map_comp
      unfolding o_assoc apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
      unfolding \<Lambda>2_natural[symmetric]
      unfolding o_assoc \<Sigma>2.map_comp0 ..
    qed
  qed
  finally show ?thesis .
qed

lemma dd3_embL3: "dd3 \<circ> embL3 = F_map embL3 \<circ> dd2"
unfolding dd3_def dd2_def o_assoc[symmetric] ddd3_embL3 by auto

lemma F_map_embL3_\<Sigma>\<Sigma>2_map:
"F_map embL3 \<circ> dd2 \<circ> \<Sigma>\<Sigma>2_map <id , dtor_J> =
 dd3 \<circ> \<Sigma>\<Sigma>3_map <id , dtor_J> \<circ> embL3"
unfolding o_assoc[symmetric] unfolding embL3_natural[symmetric]
unfolding o_assoc dd3_embL3 ..

lemma eval3_embL3: "eval3 o embL3 = eval2"
unfolding eval2_def apply(rule J.dtor_unfold_unique)
unfolding eval3_def unfolding o_assoc
unfolding dtor_unfold_J_pointfree
unfolding F_map_comp
apply(subst o_assoc[symmetric], subst o_assoc[symmetric])
unfolding F_map_embL3_\<Sigma>\<Sigma>2_map o_assoc ..

theorem alg\<Lambda>3_alg\<Lambda>2_alg\<rho>3:
"alg\<Lambda>3 o Abs_\<Sigma>3 = case_sum alg\<Lambda>2 alg\<rho>3" (is "?L = ?R")
proof(rule sum_comp_cases)
  show "?L o Inl = ?R o Inl"
  unfolding case_sum_o_inj apply(subst dtor_J_o_inj[symmetric])
  unfolding o_assoc dtor_J_alg\<Lambda>3 unfolding Abs_\<Sigma>3_natural o_assoc[symmetric] map_sum_Inl
  unfolding o_assoc apply(subst o_assoc[symmetric], subst o_assoc[symmetric]) unfolding \<Lambda>3_Inl
  unfolding o_assoc F_map_comp[symmetric] eval3_embL3 dtor_J_alg\<Lambda>2 ..
next
  show "?L o Inr = ?R o Inr"
  unfolding alg\<rho>3_def case_sum_o_inj alg\<Lambda>3_def K3_as_\<Sigma>\<Sigma>3_def o_assoc ..
qed

theorem alg\<Lambda>3_Inl: "alg\<Lambda>3 (Abs_\<Sigma>3 (Inl x)) = alg\<Lambda>2 x" (is "?L = ?R")
unfolding o_eq_dest_lhs[OF alg\<Lambda>3_alg\<Lambda>2_alg\<rho>3] by simp

lemma alg\<Lambda>3_Inl_pointfree: "alg\<Lambda>3 o Abs_\<Sigma>3 o Inl = alg\<Lambda>2"
unfolding o_def fun_eq_iff alg\<Lambda>3_Inl by simp

theorem alg\<Lambda>3_Inr: "alg\<Lambda>3 (Abs_\<Sigma>3 (Inr x)) = alg\<rho>3 x" (is "?L = ?R")
unfolding o_eq_dest_lhs[OF alg\<Lambda>3_alg\<Lambda>2_alg\<rho>3] by simp



subsection{* Up-to corecursor with guard not necessarily at the top *}

definition ff3 :: "'a F \<Rightarrow> 'a \<Sigma>3" where "ff3 \<equiv> Abs_\<Sigma>3 o Inl o ff2"

lemma alg\<Lambda>3_ff3: "alg\<Lambda>3 \<circ> ff3 = ctor_J"
unfolding ff3_def o_assoc alg\<Lambda>3_Inl_pointfree alg\<Lambda>2_ff2 ..

lemma ff3_transfer[transfer_rule]: "(F_rel R ===> \<Sigma>3_rel R) ff3 ff3"
unfolding ff3_def by transfer_prover

lemma ff3_natural: "\<Sigma>3_map f o ff3 = ff3 o F_map f"
using ff3_transfer[of "BNF_Def.Grp UNIV f"]
unfolding \<Sigma>3.rel_Grp F_rel_Grp
unfolding Grp_def rel_fun_def by auto

definition gg3 :: "'a \<Sigma>\<Sigma>3 F \<Rightarrow> 'a \<Sigma>\<Sigma>3" where
"gg3 \<equiv> \<oo>\<pp>3 o ff3"

lemma eval3_gg3: "eval3 o gg3 = ctor_J o F_map eval3"
unfolding gg3_def
unfolding o_assoc unfolding eval3_comp_\<oo>\<pp>3
unfolding o_assoc[symmetric] ff3_natural
unfolding o_assoc alg\<Lambda>3_ff3 ..

lemma gg3_transfer[transfer_rule]: "(F_rel (\<Sigma>\<Sigma>3_rel R) ===> \<Sigma>\<Sigma>3_rel R) gg3 gg3"
unfolding gg3_def by transfer_prover

lemma gg3_natural: "\<Sigma>\<Sigma>3_map f o gg3 = gg3 o F_map (\<Sigma>\<Sigma>3_map f)"
using gg3_transfer[of "BNF_Def.Grp UNIV f"]
unfolding \<Sigma>\<Sigma>3.rel_Grp F_rel_Grp
unfolding Grp_def rel_fun_def by auto

definition unfoldUU3 :: "('a \<Rightarrow> 'a \<Sigma>\<Sigma>3 F \<Sigma>\<Sigma>3) \<Rightarrow> 'a \<Rightarrow> J" where
"unfoldUU3 s \<equiv> unfoldU3 (F_map flat3 o dd3 o \<Sigma>\<Sigma>3_map <gg3, id> o s)"

theorem unfoldUU3:
"unfoldUU3 s =
 eval3 o \<Sigma>\<Sigma>3_map (ctor_J o F_map eval3 o F_map (\<Sigma>\<Sigma>3_map (unfoldUU3 s))) o s"
unfolding unfoldUU3_def apply(subst unfoldU3_ctor_J_pointfree[symmetric]) unfolding unfoldUU3_def[symmetric]
unfolding extdd3_def F_map_comp[symmetric] o_assoc
apply(subst o_assoc[symmetric]) unfolding F_map_comp[symmetric]
apply(subst o_assoc[symmetric]) unfolding flat3_natural[symmetric]
apply(subst o_assoc) unfolding eval3_flat3
unfolding F_map_comp
apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
unfolding dd3_natural[symmetric]
unfolding o_assoc apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
unfolding dd3_natural[symmetric]
unfolding o_assoc[symmetric] \<Sigma>\<Sigma>3.map_comp0[symmetric]
unfolding o_assoc eval3_gg3 unfolding \<Sigma>\<Sigma>3.map_comp0 o_assoc
apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric],
      subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
unfolding \<Sigma>\<Sigma>3.map_comp0[symmetric]
apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
unfolding \<Sigma>\<Sigma>3.map_comp0[symmetric] map_prod.comp map_prod_o_convol o_id F_map_comp[symmetric]
apply(rule sym) unfolding o_assoc
apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
unfolding \<Sigma>\<Sigma>3.map_comp0[symmetric] F_map_comp[symmetric] o_assoc[symmetric] gg3_natural
unfolding o_assoc eval3_gg3
apply(rule sym)
apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
unfolding F_map_comp[symmetric] convol_comp_id2 convol_ctor_J_dtor_J
          \<Sigma>\<Sigma>3.map_comp0 o_assoc eval3 ctor_dtor_J_pointfree id_o ..

theorem unfoldUU3_unique:
assumes f: "f = eval3 o \<Sigma>\<Sigma>3_map (ctor_J o F_map eval3 o F_map (\<Sigma>\<Sigma>3_map f)) o s"
shows "f = unfoldUU3 s"
unfolding unfoldUU3_def apply(rule unfoldU3_unique)
apply(rule sym) apply(subst f) unfolding extdd3_def
unfolding o_assoc
apply(subst eval3_def) unfolding dtor_unfold_J_pointfree apply(subst eval3_def[symmetric])
unfolding o_assoc
apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
unfolding o_assoc \<Sigma>\<Sigma>3.map_comp0[symmetric]  convol_o id_o dtor_J_ctor_pointfree F_map_comp[symmetric]
unfolding o_assoc[symmetric] flat3_natural[symmetric]
unfolding o_assoc eval3_flat3 unfolding o_assoc[symmetric] unfolding F_map_comp
apply(rule sym) apply(subst F_map_comp[symmetric], subst \<Sigma>\<Sigma>3.map_comp0[symmetric])
unfolding o_assoc apply(subst o_assoc[symmetric])
unfolding dd3_natural[symmetric]
unfolding o_assoc[symmetric] \<Sigma>\<Sigma>3.map_comp0[symmetric] map_prod_o_convol o_id
unfolding o_assoc[symmetric] gg3_natural
unfolding o_assoc eval3_gg3 F_map_comp ..

(* corecursion: *)
definition corecUU3 :: "('a \<Rightarrow> (J + 'a) \<Sigma>\<Sigma>3 F \<Sigma>\<Sigma>3) \<Rightarrow> 'a \<Rightarrow> J" where
"corecUU3 s \<equiv>
 unfoldUU3 (case_sum (leaf3 o dd3 o leaf3 o <Inl , F_map Inl \<circ> dtor_J>) s) o Inr"

lemma unfoldUU3_Inl:
"unfoldUU3 (case_sum (leaf3 \<circ> dd3 \<circ> leaf3 \<circ> <Inl , F_map Inl \<circ> dtor_J>) s) \<circ> Inl = id"
(is "?L = ?R")
proof-
  have "?L = unfoldUU3 (leaf3 o dd3 o leaf3 o <id, dtor_J>)"
  apply(rule unfoldUU3_unique)
  apply(subst unfoldUU3)
  unfolding o_assoc[symmetric] case_sum_o_inj snd_convol
  unfolding F_map_comp \<Sigma>\<Sigma>3.map_comp0
  unfolding o_assoc
  apply(rule sym)
  unfolding o_assoc
  apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric],
              subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
  apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric],
              subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric],
              subst o_assoc[symmetric])
  unfolding leaf3_natural apply(subst o_assoc[symmetric])
  apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric],
              subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
  unfolding dd3_natural[symmetric]
  apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric],
              subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
  apply(subst o_assoc[symmetric], subst o_assoc[symmetric])
  unfolding leaf3_natural
  unfolding o_assoc[symmetric] map_prod_o_convol o_id ..
  also have "... = ?R"
  apply(rule sym, rule unfoldUU3_unique)
  unfolding \<Sigma>\<Sigma>3.map_id0 F_map_id o_id
  unfolding o_assoc
  apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric],
              subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
  unfolding dd3_leaf3
  unfolding o_assoc[symmetric] snd_convol
  unfolding o_assoc
  apply(subst o_assoc[symmetric])
  unfolding leaf3_natural unfolding o_assoc eval3_leaf3 id_o
  apply(subst o_assoc[symmetric])
  unfolding F_map_comp[symmetric] eval3_leaf3 F_map_id o_id ctor_dtor_J_pointfree ..
  finally show ?thesis .
qed

theorem corecUU3_pointfree:
"corecUU3 s =
 eval3 o \<Sigma>\<Sigma>3_map (ctor_J o F_map eval3 o F_map (\<Sigma>\<Sigma>3_map (case_sum id (corecUU3 s)))) o s"
unfolding corecUU3_def
apply(subst unfoldUU3)
unfolding o_assoc[symmetric] unfolding case_sum_o_inj
apply(subst unfoldUU3_Inl[symmetric, of s])
unfolding o_assoc case_sum_Inl_Inr_L extdd3_def ..

theorem corecUU3_unique:
  assumes f: "f = eval3 o \<Sigma>\<Sigma>3_map (ctor_J o F_map eval3 o F_map (\<Sigma>\<Sigma>3_map (case_sum id f))) o s"
  shows "f = corecUU3 s"
  unfolding corecUU3_def
  apply(rule eq_o_InrI[OF unfoldUU3_Inl unfoldUU3_unique])
  apply (subst f)
  apply (auto simp: fun_eq_iff eval3_leaf3' pre_J.map_comp o_eq_dest[OF dd3_leaf3] convol_def
    leaf3_natural o_assoc case_sum_o_inj(1) eval3_leaf3 pre_J.map_id J.ctor_dtor split: sum.splits)
  done

theorem corecUU3:
"corecUU3 s a =
 eval3 (\<Sigma>\<Sigma>3_map (ctor_J o F_map eval3 o F_map (\<Sigma>\<Sigma>3_map (case_sum id (corecUU3 s)))) (s a))"
using corecUU3_pointfree unfolding o_def fun_eq_iff by(rule allE)

end