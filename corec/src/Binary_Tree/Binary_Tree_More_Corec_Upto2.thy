header {* More on corecursion and coinduction up to *}

theory Binary_Tree_More_Corec_Upto2
imports Binary_Tree_Corec_Upto2
begin


subsection{* A natural-transformation-based version of the up-to corecursion principle *}

definition alg\<rho>2 :: "J K2 \<Rightarrow> J" where "alg\<rho>2 \<equiv> eval2 o K2_as_\<Sigma>\<Sigma>2"

lemma dd2_K2_as_\<Sigma>\<Sigma>2:
"dd2 o K2_as_\<Sigma>\<Sigma>2 = \<rho>2"
unfolding K2_as_\<Sigma>\<Sigma>2_def dd2_def
unfolding o_assoc apply(subst o_assoc[symmetric])
unfolding ddd2_\<oo>\<pp>2 unfolding o_assoc snd_convol
unfolding o_assoc apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
unfolding \<Sigma>2.map_comp0[symmetric] ddd2_leaf2 \<Lambda>2_natural
unfolding o_assoc F_map_comp[symmetric] leaf2_flat2 F_map_id id_o \<Lambda>2_Inr ..

lemma alg\<rho>2: "dtor_J o alg\<rho>2 = F_map eval2 o \<rho>2 o K2_map <id, dtor_J>"
unfolding dd2_K2_as_\<Sigma>\<Sigma>2[symmetric] o_assoc
unfolding o_assoc[symmetric] K2_as_\<Sigma>\<Sigma>2_natural
unfolding o_assoc eval2 alg\<rho>2_def ..

lemma flat2_embL2: "flat2 o embL2 o \<Sigma>\<Sigma>1_map embL2 = embL2 o flat1" (is "?L = ?R")
proof-
  have "?L = ext1 (\<oo>\<pp>2 o Abs_\<Sigma>2 o Inl) embL2"
  proof(rule ext1_unique)
    show "flat2 \<circ> embL2 \<circ> \<Sigma>\<Sigma>1_map embL2 \<circ> leaf1 = embL2"
    unfolding o_assoc[symmetric] unfolding leaf1_natural
    unfolding o_assoc apply(subst o_assoc[symmetric])
    apply(subst embL2_def) unfolding ext1_comp_leaf1 flat2_leaf2 id_o ..
  next
    show "flat2 \<circ> embL2 \<circ> \<Sigma>\<Sigma>1_map embL2 \<circ> \<oo>\<pp>1 = \<oo>\<pp>2 \<circ> Abs_\<Sigma>2 \<circ> Inl \<circ> \<Sigma>1_map (flat2 \<circ> embL2 \<circ> \<Sigma>\<Sigma>1_map embL2)"
    apply(subst o_assoc[symmetric]) unfolding embL2_natural
    unfolding o_assoc apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric],
                            subst o_assoc[symmetric])
    unfolding embL2_def unfolding ext1_commute unfolding embL2_def[symmetric]
    unfolding o_assoc apply(subst o_assoc[symmetric])
    unfolding \<oo>\<pp>2_natural[symmetric]
    unfolding o_assoc apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
    unfolding map_sum_Inl Abs_\<Sigma>2_natural
    unfolding o_assoc[symmetric] map_sum_Inl \<Sigma>1.map_comp0[symmetric] embL2_natural[symmetric]
    apply(rule sym) apply(subst \<Sigma>1.map_comp0) unfolding o_assoc
    unfolding flat2_def unfolding ext2_commute
    apply(rule sym) apply(subst o_assoc[symmetric])
    unfolding Abs_\<Sigma>2_natural unfolding o_assoc[symmetric] map_sum_Inl \<oo>\<pp>2_natural[symmetric] ..
  qed
  also have "... = ?R"
  proof(rule sym, rule ext1_unique)
    show "embL2 \<circ> flat1 \<circ> leaf1 = embL2"
    unfolding o_assoc[symmetric] flat1_leaf1 o_id ..
  next
    show "embL2 \<circ> flat1 \<circ> \<oo>\<pp>1 = \<oo>\<pp>2 \<circ> Abs_\<Sigma>2 \<circ> Inl \<circ> \<Sigma>1_map (embL2 \<circ> flat1)"
    unfolding flat1_def o_assoc[symmetric] ext1_commute
    unfolding o_assoc
    apply(subst embL2_def) unfolding ext1_commute apply(subst embL2_def[symmetric])
    unfolding \<Sigma>1.map_comp0 o_assoc ..
  qed
  finally show ?thesis .
qed

lemma ddd2_embL2: "ddd2 \<circ> embL2 = (embL2 ** F_map embL2) \<circ> ddd1" (is "?L = ?R")
proof-
  have "?L = ext1 <\<oo>\<pp>2 o Abs_\<Sigma>2 o Inl o \<Sigma>1_map fst, F_map (flat2 o embL2) o \<Lambda>1> (leaf2 ** F_map leaf2)"
  proof(rule ext1_unique)
    show "ddd2 \<circ> embL2 \<circ> leaf1 = leaf2 ** F_map leaf2"
    apply(rule fst_snd_cong)
    unfolding fst_comp_map_prod snd_comp_map_prod
    unfolding  embL2_def
    apply (subst (3) o_assoc[symmetric]) defer apply (subst (3) o_assoc[symmetric])
    unfolding ext1_comp_leaf1
    unfolding ddd2_def ext2_comp_leaf2 fst_comp_map_prod snd_comp_map_prod by(rule refl, rule refl)
  next
    show "ddd2 \<circ> embL2 \<circ> \<oo>\<pp>1 =
          <\<oo>\<pp>2 \<circ> Abs_\<Sigma>2 \<circ> Inl \<circ> \<Sigma>1_map fst , F_map (flat2 \<circ> embL2) \<circ> \<Lambda>1> \<circ> \<Sigma>1_map (ddd2 \<circ> embL2)" (is "?A = ?B")
    proof(rule fst_snd_cong)
      show "fst o ?A = fst o ?B"
      unfolding o_assoc fst_convol unfolding o_assoc[symmetric] \<Sigma>1.map_comp0[symmetric]
      unfolding o_assoc
      apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
      apply(subst embL2_def) unfolding ext1_commute apply(subst embL2_def[symmetric])
      unfolding o_assoc apply(subst o_assoc[symmetric])
      apply(subst ddd2_def) unfolding ext2_commute apply(subst ddd2_def[symmetric])
      unfolding o_assoc fst_convol
      apply(subst o_assoc[symmetric]) unfolding \<Sigma>2.map_comp0[symmetric]
      apply(subst o_assoc[symmetric]) unfolding Abs_\<Sigma>2_natural map_sum_Inl o_assoc[symmetric]
      unfolding \<Sigma>1.map_comp0[symmetric] o_assoc ..
    next
      show "snd o ?A = snd o ?B"
      unfolding o_assoc snd_convol unfolding o_assoc[symmetric]
      apply(subst embL2_def) unfolding ext1_commute apply(subst embL2_def[symmetric])
      unfolding o_assoc apply(subst o_assoc[symmetric], subst o_assoc[symmetric])
      apply(subst ddd2_def) unfolding ext2_commute apply(subst ddd2_def[symmetric])
      unfolding o_assoc snd_convol
      unfolding o_assoc apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
      unfolding Abs_\<Sigma>2_natural map_sum_Inl o_assoc[symmetric]
      unfolding o_assoc apply(subst o_assoc[symmetric], subst o_assoc[symmetric])
      unfolding \<Lambda>2_Inl unfolding \<Sigma>1.map_comp0 F_map_comp o_assoc ..
    qed
  qed
  also have "... = ?R"
  proof(rule sym, rule ext1_unique)
    show "(embL2 ** F_map embL2) \<circ> ddd1 \<circ> leaf1 = leaf2 ** F_map leaf2"
    unfolding o_assoc apply(subst o_assoc[symmetric])
    apply(subst ddd1_def) unfolding ext1_comp_leaf1
    unfolding map_prod.comp unfolding F_map_comp[symmetric]
    apply(subst embL2_def, subst embL2_def) unfolding ext1_comp_leaf1 ..
  next
    show "embL2 ** F_map embL2 \<circ> ddd1 \<circ> \<oo>\<pp>1 =
          <\<oo>\<pp>2 \<circ> Abs_\<Sigma>2 \<circ> Inl \<circ> \<Sigma>1_map fst , F_map (flat2 \<circ> embL2) \<circ> \<Lambda>1> \<circ> \<Sigma>1_map (embL2 ** F_map embL2 \<circ> ddd1)"
    (is "?A = ?B") proof(rule fst_snd_cong)
      show "fst o ?A = fst o ?B"
      unfolding o_assoc fst_convol fst_comp_map_prod
      unfolding o_assoc[symmetric] \<Sigma>1.map_comp0[symmetric] unfolding o_assoc unfolding fst_comp_map_prod
      unfolding o_assoc apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
      apply(subst ddd1_def) unfolding ext1_commute apply(subst ddd1_def[symmetric])
      unfolding o_assoc fst_convol
      apply(subst embL2_def) unfolding ext1_commute apply(subst embL2_def[symmetric])
      unfolding \<Sigma>1.map_comp0 o_assoc ..
    next
      show "snd o ?A = snd o ?B"
      unfolding o_assoc snd_convol snd_comp_map_prod
      unfolding o_assoc apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
      apply(subst ddd1_def) unfolding ext1_commute apply(subst ddd1_def[symmetric])
      unfolding o_assoc apply(subst o_assoc[symmetric]) unfolding snd_convol
      unfolding o_assoc F_map_comp[symmetric]
      unfolding flat2_embL2[symmetric]
      unfolding F_map_comp
      unfolding o_assoc apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
      unfolding \<Lambda>1_natural[symmetric]
      unfolding o_assoc \<Sigma>1.map_comp0 ..
    qed
  qed
  finally show ?thesis .
qed

lemma dd2_embL2: "dd2 \<circ> embL2 = F_map embL2 \<circ> dd1"
unfolding dd2_def dd1_def o_assoc[symmetric] ddd2_embL2 by auto

lemma F_map_embL2_\<Sigma>\<Sigma>1_map:
"F_map embL2 \<circ> dd1 \<circ> \<Sigma>\<Sigma>1_map <id , dtor_J> =
 dd2 \<circ> \<Sigma>\<Sigma>2_map <id , dtor_J> \<circ> embL2"
unfolding o_assoc[symmetric] unfolding embL2_natural[symmetric]
unfolding o_assoc dd2_embL2 ..

lemma eval2_embL2: "eval2 o embL2 = eval1"
unfolding eval1_def apply(rule J.dtor_unfold_unique)
unfolding eval2_def unfolding o_assoc
unfolding dtor_unfold_J_pointfree
unfolding F_map_comp
apply(subst o_assoc[symmetric], subst o_assoc[symmetric])
unfolding F_map_embL2_\<Sigma>\<Sigma>1_map o_assoc ..

theorem alg\<Lambda>2_alg\<Lambda>1_alg\<rho>2:
"alg\<Lambda>2 o Abs_\<Sigma>2 = case_sum alg\<Lambda>1 alg\<rho>2" (is "?L = ?R")
proof(rule sum_comp_cases)
  show "?L o Inl = ?R o Inl"
  unfolding case_sum_o_inj apply(subst dtor_J_o_inj[symmetric])
  unfolding o_assoc dtor_J_alg\<Lambda>2 unfolding Abs_\<Sigma>2_natural o_assoc[symmetric] map_sum_Inl
  unfolding o_assoc apply(subst o_assoc[symmetric], subst o_assoc[symmetric]) unfolding \<Lambda>2_Inl
  unfolding o_assoc F_map_comp[symmetric] eval2_embL2 dtor_J_alg\<Lambda>1 ..
next
  show "?L o Inr = ?R o Inr"
  unfolding alg\<rho>2_def case_sum_o_inj alg\<Lambda>2_def K2_as_\<Sigma>\<Sigma>2_def o_assoc ..
qed

theorem alg\<Lambda>2_Inl: "alg\<Lambda>2 (Abs_\<Sigma>2 (Inl x)) = alg\<Lambda>1 x" (is "?L = ?R")
unfolding o_eq_dest_lhs[OF alg\<Lambda>2_alg\<Lambda>1_alg\<rho>2] by simp

lemma alg\<Lambda>2_Inl_pointfree: "alg\<Lambda>2 o Abs_\<Sigma>2 o Inl = alg\<Lambda>1"
unfolding o_def fun_eq_iff alg\<Lambda>2_Inl by simp

theorem alg\<Lambda>2_Inr: "alg\<Lambda>2 (Abs_\<Sigma>2 (Inr x)) = alg\<rho>2 x" (is "?L = ?R")
unfolding o_eq_dest_lhs[OF alg\<Lambda>2_alg\<Lambda>1_alg\<rho>2] by simp



subsection{* Up-to corecursor with guard not necessarily at the top *}

definition ff2 :: "'a F \<Rightarrow> 'a \<Sigma>2" where "ff2 \<equiv> Abs_\<Sigma>2 o Inl o ff1"

lemma alg\<Lambda>2_ff2: "alg\<Lambda>2 \<circ> ff2 = ctor_J"
unfolding ff2_def o_assoc alg\<Lambda>2_Inl_pointfree alg\<Lambda>1_ff1 ..

lemma ff2_transfer[transfer_rule]: "(F_rel R ===> \<Sigma>2_rel R) ff2 ff2"
unfolding ff2_def by transfer_prover

lemma ff2_natural: "\<Sigma>2_map f o ff2 = ff2 o F_map f"
using ff2_transfer[of "BNF_Def.Grp UNIV f"]
unfolding \<Sigma>2.rel_Grp F_rel_Grp
unfolding Grp_def rel_fun_def by auto

definition gg2 :: "'a \<Sigma>\<Sigma>2 F \<Rightarrow> 'a \<Sigma>\<Sigma>2" where
"gg2 \<equiv> \<oo>\<pp>2 o ff2"

lemma eval2_gg2: "eval2 o gg2 = ctor_J o F_map eval2"
unfolding gg2_def
unfolding o_assoc unfolding eval2_comp_\<oo>\<pp>2
unfolding o_assoc[symmetric] ff2_natural
unfolding o_assoc alg\<Lambda>2_ff2 ..

lemma gg2_transfer[transfer_rule]: "(F_rel (\<Sigma>\<Sigma>2_rel R) ===> \<Sigma>\<Sigma>2_rel R) gg2 gg2"
unfolding gg2_def by transfer_prover

lemma gg2_natural: "\<Sigma>\<Sigma>2_map f o gg2 = gg2 o F_map (\<Sigma>\<Sigma>2_map f)"
using gg2_transfer[of "BNF_Def.Grp UNIV f"]
unfolding \<Sigma>\<Sigma>2.rel_Grp F_rel_Grp
unfolding Grp_def rel_fun_def by auto

definition unfoldUU2 :: "('a \<Rightarrow> 'a \<Sigma>\<Sigma>2 F \<Sigma>\<Sigma>2) \<Rightarrow> 'a \<Rightarrow> J" where
"unfoldUU2 s \<equiv> unfoldU2 (F_map flat2 o dd2 o \<Sigma>\<Sigma>2_map <gg2, id> o s)"

theorem unfoldUU2:
"unfoldUU2 s =
 eval2 o \<Sigma>\<Sigma>2_map (ctor_J o F_map eval2 o F_map (\<Sigma>\<Sigma>2_map (unfoldUU2 s))) o s"
unfolding unfoldUU2_def apply(subst unfoldU2_ctor_J_pointfree[symmetric]) unfolding unfoldUU2_def[symmetric]
unfolding extdd2_def F_map_comp[symmetric] o_assoc
apply(subst o_assoc[symmetric]) unfolding F_map_comp[symmetric]
apply(subst o_assoc[symmetric]) unfolding flat2_natural[symmetric]
apply(subst o_assoc) unfolding eval2_flat2
unfolding F_map_comp
apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
unfolding dd2_natural[symmetric]
unfolding o_assoc apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
unfolding dd2_natural[symmetric]
unfolding o_assoc[symmetric] \<Sigma>\<Sigma>2.map_comp0[symmetric]
unfolding o_assoc eval2_gg2 unfolding \<Sigma>\<Sigma>2.map_comp0 o_assoc
apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric],
      subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
unfolding \<Sigma>\<Sigma>2.map_comp0[symmetric]
apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
unfolding \<Sigma>\<Sigma>2.map_comp0[symmetric] map_prod.comp map_prod_o_convol o_id F_map_comp[symmetric]
apply(rule sym) unfolding o_assoc
apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
unfolding \<Sigma>\<Sigma>2.map_comp0[symmetric] F_map_comp[symmetric] o_assoc[symmetric] gg2_natural
unfolding o_assoc eval2_gg2
apply(rule sym)
apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
unfolding F_map_comp[symmetric] convol_comp_id2 convol_ctor_J_dtor_J
          \<Sigma>\<Sigma>2.map_comp0 o_assoc eval2 ctor_dtor_J_pointfree id_o ..

theorem unfoldUU2_unique:
assumes f: "f = eval2 o \<Sigma>\<Sigma>2_map (ctor_J o F_map eval2 o F_map (\<Sigma>\<Sigma>2_map f)) o s"
shows "f = unfoldUU2 s"
unfolding unfoldUU2_def apply(rule unfoldU2_unique)
apply(rule sym) apply(subst f) unfolding extdd2_def
unfolding o_assoc
apply(subst eval2_def) unfolding dtor_unfold_J_pointfree apply(subst eval2_def[symmetric])
unfolding o_assoc
apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
unfolding o_assoc \<Sigma>\<Sigma>2.map_comp0[symmetric]  convol_o id_o dtor_J_ctor_pointfree F_map_comp[symmetric]
unfolding o_assoc[symmetric] flat2_natural[symmetric]
unfolding o_assoc eval2_flat2 unfolding o_assoc[symmetric] unfolding F_map_comp
apply(rule sym) apply(subst F_map_comp[symmetric], subst \<Sigma>\<Sigma>2.map_comp0[symmetric])
unfolding o_assoc apply(subst o_assoc[symmetric])
unfolding dd2_natural[symmetric]
unfolding o_assoc[symmetric] \<Sigma>\<Sigma>2.map_comp0[symmetric] map_prod_o_convol o_id
unfolding o_assoc[symmetric] gg2_natural
unfolding o_assoc eval2_gg2 F_map_comp ..

(* corecursion: *)
definition corecUU2 :: "('a \<Rightarrow> (J + 'a) \<Sigma>\<Sigma>2 F \<Sigma>\<Sigma>2) \<Rightarrow> 'a \<Rightarrow> J" where
"corecUU2 s \<equiv>
 unfoldUU2 (case_sum (leaf2 o dd2 o leaf2 o <Inl , F_map Inl \<circ> dtor_J>) s) o Inr"

lemma unfoldUU2_Inl:
"unfoldUU2 (case_sum (leaf2 \<circ> dd2 \<circ> leaf2 \<circ> <Inl , F_map Inl \<circ> dtor_J>) s) \<circ> Inl = id"
(is "?L = ?R")
proof-
  have "?L = unfoldUU2 (leaf2 o dd2 o leaf2 o <id, dtor_J>)"
  apply(rule unfoldUU2_unique)
  apply(subst unfoldUU2)
  unfolding o_assoc[symmetric] case_sum_o_inj snd_convol
  unfolding F_map_comp \<Sigma>\<Sigma>2.map_comp0
  unfolding o_assoc
  apply(rule sym)
  unfolding o_assoc
  apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric],
              subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
  apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric],
              subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric],
              subst o_assoc[symmetric])
  unfolding leaf2_natural apply(subst o_assoc[symmetric])
  apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric],
              subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
  unfolding dd2_natural[symmetric]
  apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric],
              subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
  apply(subst o_assoc[symmetric], subst o_assoc[symmetric])
  unfolding leaf2_natural
  unfolding o_assoc[symmetric] map_prod_o_convol o_id ..
  also have "... = ?R"
  apply(rule sym, rule unfoldUU2_unique)
  unfolding \<Sigma>\<Sigma>2.map_id0 F_map_id o_id
  unfolding o_assoc
  apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric],
              subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
  unfolding dd2_leaf2
  unfolding o_assoc[symmetric] snd_convol
  unfolding o_assoc
  apply(subst o_assoc[symmetric])
  unfolding leaf2_natural unfolding o_assoc eval2_leaf2 id_o
  apply(subst o_assoc[symmetric])
  unfolding F_map_comp[symmetric] eval2_leaf2 F_map_id o_id ctor_dtor_J_pointfree ..
  finally show ?thesis .
qed

theorem corecUU2_pointfree:
"corecUU2 s =
 eval2 o \<Sigma>\<Sigma>2_map (ctor_J o F_map eval2 o F_map (\<Sigma>\<Sigma>2_map (case_sum id (corecUU2 s)))) o s"
unfolding corecUU2_def
apply(subst unfoldUU2)
unfolding o_assoc[symmetric] unfolding case_sum_o_inj
apply(subst unfoldUU2_Inl[symmetric, of s])
unfolding o_assoc case_sum_Inl_Inr_L extdd2_def ..

theorem corecUU2_unique:
  assumes f: "f = eval2 o \<Sigma>\<Sigma>2_map (ctor_J o F_map eval2 o F_map (\<Sigma>\<Sigma>2_map (case_sum id f))) o s"
  shows "f = corecUU2 s"
  unfolding corecUU2_def
  apply(rule eq_o_InrI[OF unfoldUU2_Inl unfoldUU2_unique])
  apply (subst f)
  apply (auto simp: fun_eq_iff eval2_leaf2' pre_J.map_comp o_eq_dest[OF dd2_leaf2] convol_def
    leaf2_natural o_assoc case_sum_o_inj(1) eval2_leaf2 pre_J.map_id J.ctor_dtor split: sum.splits)
  done

theorem corecUU2:
"corecUU2 s a =
 eval2 (\<Sigma>\<Sigma>2_map (ctor_J o F_map eval2 o F_map (\<Sigma>\<Sigma>2_map (case_sum id (corecUU2 s)))) (s a))"
using corecUU2_pointfree unfolding o_def fun_eq_iff by(rule allE)

end