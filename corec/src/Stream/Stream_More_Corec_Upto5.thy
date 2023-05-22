header {* More on corecursion and coinduction up to *}

theory Stream_More_Corec_Upto5
imports Stream_Corec_Upto5
begin


subsection{* A natural-transformation-based version of the up-to corecursion principle *}

definition alg\<rho>5 :: "J K5 \<Rightarrow> J" where "alg\<rho>5 \<equiv> eval5 o K5_as_\<Sigma>\<Sigma>5"

lemma dd5_K5_as_\<Sigma>\<Sigma>5:
"dd5 o K5_as_\<Sigma>\<Sigma>5 = \<rho>5"
unfolding K5_as_\<Sigma>\<Sigma>5_def dd5_def
unfolding o_assoc apply(subst o_assoc[symmetric])
unfolding ddd5_\<oo>\<pp>5 unfolding o_assoc snd_convol
unfolding o_assoc apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
unfolding \<Sigma>5.map_comp0[symmetric] ddd5_leaf5 \<Lambda>5_natural
unfolding o_assoc F_map_comp[symmetric] leaf5_flat5 F_map_id id_o \<Lambda>5_Inr ..

lemma alg\<rho>5: "dtor_J o alg\<rho>5 = F_map eval5 o \<rho>5 o K5_map <id, dtor_J>"
unfolding dd5_K5_as_\<Sigma>\<Sigma>5[symmetric] o_assoc
unfolding o_assoc[symmetric] K5_as_\<Sigma>\<Sigma>5_natural
unfolding o_assoc eval5 alg\<rho>5_def ..

lemma flat5_embL5: "flat5 o embL5 o \<Sigma>\<Sigma>4_map embL5 = embL5 o flat4" (is "?L = ?R")
proof-
  have "?L = ext4 (\<oo>\<pp>5 o Abs_\<Sigma>5 o Inl) embL5"
  proof(rule ext4_unique)
    show "flat5 \<circ> embL5 \<circ> \<Sigma>\<Sigma>4_map embL5 \<circ> leaf4 = embL5"
    unfolding o_assoc[symmetric] unfolding leaf4_natural
    unfolding o_assoc apply(subst o_assoc[symmetric])
    apply(subst embL5_def) unfolding ext4_comp_leaf4 flat5_leaf5 id_o ..
  next
    show "flat5 \<circ> embL5 \<circ> \<Sigma>\<Sigma>4_map embL5 \<circ> \<oo>\<pp>4 = \<oo>\<pp>5 \<circ> Abs_\<Sigma>5 \<circ> Inl \<circ> \<Sigma>4_map (flat5 \<circ> embL5 \<circ> \<Sigma>\<Sigma>4_map embL5)"
    apply(subst o_assoc[symmetric]) unfolding embL5_natural
    unfolding o_assoc apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric],
                            subst o_assoc[symmetric])
    unfolding embL5_def unfolding ext4_commute unfolding embL5_def[symmetric]
    unfolding o_assoc apply(subst o_assoc[symmetric])
    unfolding \<oo>\<pp>5_natural[symmetric]
    unfolding o_assoc apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
    unfolding map_sum_Inl Abs_\<Sigma>5_natural
    unfolding o_assoc[symmetric] map_sum_Inl \<Sigma>4.map_comp0[symmetric] embL5_natural[symmetric]
    apply(rule sym) apply(subst \<Sigma>4.map_comp0) unfolding o_assoc
    unfolding flat5_def unfolding ext5_commute
    apply(rule sym) apply(subst o_assoc[symmetric])
    unfolding Abs_\<Sigma>5_natural unfolding o_assoc[symmetric] map_sum_Inl \<oo>\<pp>5_natural[symmetric] ..
  qed
  also have "... = ?R"
  proof(rule sym, rule ext4_unique)
    show "embL5 \<circ> flat4 \<circ> leaf4 = embL5"
    unfolding o_assoc[symmetric] flat4_leaf4 o_id ..
  next
    show "embL5 \<circ> flat4 \<circ> \<oo>\<pp>4 = \<oo>\<pp>5 \<circ> Abs_\<Sigma>5 \<circ> Inl \<circ> \<Sigma>4_map (embL5 \<circ> flat4)"
    unfolding flat4_def o_assoc[symmetric] ext4_commute
    unfolding o_assoc
    apply(subst embL5_def) unfolding ext4_commute apply(subst embL5_def[symmetric])
    unfolding \<Sigma>4.map_comp0 o_assoc ..
  qed
  finally show ?thesis .
qed

lemma ddd5_embL5: "ddd5 \<circ> embL5 = (embL5 ** F_map embL5) \<circ> ddd4" (is "?L = ?R")
proof-
  have "?L = ext4 <\<oo>\<pp>5 o Abs_\<Sigma>5 o Inl o \<Sigma>4_map fst, F_map (flat5 o embL5) o \<Lambda>4> (leaf5 ** F_map leaf5)"
  proof(rule ext4_unique)
    show "ddd5 \<circ> embL5 \<circ> leaf4 = leaf5 ** F_map leaf5"
    apply(rule fst_snd_cong)
    unfolding fst_comp_map_prod snd_comp_map_prod
    unfolding  embL5_def
    apply (subst (3) o_assoc[symmetric]) defer apply (subst (3) o_assoc[symmetric])
    unfolding ext4_comp_leaf4
    unfolding ddd5_def ext5_comp_leaf5 fst_comp_map_prod snd_comp_map_prod by(rule refl, rule refl)
  next
    show "ddd5 \<circ> embL5 \<circ> \<oo>\<pp>4 =
          <\<oo>\<pp>5 \<circ> Abs_\<Sigma>5 \<circ> Inl \<circ> \<Sigma>4_map fst , F_map (flat5 \<circ> embL5) \<circ> \<Lambda>4> \<circ> \<Sigma>4_map (ddd5 \<circ> embL5)" (is "?A = ?B")
    proof(rule fst_snd_cong)
      show "fst o ?A = fst o ?B"
      unfolding o_assoc fst_convol unfolding o_assoc[symmetric] \<Sigma>4.map_comp0[symmetric]
      unfolding o_assoc
      apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
      apply(subst embL5_def) unfolding ext4_commute apply(subst embL5_def[symmetric])
      unfolding o_assoc apply(subst o_assoc[symmetric])
      apply(subst ddd5_def) unfolding ext5_commute apply(subst ddd5_def[symmetric])
      unfolding o_assoc fst_convol
      apply(subst o_assoc[symmetric]) unfolding \<Sigma>5.map_comp0[symmetric]
      apply(subst o_assoc[symmetric]) unfolding Abs_\<Sigma>5_natural map_sum_Inl o_assoc[symmetric]
      unfolding \<Sigma>4.map_comp0[symmetric] o_assoc ..
    next
      show "snd o ?A = snd o ?B"
      unfolding o_assoc snd_convol unfolding o_assoc[symmetric]
      apply(subst embL5_def) unfolding ext4_commute apply(subst embL5_def[symmetric])
      unfolding o_assoc apply(subst o_assoc[symmetric], subst o_assoc[symmetric])
      apply(subst ddd5_def) unfolding ext5_commute apply(subst ddd5_def[symmetric])
      unfolding o_assoc snd_convol
      unfolding o_assoc apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
      unfolding Abs_\<Sigma>5_natural map_sum_Inl o_assoc[symmetric]
      unfolding o_assoc apply(subst o_assoc[symmetric], subst o_assoc[symmetric])
      unfolding \<Lambda>5_Inl unfolding \<Sigma>4.map_comp0 F_map_comp o_assoc ..
    qed
  qed
  also have "... = ?R"
  proof(rule sym, rule ext4_unique)
    show "(embL5 ** F_map embL5) \<circ> ddd4 \<circ> leaf4 = leaf5 ** F_map leaf5"
    unfolding o_assoc apply(subst o_assoc[symmetric])
    apply(subst ddd4_def) unfolding ext4_comp_leaf4
    unfolding map_prod.comp unfolding F_map_comp[symmetric]
    apply(subst embL5_def, subst embL5_def) unfolding ext4_comp_leaf4 ..
  next
    show "embL5 ** F_map embL5 \<circ> ddd4 \<circ> \<oo>\<pp>4 =
          <\<oo>\<pp>5 \<circ> Abs_\<Sigma>5 \<circ> Inl \<circ> \<Sigma>4_map fst , F_map (flat5 \<circ> embL5) \<circ> \<Lambda>4> \<circ> \<Sigma>4_map (embL5 ** F_map embL5 \<circ> ddd4)"
    (is "?A = ?B") proof(rule fst_snd_cong)
      show "fst o ?A = fst o ?B"
      unfolding o_assoc fst_convol fst_comp_map_prod
      unfolding o_assoc[symmetric] \<Sigma>4.map_comp0[symmetric] unfolding o_assoc unfolding fst_comp_map_prod
      unfolding o_assoc apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
      apply(subst ddd4_def) unfolding ext4_commute apply(subst ddd4_def[symmetric])
      unfolding o_assoc fst_convol
      apply(subst embL5_def) unfolding ext4_commute apply(subst embL5_def[symmetric])
      unfolding \<Sigma>4.map_comp0 o_assoc ..
    next
      show "snd o ?A = snd o ?B"
      unfolding o_assoc snd_convol snd_comp_map_prod
      unfolding o_assoc apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
      apply(subst ddd4_def) unfolding ext4_commute apply(subst ddd4_def[symmetric])
      unfolding o_assoc apply(subst o_assoc[symmetric]) unfolding snd_convol
      unfolding o_assoc F_map_comp[symmetric]
      unfolding flat5_embL5[symmetric]
      unfolding F_map_comp
      unfolding o_assoc apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
      unfolding \<Lambda>4_natural[symmetric]
      unfolding o_assoc \<Sigma>4.map_comp0 ..
    qed
  qed
  finally show ?thesis .
qed

lemma dd5_embL5: "dd5 \<circ> embL5 = F_map embL5 \<circ> dd4"
unfolding dd5_def dd4_def o_assoc[symmetric] ddd5_embL5 by auto

lemma F_map_embL5_\<Sigma>\<Sigma>4_map:
"F_map embL5 \<circ> dd4 \<circ> \<Sigma>\<Sigma>4_map <id , dtor_J> =
 dd5 \<circ> \<Sigma>\<Sigma>5_map <id , dtor_J> \<circ> embL5"
unfolding o_assoc[symmetric] unfolding embL5_natural[symmetric]
unfolding o_assoc dd5_embL5 ..

lemma eval5_embL5: "eval5 o embL5 = eval4"
unfolding eval4_def apply(rule J.dtor_unfold_unique)
unfolding eval5_def unfolding o_assoc
unfolding dtor_unfold_J_pointfree
unfolding F_map_comp
apply(subst o_assoc[symmetric], subst o_assoc[symmetric])
unfolding F_map_embL5_\<Sigma>\<Sigma>4_map o_assoc ..

theorem alg\<Lambda>5_alg\<Lambda>4_alg\<rho>5:
"alg\<Lambda>5 o Abs_\<Sigma>5 = case_sum alg\<Lambda>4 alg\<rho>5" (is "?L = ?R")
proof(rule sum_comp_cases)
  show "?L o Inl = ?R o Inl"
  unfolding case_sum_o_inj apply(subst dtor_J_o_inj[symmetric])
  unfolding o_assoc dtor_J_alg\<Lambda>5 unfolding Abs_\<Sigma>5_natural o_assoc[symmetric] map_sum_Inl
  unfolding o_assoc apply(subst o_assoc[symmetric], subst o_assoc[symmetric]) unfolding \<Lambda>5_Inl
  unfolding o_assoc F_map_comp[symmetric] eval5_embL5 dtor_J_alg\<Lambda>4 ..
next
  show "?L o Inr = ?R o Inr"
  unfolding alg\<rho>5_def case_sum_o_inj alg\<Lambda>5_def K5_as_\<Sigma>\<Sigma>5_def o_assoc ..
qed

theorem alg\<Lambda>5_Inl: "alg\<Lambda>5 (Abs_\<Sigma>5 (Inl x)) = alg\<Lambda>4 x" (is "?L = ?R")
unfolding o_eq_dest_lhs[OF alg\<Lambda>5_alg\<Lambda>4_alg\<rho>5] by simp

lemma alg\<Lambda>5_Inl_pointfree: "alg\<Lambda>5 o Abs_\<Sigma>5 o Inl = alg\<Lambda>4"
unfolding o_def fun_eq_iff alg\<Lambda>5_Inl by simp

theorem alg\<Lambda>5_Inr: "alg\<Lambda>5 (Abs_\<Sigma>5 (Inr x)) = alg\<rho>5 x" (is "?L = ?R")
unfolding o_eq_dest_lhs[OF alg\<Lambda>5_alg\<Lambda>4_alg\<rho>5] by simp



subsection{* Up-to corecursor with guard not necessarily at the top *}

definition ff5 :: "'a F \<Rightarrow> 'a \<Sigma>5" where "ff5 \<equiv> Abs_\<Sigma>5 o Inl o ff4"

lemma alg\<Lambda>5_ff5: "alg\<Lambda>5 \<circ> ff5 = ctor_J"
unfolding ff5_def o_assoc alg\<Lambda>5_Inl_pointfree alg\<Lambda>4_ff4 ..

lemma ff5_transfer[transfer_rule]: "(F_rel R ===> \<Sigma>5_rel R) ff5 ff5"
unfolding ff5_def by transfer_prover

lemma ff5_natural: "\<Sigma>5_map f o ff5 = ff5 o F_map f"
using ff5_transfer[of "BNF_Def.Grp UNIV f"]
unfolding \<Sigma>5.rel_Grp F_rel_Grp
unfolding Grp_def rel_fun_def by auto

definition gg5 :: "'a \<Sigma>\<Sigma>5 F \<Rightarrow> 'a \<Sigma>\<Sigma>5" where
"gg5 \<equiv> \<oo>\<pp>5 o ff5"

lemma eval5_gg5: "eval5 o gg5 = ctor_J o F_map eval5"
unfolding gg5_def
unfolding o_assoc unfolding eval5_comp_\<oo>\<pp>5
unfolding o_assoc[symmetric] ff5_natural
unfolding o_assoc alg\<Lambda>5_ff5 ..

lemma gg5_transfer[transfer_rule]: "(F_rel (\<Sigma>\<Sigma>5_rel R) ===> \<Sigma>\<Sigma>5_rel R) gg5 gg5"
unfolding gg5_def by transfer_prover

lemma gg5_natural: "\<Sigma>\<Sigma>5_map f o gg5 = gg5 o F_map (\<Sigma>\<Sigma>5_map f)"
using gg5_transfer[of "BNF_Def.Grp UNIV f"]
unfolding \<Sigma>\<Sigma>5.rel_Grp F_rel_Grp
unfolding Grp_def rel_fun_def by auto

definition unfoldUU5 :: "('a \<Rightarrow> 'a \<Sigma>\<Sigma>5 F \<Sigma>\<Sigma>5) \<Rightarrow> 'a \<Rightarrow> J" where
"unfoldUU5 s \<equiv> unfoldU5 (F_map flat5 o dd5 o \<Sigma>\<Sigma>5_map <gg5, id> o s)"

theorem unfoldUU5:
"unfoldUU5 s =
 eval5 o \<Sigma>\<Sigma>5_map (ctor_J o F_map eval5 o F_map (\<Sigma>\<Sigma>5_map (unfoldUU5 s))) o s"
unfolding unfoldUU5_def apply(subst unfoldU5_ctor_J_pointfree[symmetric]) unfolding unfoldUU5_def[symmetric]
unfolding extdd5_def F_map_comp[symmetric] o_assoc
apply(subst o_assoc[symmetric]) unfolding F_map_comp[symmetric]
apply(subst o_assoc[symmetric]) unfolding flat5_natural[symmetric]
apply(subst o_assoc) unfolding eval5_flat5
unfolding F_map_comp
apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
unfolding dd5_natural[symmetric]
unfolding o_assoc apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
unfolding dd5_natural[symmetric]
unfolding o_assoc[symmetric] \<Sigma>\<Sigma>5.map_comp0[symmetric]
unfolding o_assoc eval5_gg5 unfolding \<Sigma>\<Sigma>5.map_comp0 o_assoc
apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric],
      subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
unfolding \<Sigma>\<Sigma>5.map_comp0[symmetric]
apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
unfolding \<Sigma>\<Sigma>5.map_comp0[symmetric] map_prod.comp map_prod_o_convol o_id F_map_comp[symmetric]
apply(rule sym) unfolding o_assoc
apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
unfolding \<Sigma>\<Sigma>5.map_comp0[symmetric] F_map_comp[symmetric] o_assoc[symmetric] gg5_natural
unfolding o_assoc eval5_gg5
apply(rule sym)
apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
unfolding F_map_comp[symmetric] convol_comp_id2 convol_ctor_J_dtor_J
          \<Sigma>\<Sigma>5.map_comp0 o_assoc eval5 ctor_dtor_J_pointfree id_o ..

theorem unfoldUU5_unique:
assumes f: "f = eval5 o \<Sigma>\<Sigma>5_map (ctor_J o F_map eval5 o F_map (\<Sigma>\<Sigma>5_map f)) o s"
shows "f = unfoldUU5 s"
unfolding unfoldUU5_def apply(rule unfoldU5_unique)
apply(rule sym) apply(subst f) unfolding extdd5_def
unfolding o_assoc
apply(subst eval5_def) unfolding dtor_unfold_J_pointfree apply(subst eval5_def[symmetric])
unfolding o_assoc
apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
unfolding o_assoc \<Sigma>\<Sigma>5.map_comp0[symmetric]  convol_o id_o dtor_J_ctor_pointfree F_map_comp[symmetric]
unfolding o_assoc[symmetric] flat5_natural[symmetric]
unfolding o_assoc eval5_flat5 unfolding o_assoc[symmetric] unfolding F_map_comp
apply(rule sym) apply(subst F_map_comp[symmetric], subst \<Sigma>\<Sigma>5.map_comp0[symmetric])
unfolding o_assoc apply(subst o_assoc[symmetric])
unfolding dd5_natural[symmetric]
unfolding o_assoc[symmetric] \<Sigma>\<Sigma>5.map_comp0[symmetric] map_prod_o_convol o_id
unfolding o_assoc[symmetric] gg5_natural
unfolding o_assoc eval5_gg5 F_map_comp ..

(* corecursion: *)
definition corecUU5 :: "('a \<Rightarrow> (J + 'a) \<Sigma>\<Sigma>5 F \<Sigma>\<Sigma>5) \<Rightarrow> 'a \<Rightarrow> J" where
"corecUU5 s \<equiv>
 unfoldUU5 (case_sum (leaf5 o dd5 o leaf5 o <Inl , F_map Inl \<circ> dtor_J>) s) o Inr"

lemma unfoldUU5_Inl:
"unfoldUU5 (case_sum (leaf5 \<circ> dd5 \<circ> leaf5 \<circ> <Inl , F_map Inl \<circ> dtor_J>) s) \<circ> Inl = id"
(is "?L = ?R")
proof-
  have "?L = unfoldUU5 (leaf5 o dd5 o leaf5 o <id, dtor_J>)"
  apply(rule unfoldUU5_unique)
  apply(subst unfoldUU5)
  unfolding o_assoc[symmetric] case_sum_o_inj snd_convol
  unfolding F_map_comp \<Sigma>\<Sigma>5.map_comp0
  unfolding o_assoc
  apply(rule sym)
  unfolding o_assoc
  apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric],
              subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
  apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric],
              subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric],
              subst o_assoc[symmetric])
  unfolding leaf5_natural apply(subst o_assoc[symmetric])
  apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric],
              subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
  unfolding dd5_natural[symmetric]
  apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric],
              subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
  apply(subst o_assoc[symmetric], subst o_assoc[symmetric])
  unfolding leaf5_natural
  unfolding o_assoc[symmetric] map_prod_o_convol o_id ..
  also have "... = ?R"
  apply(rule sym, rule unfoldUU5_unique)
  unfolding \<Sigma>\<Sigma>5.map_id0 F_map_id o_id
  unfolding o_assoc
  apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric],
              subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
  unfolding dd5_leaf5
  unfolding o_assoc[symmetric] snd_convol
  unfolding o_assoc
  apply(subst o_assoc[symmetric])
  unfolding leaf5_natural unfolding o_assoc eval5_leaf5 id_o
  apply(subst o_assoc[symmetric])
  unfolding F_map_comp[symmetric] eval5_leaf5 F_map_id o_id ctor_dtor_J_pointfree ..
  finally show ?thesis .
qed

theorem corecUU5_pointfree:
"corecUU5 s =
 eval5 o \<Sigma>\<Sigma>5_map (ctor_J o F_map eval5 o F_map (\<Sigma>\<Sigma>5_map (case_sum id (corecUU5 s)))) o s"
unfolding corecUU5_def
apply(subst unfoldUU5)
unfolding o_assoc[symmetric] unfolding case_sum_o_inj
apply(subst unfoldUU5_Inl[symmetric, of s])
unfolding o_assoc case_sum_Inl_Inr_L extdd5_def ..

theorem corecUU5_unique:
  assumes f: "f = eval5 o \<Sigma>\<Sigma>5_map (ctor_J o F_map eval5 o F_map (\<Sigma>\<Sigma>5_map (case_sum id f))) o s"
  shows "f = corecUU5 s"
  unfolding corecUU5_def
  apply(rule eq_o_InrI[OF unfoldUU5_Inl unfoldUU5_unique])
  apply (subst f)
  apply (auto simp: fun_eq_iff eval5_leaf5' pre_J.map_comp o_eq_dest[OF dd5_leaf5] convol_def
    leaf5_natural o_assoc case_sum_o_inj(1) eval5_leaf5 pre_J.map_id J.ctor_dtor split: sum.splits)
  done

theorem corecUU5:
"corecUU5 s a =
 eval5 (\<Sigma>\<Sigma>5_map (ctor_J o F_map eval5 o F_map (\<Sigma>\<Sigma>5_map (case_sum id (corecUU5 s)))) (s a))"
using corecUU5_pointfree unfolding o_def fun_eq_iff by(rule allE)

end