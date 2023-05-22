header {* The initial algll operation is precisely (the copy of) ctor_J *}

theory Binary_Tree_More_Corec_Upto0
imports Binary_Tree_Corec_Upto0
begin

lemma alg\<Lambda>0: "alg\<Lambda>0 o Abs_\<Sigma>0 = ctor_J"
unfolding ctor_J_def apply(rule J.dtor_unfold_unique)
unfolding o_assoc dtor_J_alg\<Lambda>0
unfolding alg\<Lambda>0_def unfolding o_assoc[symmetric] Abs_\<Sigma>0_natural
unfolding F_map_comp[symmetric] o_assoc
unfolding \<Lambda>0_def
unfolding o_assoc[symmetric] snd_comp_map_prod
unfolding o_assoc \<Sigma>0.map_comp0[symmetric]
apply(rule sym)
apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric],
            subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric],
            subst o_assoc[symmetric])
unfolding o_id Abs_\<Sigma>0_natural o_assoc Rep_\<Sigma>0_o_Abs_\<Sigma>0
unfolding F_map_comp[symmetric] o_assoc[symmetric] snd_convol
unfolding o_assoc
apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
unfolding o_assoc ..

(* This should be the default evaluator for eval0 on the term algebra: *)

theorem eval0_\<oo>\<pp>0_ctor_J:
"eval0 (\<oo>\<pp>0 t) = ctor_J (Rep_\<Sigma>0 (\<Sigma>0_map eval0 t))"
unfolding eval0_\<oo>\<pp>0 alg\<Lambda>0[symmetric] o_apply Rep_\<Sigma>0_inverse ..


subsection{* Up-to corecursor with guard not necessarily at the top *}

definition ff0 :: "'a F \<Rightarrow> 'a \<Sigma>0" where "ff0 \<equiv> Abs_\<Sigma>0" (* just for bootstrapping *)

lemma alg\<Lambda>0_ff0: "alg\<Lambda>0 \<circ> ff0 = ctor_J"
unfolding ff0_def o_assoc alg\<Lambda>0 ..

lemma ff0_transfer[transfer_rule]: "(F_rel R ===> \<Sigma>0_rel R) ff0 ff0"
unfolding ff0_def by transfer_prover

lemma ff0_natural: "\<Sigma>0_map f o ff0 = ff0 o F_map f"
using ff0_transfer[of "BNF_Def.Grp UNIV f"]
unfolding \<Sigma>0.rel_Grp F_rel_Grp
unfolding Grp_def rel_fun_def by auto

definition gg0 :: "'a \<Sigma>\<Sigma>0 F \<Rightarrow> 'a \<Sigma>\<Sigma>0" where
"gg0 \<equiv> \<oo>\<pp>0 o ff0"

lemma eval0_gg0: "eval0 o gg0 = ctor_J o F_map eval0"
unfolding o_assoc gg0_def eval0_comp_\<oo>\<pp>0 alg\<Lambda>0[symmetric]
unfolding o_assoc[symmetric] unfolding ff0_def Abs_\<Sigma>0_natural
..

lemma gg0_transfer[transfer_rule]: "(F_rel (\<Sigma>\<Sigma>0_rel R) ===> \<Sigma>\<Sigma>0_rel R) gg0 gg0"
unfolding gg0_def by transfer_prover

lemma gg0_natural: "\<Sigma>\<Sigma>0_map f o gg0 = gg0 o F_map (\<Sigma>\<Sigma>0_map f)"
using gg0_transfer[of "BNF_Def.Grp UNIV f"]
unfolding \<Sigma>\<Sigma>0.rel_Grp F_rel_Grp
unfolding Grp_def rel_fun_def by auto

definition unfoldUU0 :: "('a \<Rightarrow> 'a \<Sigma>\<Sigma>0 F \<Sigma>\<Sigma>0) \<Rightarrow> 'a \<Rightarrow> J" where
"unfoldUU0 s \<equiv> unfoldU0 (F_map flat0 o dd0 o \<Sigma>\<Sigma>0_map <gg0, id> o s)"

theorem unfoldUU0:
"unfoldUU0 s =
 eval0 o \<Sigma>\<Sigma>0_map (ctor_J o F_map eval0 o F_map (\<Sigma>\<Sigma>0_map (unfoldUU0 s))) o s"
unfolding unfoldUU0_def apply(subst unfoldU0_ctor_J_pointfree[symmetric]) unfolding unfoldUU0_def[symmetric]
unfolding extdd0_def F_map_comp[symmetric] o_assoc
apply(subst o_assoc[symmetric]) unfolding F_map_comp[symmetric]
apply(subst o_assoc[symmetric]) unfolding flat0_natural[symmetric]
apply(subst o_assoc) unfolding eval0_flat0
unfolding F_map_comp
apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
unfolding dd0_natural[symmetric]
unfolding o_assoc apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
unfolding dd0_natural[symmetric]
unfolding o_assoc[symmetric] \<Sigma>\<Sigma>0.map_comp0[symmetric]
unfolding o_assoc eval0_gg0 unfolding \<Sigma>\<Sigma>0.map_comp0 o_assoc
apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric],
      subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
unfolding \<Sigma>\<Sigma>0.map_comp0[symmetric]
apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
unfolding \<Sigma>\<Sigma>0.map_comp0[symmetric] map_prod.comp map_prod_o_convol o_id F_map_comp[symmetric]
apply(rule sym) unfolding o_assoc
apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
unfolding \<Sigma>\<Sigma>0.map_comp0[symmetric] F_map_comp[symmetric] o_assoc[symmetric] gg0_natural
unfolding o_assoc eval0_gg0
apply(rule sym)
apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
unfolding F_map_comp[symmetric] convol_comp_id2 convol_ctor_J_dtor_J
          \<Sigma>\<Sigma>0.map_comp0 o_assoc eval0 ctor_dtor_J_pointfree id_o ..

theorem unfoldUU0_unique:
assumes f: "f = eval0 o \<Sigma>\<Sigma>0_map (ctor_J o F_map eval0 o F_map (\<Sigma>\<Sigma>0_map f)) o s"
shows "f = unfoldUU0 s"
unfolding unfoldUU0_def apply(rule unfoldU0_unique)
apply(rule sym) apply(subst f) unfolding extdd0_def
unfolding o_assoc
apply(subst eval0_def) unfolding dtor_unfold_J_pointfree apply(subst eval0_def[symmetric])
unfolding o_assoc
apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
unfolding o_assoc \<Sigma>\<Sigma>0.map_comp0[symmetric]  convol_o id_o dtor_J_ctor_pointfree F_map_comp[symmetric]
unfolding o_assoc[symmetric] flat0_natural[symmetric]
unfolding o_assoc eval0_flat0 unfolding o_assoc[symmetric] unfolding F_map_comp
apply(rule sym) apply(subst F_map_comp[symmetric], subst \<Sigma>\<Sigma>0.map_comp0[symmetric])
unfolding o_assoc apply(subst o_assoc[symmetric])
unfolding dd0_natural[symmetric]
unfolding o_assoc[symmetric] \<Sigma>\<Sigma>0.map_comp0[symmetric] map_prod_o_convol o_id
unfolding o_assoc[symmetric] gg0_natural
unfolding o_assoc eval0_gg0 F_map_comp ..

(* corecursion: *)
definition corecUU0 :: "('a \<Rightarrow> (J + 'a) \<Sigma>\<Sigma>0 F \<Sigma>\<Sigma>0) \<Rightarrow> 'a \<Rightarrow> J" where
"corecUU0 s \<equiv>
 unfoldUU0 (case_sum (leaf0 o dd0 o leaf0 o <Inl , F_map Inl \<circ> dtor_J>) s) o Inr"

lemma unfoldUU0_Inl:
"unfoldUU0 (case_sum (leaf0 \<circ> dd0 \<circ> leaf0 \<circ> <Inl , F_map Inl \<circ> dtor_J>) s) \<circ> Inl = id"
(is "?L = ?R")
proof-
  have "?L = unfoldUU0 (leaf0 o dd0 o leaf0 o <id, dtor_J>)"
  apply(rule unfoldUU0_unique)
  apply(subst unfoldUU0)
  unfolding o_assoc[symmetric] case_sum_o_inj snd_convol
  unfolding F_map_comp \<Sigma>\<Sigma>0.map_comp0
  unfolding o_assoc
  apply(rule sym)
  unfolding o_assoc
  apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric],
              subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
  apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric],
              subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric],
              subst o_assoc[symmetric])
  unfolding leaf0_natural apply(subst o_assoc[symmetric])
  apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric],
              subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
  unfolding dd0_natural[symmetric]
  apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric],
              subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
  apply(subst o_assoc[symmetric], subst o_assoc[symmetric])
  unfolding leaf0_natural
  unfolding o_assoc[symmetric] map_prod_o_convol o_id ..
  also have "... = ?R"
  apply(rule sym, rule unfoldUU0_unique)
  unfolding \<Sigma>\<Sigma>0.map_id0 F_map_id o_id
  unfolding o_assoc
  apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric],
              subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
  unfolding dd0_leaf0
  unfolding o_assoc[symmetric] snd_convol
  unfolding o_assoc
  apply(subst o_assoc[symmetric])
  unfolding leaf0_natural unfolding o_assoc eval0_leaf0 id_o
  apply(subst o_assoc[symmetric])
  unfolding F_map_comp[symmetric] eval0_leaf0 F_map_id o_id ctor_dtor_J_pointfree ..
  finally show ?thesis .
qed

theorem corecUU0_pointfree:
"corecUU0 s =
 eval0 o \<Sigma>\<Sigma>0_map (ctor_J o F_map eval0 o F_map (\<Sigma>\<Sigma>0_map (case_sum id (corecUU0 s)))) o s"
unfolding corecUU0_def
apply(subst unfoldUU0)
unfolding o_assoc[symmetric] unfolding case_sum_o_inj
apply(subst unfoldUU0_Inl[symmetric, of s])
unfolding o_assoc case_sum_Inl_Inr_L extdd0_def ..

theorem corecUU0_unique:
  assumes f: "f = eval0 o \<Sigma>\<Sigma>0_map (ctor_J o F_map eval0 o F_map (\<Sigma>\<Sigma>0_map (case_sum id f))) o s"
  shows "f = corecUU0 s"
  unfolding corecUU0_def
  apply(rule eq_o_InrI[OF unfoldUU0_Inl unfoldUU0_unique])
  apply (subst f)
  apply (auto simp: fun_eq_iff eval0_leaf0' pre_J.map_comp o_eq_dest[OF dd0_leaf0] convol_def
    leaf0_natural o_assoc case_sum_o_inj(1) eval0_leaf0 pre_J.map_id J.ctor_dtor split: sum.splits)
  done

theorem corecUU0:
"corecUU0 s a =
 eval0 (\<Sigma>\<Sigma>0_map (ctor_J o F_map eval0 o F_map (\<Sigma>\<Sigma>0_map (case_sum id (corecUU0 s)))) (s a))"
using corecUU0_pointfree unfolding o_def fun_eq_iff by(rule allE)


end