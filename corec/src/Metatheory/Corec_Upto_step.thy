header {* Corecursion and coinduction up to *}

theory Corec_Upto_step
imports Lift_to_Free_step
begin


subsection{* The algebra associated to dd_step *}

definition "eval_step \<equiv> dtor_unfold_J (dd_step o \<Sigma>\<Sigma>_step_map <id, dtor_J>)"

lemma eval_step: "F_map eval_step o dd_step o \<Sigma>\<Sigma>_step_map <id, dtor_J> = dtor_J o eval_step"
  unfolding eval_step_def dtor_unfold_J_pointfree unfolding o_assoc ..

lemma eval_step_ctor_J: "ctor_J o F_map eval_step o dd_step o \<Sigma>\<Sigma>_step_map <id, dtor_J> = eval_step"
  unfolding o_def spec[OF eval_step[unfolded o_def fun_eq_iff]] J.ctor_dtor ..

lemma eval_step_leaf_step: "eval_step \<circ> leaf_step = id"
proof (rule trans)
  show "eval_step \<circ> leaf_step = dtor_unfold_J dtor_J"
  apply(rule J.dtor_unfold_unique)
  unfolding o_assoc eval_step[symmetric] unfolding o_assoc[symmetric] leaf_step_natural
  apply(rule sym)
  unfolding F_map_comp o_assoc apply (subst o_assoc[symmetric])
  unfolding dd_step_leaf_step unfolding o_assoc[symmetric] by simp
qed(metis F_map_id J.dtor_unfold_unique fun.map_id o_id)

lemma eval_step_flat_step: "eval_step \<circ> flat_step = eval_step \<circ> \<Sigma>\<Sigma>_step_map eval_step"
proof (rule trans)
  let ?K_step = "dtor_unfold_J (dd_step o \<Sigma>\<Sigma>_step_map <\<Sigma>\<Sigma>_step_map fst, dd_step> o \<Sigma>\<Sigma>_step_map (\<Sigma>\<Sigma>_step_map <id, dtor_J>))"
  show "eval_step \<circ> flat_step = ?K_step"
  apply(rule J.dtor_unfold_unique)
  unfolding F_map_comp o_assoc
  apply(subst o_assoc[symmetric], subst o_assoc[symmetric])
  unfolding dd_step_flat_step
  unfolding o_assoc[symmetric] \<Sigma>\<Sigma>_step.map_comp0[symmetric] snd_convol
  unfolding flat_step_natural
  unfolding o_assoc eval_step ..
  (*  *)
  have A: "<eval_step, dtor_J o eval_step> = <id,dtor_J> o eval_step" by simp
  show "?K_step = eval_step \<circ> \<Sigma>\<Sigma>_step_map eval_step"
  apply(rule J.dtor_unfold_unique[symmetric])
  unfolding o_assoc[symmetric] \<Sigma>\<Sigma>_step.map_comp0[symmetric] map_prod_o_convol id_o
  unfolding F_map_comp o_assoc
  apply(subst o_assoc[symmetric]) unfolding dd_step_natural[symmetric]
  unfolding o_assoc[symmetric] \<Sigma>\<Sigma>_step.map_comp0[symmetric]
  unfolding o_assoc unfolding map_prod_o_convol unfolding convol_o
  unfolding o_assoc[symmetric] \<Sigma>\<Sigma>_step.map_comp0[symmetric] fst_convol \<Sigma>\<Sigma>_step.map_id0 o_id
  unfolding o_assoc eval_step unfolding A unfolding convol_o id_o
  apply(rule sym) apply(subst eval_step[symmetric])
  unfolding o_assoc[symmetric] \<Sigma>\<Sigma>_step.map_comp0[symmetric] convol_o id_o ..
qed


subsection{* The correspondence between coalgebras up to and coalgebras *}

(* This correspondence, and add_step the lemmas of this subsection, make
sense not only for (J,dtor_J,eval_step), but also for any dd_step-bialgebra *)

(* Coalgebra-up-to to coalgebra and vice versa: *)
definition cut\<Sigma>\<Sigma>_stepOc :: "('a \<Rightarrow> 'a \<Sigma>\<Sigma>_step F) \<Rightarrow> ('a \<Sigma>\<Sigma>_step \<Rightarrow> 'a \<Sigma>\<Sigma>_step F)"
where "cut\<Sigma>\<Sigma>_stepOc s \<equiv> F_map flat_step o dd_step o \<Sigma>\<Sigma>_step_map <leaf_step, s>"
definition c\<Sigma>\<Sigma>_stepOcut :: "('a \<Sigma>\<Sigma>_step \<Rightarrow> 'a \<Sigma>\<Sigma>_step F) \<Rightarrow> ('a \<Rightarrow> 'a \<Sigma>\<Sigma>_step F)"
where "c\<Sigma>\<Sigma>_stepOcut s' \<equiv> s' o leaf_step"

lemma c\<Sigma>\<Sigma>_stepOcut_cut\<Sigma>\<Sigma>_stepOc: "c\<Sigma>\<Sigma>_stepOcut (cut\<Sigma>\<Sigma>_stepOc s) = s"
unfolding c\<Sigma>\<Sigma>_stepOcut_def cut\<Sigma>\<Sigma>_stepOc_def
unfolding o_assoc[symmetric] unfolding leaf_step_natural
unfolding o_assoc apply(subst o_assoc[symmetric])
unfolding dd_step_leaf_step unfolding o_assoc F_map_comp[symmetric] flat_step_leaf_step
unfolding F_map_id id_o by simp

lemma cut\<Sigma>\<Sigma>_stepOc_inj: "cut\<Sigma>\<Sigma>_stepOc s_step = cut\<Sigma>\<Sigma>_stepOc s2 \<longleftrightarrow> s_step = s2"
by (metis c\<Sigma>\<Sigma>_stepOcut_cut\<Sigma>\<Sigma>_stepOc)

lemma c\<Sigma>\<Sigma>_stepOcut_surj: "\<exists> s'. c\<Sigma>\<Sigma>_stepOcut s' = s"
using c\<Sigma>\<Sigma>_stepOcut_cut\<Sigma>\<Sigma>_stepOc by(rule exI[of _ "cut\<Sigma>\<Sigma>_stepOc s"])

(* Morphism-up-to to morphism and vice versa: *)
(* The dd_step-extension of a function *)
definition extdd_step :: "('a \<Rightarrow> J) \<Rightarrow> ('a \<Sigma>\<Sigma>_step \<Rightarrow> J)"
where "extdd_step f \<equiv> eval_step o \<Sigma>\<Sigma>_step_map f"
(* The restriction of a function *)  term eval_step
definition restr :: "('a \<Sigma>\<Sigma>_step \<Rightarrow> J) \<Rightarrow> ('a \<Rightarrow> J)"
where "restr f' \<equiv> f' o leaf_step"

(* We think of extdd_step and restr as operating
extdd_step : Hom_dd_step(s,dtor_J) \<rightarrow> Hom(cut\<Sigma>\<Sigma>_stepOc s,dtor_J) and
restr : Hom(cut\<Sigma>\<Sigma>_stepOc s,dtor_J) \<rightarrow> Hom_dd_step(s,dtor_J), where
Hom(cut\<Sigma>\<Sigma>_stepOc s,dtor_J) is the set of coalgebra morphisms betwee cut\<Sigma>\<Sigma>_stepOc s and dtor_J and
Hom_dd_step(s,dtor_J) is the set of coalgebra up-to-dd_step-morphisms between s and dtor_J  *)

(* extdd_step is wedd_step-defined: *)
lemma extdd_step_mor:
assumes f:  "F_map (extdd_step f) o s = dtor_J o f"
shows "F_map (extdd_step f) o cut\<Sigma>\<Sigma>_stepOc s = dtor_J o (extdd_step f)"
proof-
  have AA: "eval_step ** F_map eval_step \<circ> (\<Sigma>\<Sigma>_step_map f ** F_map (\<Sigma>\<Sigma>_step_map f) \<circ> <leaf_step , s>) =
            <f , F_map eval_step \<circ> (F_map (\<Sigma>\<Sigma>_step_map f) \<circ> s)>"
  unfolding map_prod_o_convol unfolding leaf_step_natural o_assoc eval_step_leaf_step id_o  ..
  show ?thesis
  unfolding extdd_step_def
  unfolding o_assoc eval_step[symmetric]
  unfolding o_assoc[symmetric] \<Sigma>\<Sigma>_step.map_comp0[symmetric]
  unfolding convol_comp[symmetric] id_o
  unfolding f[symmetric, unfolded extdd_step_def]
  unfolding o_assoc
  apply(subst o_assoc[symmetric])
  unfolding F_map_comp o_assoc
  unfolding cut\<Sigma>\<Sigma>_stepOc_def
  unfolding o_assoc
  unfolding F_map_comp[symmetric] unfolding o_assoc[symmetric]
  unfolding flat_step_natural[symmetric]
  unfolding o_assoc F_map_comp
  apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
  unfolding dd_step_natural[symmetric]
  unfolding o_assoc unfolding F_map_comp[symmetric] eval_step_flat_step
  unfolding F_map_comp apply(subst o_assoc[symmetric])
  unfolding dd_step_natural[symmetric] unfolding o_assoc[symmetric] \<Sigma>\<Sigma>_step.map_comp0[symmetric]
  unfolding o_assoc[symmetric] AA[unfolded o_assoc[symmetric]] ..
qed

lemma mor_cut\<Sigma>\<Sigma>_stepOc_flat_step:
assumes f': "F_map f' o cut\<Sigma>\<Sigma>_stepOc s = dtor_J o f'"
shows "eval_step o \<Sigma>\<Sigma>_step_map f' = f' o flat_step"
proof(rule trans) (* this proof is clearly improvable: *)
  def h \<equiv> "dd_step o \<Sigma>\<Sigma>_step_map <id,cut\<Sigma>\<Sigma>_stepOc s>"
  have f'_id: "f' = f' o id" by simp
  show "eval_step \<circ> \<Sigma>\<Sigma>_step_map f' = dtor_unfold_J h"
  apply(rule J.dtor_unfold_unique, rule sym)
  unfolding o_assoc eval_step[symmetric]
  unfolding o_assoc[symmetric] \<Sigma>\<Sigma>_step.map_comp0[symmetric]
  unfolding convol_comp_id1[symmetric] unfolding f'[symmetric]
  apply(subst f'_id)
  unfolding o_assoc \<Sigma>\<Sigma>_step.map_comp0
  apply(subst o_assoc[symmetric])
  unfolding o_assoc[symmetric] F_map_comp
  unfolding h_def apply(rule sym)
  unfolding o_assoc apply(subst o_assoc[symmetric])
  unfolding dd_step_natural[symmetric] unfolding o_assoc[symmetric]
  unfolding \<Sigma>\<Sigma>_step.map_comp0[symmetric] map_prod_o_convol ..
  (*  *)
  have AA: "<id , cut\<Sigma>\<Sigma>_stepOc s> = (flat_step ** F_map flat_step) o (id ** dd_step) o <leaf_step, \<Sigma>\<Sigma>_step_map <leaf_step , s>>"
  unfolding map_prod_o_convol o_assoc map_prod.comp cut\<Sigma>\<Sigma>_stepOc_def o_id flat_step_leaf_step ..
  have BB: "flat_step ** F_map flat_step \<circ> id ** dd_step \<circ> <leaf_step , \<Sigma>\<Sigma>_step_map <leaf_step , s>> = flat_step ** F_map flat_step \<circ> id ** dd_step \<circ> <\<Sigma>\<Sigma>_step_map leaf_step , \<Sigma>\<Sigma>_step_map <leaf_step , s>>"
  unfolding map_prod.comp unfolding map_prod_o_convol unfolding o_id unfolding flat_step_leaf_step leaf_step_flat_step ..
  show "dtor_unfold_J h = f' \<circ> flat_step"
  apply(rule J.dtor_unfold_unique[symmetric], rule sym)
  unfolding o_assoc f'[symmetric]
  unfolding F_map_comp o_assoc[symmetric]
  apply(rule arg_cong[of _ _ "op o (F_map f')"])
  unfolding h_def
  unfolding AA BB
  unfolding \<Sigma>\<Sigma>_step.map_comp0 apply(rule sym)
  unfolding o_assoc apply(subst o_assoc[symmetric])
  unfolding dd_step_natural
  unfolding o_assoc F_map_comp[symmetric]
  unfolding flat_step_assoc unfolding F_map_comp
  unfolding cut\<Sigma>\<Sigma>_stepOc_def o_assoc[symmetric] apply(rule arg_cong[of _ _ "op o (F_map flat_step)"])
  unfolding o_assoc
  unfolding o_assoc[symmetric] unfolding \<Sigma>\<Sigma>_step.map_comp0[symmetric] unfolding map_prod_o_convol id_o
  unfolding flat_step_natural[symmetric] unfolding o_assoc
  unfolding dd_step_flat_step[symmetric] unfolding o_assoc[symmetric] unfolding \<Sigma>\<Sigma>_step.map_comp0[symmetric]
  unfolding convol_o unfolding \<Sigma>\<Sigma>_step.map_comp0[symmetric] unfolding fst_convol ..
qed

(* restr is wedd_step-defined:  *)
lemma restr_mor:
assumes f': "F_map f' o cut\<Sigma>\<Sigma>_stepOc s = dtor_J o f'"
shows "F_map (extdd_step (restr f')) o s = dtor_J o restr f'"
unfolding extdd_step_def restr_def \<Sigma>\<Sigma>_step.map_comp0
unfolding o_assoc mor_cut\<Sigma>\<Sigma>_stepOc_flat_step[OF f']
unfolding o_assoc[symmetric] leaf_step_flat_step o_id
unfolding o_assoc f'[symmetric]
unfolding o_assoc[symmetric] c\<Sigma>\<Sigma>_stepOcut_cut\<Sigma>\<Sigma>_stepOc[unfolded c\<Sigma>\<Sigma>_stepOcut_def] ..

lemma extdd_step_restr:
assumes f': "F_map f' o cut\<Sigma>\<Sigma>_stepOc s = dtor_J o f'"
shows "extdd_step (restr f') = f'"
proof-
  have "f' = eval_step o \<Sigma>\<Sigma>_step_map f' o leaf_step"
  unfolding o_assoc[symmetric] leaf_step_natural
  unfolding o_assoc eval_step_leaf_step by simp
  also have "... = eval_step o \<Sigma>\<Sigma>_step_map (f' o leaf_step)"
  unfolding \<Sigma>\<Sigma>_step.map_comp0 o_assoc
  unfolding mor_cut\<Sigma>\<Sigma>_stepOc_flat_step[OF f'] unfolding o_assoc[symmetric] flat_step_leaf_step leaf_step_flat_step ..
  finally have A: "f' = eval_step o \<Sigma>\<Sigma>_step_map (f' o leaf_step)" .
  show ?thesis unfolding extdd_step_def restr_def A[symmetric] ..
qed

lemma restr_inj:
assumes f_step': "F_map f_step' o cut\<Sigma>\<Sigma>_stepOc s = dtor_J o f_step'"
and f2': "F_map f2' o cut\<Sigma>\<Sigma>_stepOc s = dtor_J o f2'"
shows "restr f_step' = restr f2' \<longleftrightarrow> f_step' = f2'"
using extdd_step_restr[OF f_step'] extdd_step_restr[OF f2'] by metis

lemma extdd_step_surj:
assumes f': "F_map f' o cut\<Sigma>\<Sigma>_stepOc s = dtor_J o f'"
shows "\<exists> f. extdd_step f = f'"
using extdd_step_restr[OF f'] by(rule exI[of _ "restr f'"])

lemma restr_extdd_step:
assumes f: "F_map (extdd_step f) o s = dtor_J o f"
shows "restr (extdd_step f) = f"
proof-
  have "dtor_J o f = F_map (extdd_step f) o s" using assms unfolding extdd_step_def by (rule sym)
  also have "... = dtor_J o restr (extdd_step f)"
  unfolding restr_def unfolding o_assoc extdd_step_mor[OF f, symmetric]
  unfolding o_assoc[symmetric] c\<Sigma>\<Sigma>_stepOcut_cut\<Sigma>\<Sigma>_stepOc[unfolded c\<Sigma>\<Sigma>_stepOcut_def] ..
  finally have "dtor_J o f = dtor_J \<circ> restr (extdd_step f)" .
  thus ?thesis unfolding dtor_J_o_inj by (rule sym)
qed

lemma extdd_step_inj:
assumes f1: "F_map (extdd_step f1) o s = dtor_J o f1"
and f2: "F_map (extdd_step f2) o s = dtor_J o f2"
shows "extdd_step f1 = extdd_step f2 \<longleftrightarrow> f1 = f2"
using restr_extdd_step[OF f1] restr_extdd_step[OF f2] by metis

lemma restr_surj:
assumes f: "F_map (extdd_step f) o s = dtor_J o f"
shows "\<exists> f'. restr f' = f"
using restr_extdd_step[OF f] by(rule exI[of _ "extdd_step f"])


subsection{* Coiteration up-to *}

definition "unfoldU_step s \<equiv> restr (dtor_unfold_J (cut\<Sigma>\<Sigma>_stepOc s))"

theorem unfoldU_step_pointfree:
"F_map (extdd_step (unfoldU_step s)) o s = dtor_J o unfoldU_step s"
unfolding unfoldU_step_def apply(rule restr_mor)
unfolding dtor_unfold_J_pointfree ..

theorem unfoldU_step: "F_map (extdd_step (unfoldU_step s)) (s a) = dtor_J (unfoldU_step s a)"
using unfoldU_step_pointfree unfolding o_def fun_eq_iff by(rule allE)

theorem unfoldU_step_ctor_J:
"ctor_J (F_map (extdd_step (unfoldU_step s)) (s a)) = unfoldU_step s a"
using unfoldU_step by (metis J.ctor_dtor)

theorem unfoldU_step_unique:
assumes "F_map (extdd_step f) o s = dtor_J o f"
shows "f = unfoldU_step s"
proof-
  note f = extdd_step_mor[OF assms]  note co = extdd_step_mor[OF unfoldU_step_pointfree]
  have A: "extdd_step f = extdd_step (unfoldU_step s)"
  proof(rule trans)
    show "extdd_step f = dtor_unfold_J (cut\<Sigma>\<Sigma>_stepOc s)" apply(rule J.dtor_unfold_unique) using f .
    show "dtor_unfold_J (cut\<Sigma>\<Sigma>_stepOc s) = extdd_step (unfoldU_step s)"
     apply(rule J.dtor_unfold_unique[symmetric]) using co .
  qed
  show ?thesis using A unfolding extdd_step_inj[OF assms unfoldU_step_pointfree] .
qed

lemma unfoldU_step_ctor_J_pointfree:
"ctor_J o F_map (extdd_step (unfoldU_step s)) o s = unfoldU_step s"
unfolding o_def fun_eq_iff by (subst unfoldU_step_ctor_J[symmetric]) (rule allI, rule refl)

(* Corecursion up to: *)
definition corecU_step :: "('a \<Rightarrow> (J + 'a) \<Sigma>\<Sigma>_step F) \<Rightarrow> 'a \<Rightarrow> J" where
"corecU_step s = unfoldU_step (case_sum (dd_step o leaf_step o <Inl, F_map Inl o dtor_J>) s) o Inr"

definition extddRec_step where
"extddRec_step f \<equiv> eval_step \<circ> \<Sigma>\<Sigma>_step_map (case_sum id f)"

lemma unfoldU_step_Inl:
"unfoldU_step (case_sum (dd_step \<circ> leaf_step \<circ> <Inl , F_map Inl \<circ> dtor_J>) s) o Inl = id"
(is "?L = ?R")
proof-
  have "?L = unfoldU_step (dd_step o leaf_step o <id, dtor_J>)"
  apply(rule unfoldU_step_unique)
  unfolding o_assoc unfoldU_step_pointfree[symmetric]
  unfolding o_assoc[symmetric] case_sum_o_inj extdd_step_def F_map_comp \<Sigma>\<Sigma>_step.map_comp0
  unfolding o_assoc apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric],
                          subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
  unfolding dd_step_natural[symmetric]
  apply(subst o_assoc[symmetric]) unfolding leaf_step_natural
  unfolding o_assoc[symmetric] map_prod_o_convol o_id ..
  also have "... = ?R"
  apply(rule sym, rule unfoldU_step_unique)
  unfolding extdd_step_def \<Sigma>\<Sigma>_step.map_id0 o_id dd_step_leaf_step
  unfolding o_assoc[symmetric] snd_convol
  unfolding o_assoc F_map_comp[symmetric] eval_step_leaf_step F_map_id id_o ..
  finally show ?thesis .
qed

theorem corecU_step_pointfree:
"F_map (extddRec_step (corecU_step s)) o s = dtor_J o corecU_step s" (is "?L = ?R")
unfolding corecU_step_def
unfolding o_assoc unfoldU_step_pointfree[symmetric] extddRec_step_def
unfolding o_assoc[symmetric] case_sum_o_inj
apply(subst unfoldU_step_Inl[symmetric, of s])
unfolding o_assoc case_sum_Inl_Inr_L extdd_step_def ..

theorem corecU_step:
"F_map (extddRec_step (corecU_step s)) (s a) = dtor_J (corecU_step s a)"
using corecU_step_pointfree unfolding o_def fun_eq_iff by(rule allE)


subsection{* Coinduction up-to *}

definition "cptdd_step R \<equiv> (\<Sigma>\<Sigma>_step_rel R ===> R) eval_step eval_step"

definition "cngdd_step R \<equiv> equivp R \<and> cptdd_step R"

lemma cngdd_step_Retr: "cngdd_step R \<Longrightarrow> cngdd_step (R \<sqinter> Retr R)"
  unfolding cngdd_step_def cptdd_step_def
  apply (erule conjE)
  apply (rule conjI[OF equivp_inf[OF _ equivp_retr]])
  apply assumption
  apply assumption
  apply (rule rel_funI)
  apply (frule predicate2D[OF \<Sigma>\<Sigma>_step_rel_inf])
  apply (erule inf2E)
  apply (rule inf2I)
  apply (erule rel_funE)
  apply assumption
  apply assumption
  apply (subst Retr_def)
  apply (subst eval_step_def)+
  apply (subst J.dtor_unfold)+
  unfolding F_rel_F_map_F_map Grp_def relcompp.simps[abs_def] conversep.simps[abs_def]
  apply auto
  unfolding eval_step_def[symmetric]
  apply (rule predicate2D[OF F_rel_mono])
  apply (rule predicate2I)
  apply (erule rel_funD)
  apply assumption
  apply (rule F_rel_\<Sigma>\<Sigma>_step_rel)
  unfolding \<Sigma>\<Sigma>_step_rel_\<Sigma>\<Sigma>_step_map_\<Sigma>\<Sigma>_step_map vimage2p_rel_prod vimage2p_id
  unfolding vimage2p_def Retr_def[symmetric]
  apply assumption
  done

(* The generated congruence: *)
definition "genCngdd_step R j1 j2 \<equiv> \<forall> R'. R \<le> R' \<and> cngdd_step R' \<longrightarrow> R' j1 j2"

lemma cngdd_step_genCngdd_step: "cngdd_step (genCngdd_step R)"
unfolding cngdd_step_def proof safe
  show "cptdd_step (genCngdd_step R)"
  unfolding cptdd_step_def rel_fun_def proof safe
    fix x y assume A: "\<Sigma>\<Sigma>_step_rel (genCngdd_step R) x y"
    show "genCngdd_step R (eval_step x) (eval_step y)"
    unfolding genCngdd_step_def[abs_def] proof safe
      fix R' assume "R \<le> R'" and 2: "cngdd_step R'"
      hence "\<Sigma>\<Sigma>_step_rel R' x y" by (metis A \<Sigma>\<Sigma>_step.rel_mono_strong genCngdd_step_def)
      thus "R' (eval_step x) (eval_step y)" using 2 unfolding cngdd_step_def cptdd_step_def rel_fun_def by auto
    qed
  qed
qed(rule equivpI, unfold reflp_def symp_def transp_def genCngdd_step_def cngdd_step_def equivp_def, auto)

lemma
    genCngdd_step_refl[intro,simp]: "genCngdd_step R j j"
and genCngdd_step_sym[intro]: "genCngdd_step R j1 j2 \<Longrightarrow> genCngdd_step R j2 j1"
and genCngdd_step_trans[intro]: "\<lbrakk>genCngdd_step R j1 j2; genCngdd_step R j2 j3\<rbrakk> \<Longrightarrow> genCngdd_step R j1 j3"
using cngdd_step_genCngdd_step unfolding cngdd_step_def equivp_def by auto

lemma genCngdd_step_eval_step_rel_fun: "(\<Sigma>\<Sigma>_step_rel (genCngdd_step R) ===> genCngdd_step R) eval_step eval_step"
using cngdd_step_genCngdd_step unfolding cngdd_step_def cptdd_step_def by auto

lemma genCngdd_step_eval_step: "\<Sigma>\<Sigma>_step_rel (genCngdd_step R) x y \<Longrightarrow> genCngdd_step R (eval_step x) (eval_step y)"
using genCngdd_step_eval_step_rel_fun unfolding rel_fun_def by auto

lemma leq_genCngdd_step: "R \<le> genCngdd_step R"
and imp_genCngdd_step[intro]: "R j1 j2 \<Longrightarrow> genCngdd_step R j1 j2"
unfolding genCngdd_step_def[abs_def] by auto

lemma genCngdd_step_minimal: "\<lbrakk>R \<le> R'; cngdd_step R'\<rbrakk> \<Longrightarrow> genCngdd_step R \<le> R'"
unfolding genCngdd_step_def[abs_def] by (metis (lifting, no_types) predicate2I)

theorem coinductionU_genCngdd_step:
assumes "\<forall> a b. R a b \<longrightarrow> F_rel (genCngdd_step R) (dtor_J a) (dtor_J b)"
shows "R a b \<longrightarrow> a = b"
proof-
  let ?R' = "genCngdd_step R"
  have "R \<le> Retr ?R'" using assms unfolding Retr_def[abs_def] by auto
  hence "R \<le> ?R' \<sqinter> Retr ?R'" using leq_genCngdd_step by auto
  moreover have "cngdd_step (?R' \<sqinter> Retr ?R')" using cngdd_step_Retr[OF cngdd_step_genCngdd_step[of R]] .
  ultimately have "?R' \<le> ?R' \<sqinter> Retr ?R'" using genCngdd_step_minimal by metis
  hence "?R' \<le> Retr ?R'" by auto
  hence "?R' a b \<longrightarrow> a = b"  unfolding Retr_def[abs_def] by (intro J.dtor_coinduct) auto
  thus ?thesis using leq_genCngdd_step by auto
qed


subsection{* Flattening from term algebra to "one-step" algebra *}

(* Since (J \<Sigma>\<Sigma>_step, eval_step) is an Eilenberg-Moore algebra (i.e., is compatible with
the monadic structure, it yields an algebra on the signature functor.
This is crucial for having suitable simplification rules. *)

(* The one-step algebra (naturally associated to \<Lambda>_step, not to dd_step): *)
definition alg\<Lambda>_step :: "J \<Sigma>_step \<Rightarrow> J" where "alg\<Lambda>_step = eval_step o \<oo>\<pp>_step o \<Sigma>_step_map leaf_step"

theorem eval_step_comp_\<oo>\<pp>_step: "eval_step o \<oo>\<pp>_step = alg\<Lambda>_step o \<Sigma>_step_map eval_step"
unfolding alg\<Lambda>_step_def
unfolding o_assoc[symmetric] \<Sigma>_step.map_comp0[symmetric]
unfolding leaf_step_natural[symmetric] unfolding \<Sigma>_step.map_comp0
apply(rule sym) unfolding o_assoc apply(subst o_assoc[symmetric])
unfolding \<oo>\<pp>_step_natural
unfolding o_assoc eval_step_flat_step[symmetric]
apply(subst o_assoc[symmetric]) unfolding flat_step_commute[symmetric]
unfolding o_assoc[symmetric] \<Sigma>_step.map_comp0[symmetric] flat_step_leaf_step \<Sigma>_step.map_id0 o_id ..

theorem eval_step_\<oo>\<pp>_step: "eval_step (\<oo>\<pp>_step t) = alg\<Lambda>_step (\<Sigma>_step_map eval_step t)"
using eval_step_comp_\<oo>\<pp>_step unfolding o_def fun_eq_iff by (rule allE)

theorem eval_step_leaf_step': "eval_step (leaf_step j) = j"
using eval_step_leaf_step unfolding o_def fun_eq_iff id_def by (rule allE)

theorem dtor_J_alg\<Lambda>_step: "dtor_J o alg\<Lambda>_step = F_map eval_step o \<Lambda>_step o \<Sigma>_step_map <id, dtor_J>"
  unfolding alg\<Lambda>_step_def eval_step_def o_assoc dtor_unfold_J_pointfree \<Lambda>_step_dd_step
  unfolding o_assoc[symmetric] \<oo>\<pp>_step_natural[symmetric] \<Sigma>_step.map_comp0[symmetric] leaf_step_natural
  ..

theorem dtor_J_alg\<Lambda>_step': "dtor_J (alg\<Lambda>_step t) = F_map eval_step (\<Lambda>_step (\<Sigma>_step_map (<id, dtor_J>) t))"
  by (rule trans[OF o_eq_dest[OF dtor_J_alg\<Lambda>_step] o_apply])

theorem ctor_J_alg\<Lambda>_step: "alg\<Lambda>_step t = ctor_J (F_map eval_step (\<Lambda>_step (\<Sigma>_step_map (<id, dtor_J>) t)))"
  by (rule iffD1[OF J.dtor_inject trans[OF dtor_J_alg\<Lambda>_step' J.dtor_ctor[symmetric]]])

(* Note: The user wi\<Lambda>_step indicate an "equation" equ :: J \<Sigma>_step \<Rightarrow> (J \<Sigma>\<Sigma>_step) F
in order to define the operation alg\<Lambda>_step :: J \<Sigma>_step \<Rightarrow> J on the final coalgebra
according to dtor_J_alg\<Lambda>_step.
The package wi\<Lambda>_step identify the polymorphic function \<Lambda>_step :: ('a \<times> 'a F) \<Sigma>_step \<Rightarrow> 'a \<Sigma>\<Sigma>_step F
such that equ = \<Lambda>_step o \<Sigma>_step <id, dtor_J>. Then the package wi\<Lambda>_step attempt to prove
automatica\<Lambda>_stepy that \<Lambda>_step is natural.  If the proof fails, the user wi\<Lambda>_step be asked to prove it.
Upon success, the distributive law is being registered.
*)

(* Customizing coinduction up-to: *)
definition "cpt\<Lambda>_step R \<equiv> (\<Sigma>_step_rel R ===> R) alg\<Lambda>_step alg\<Lambda>_step"

definition "cng\<Lambda>_step R \<equiv> equivp R \<and> cpt\<Lambda>_step R"

lemma cptdd_step_iff_cpt\<Lambda>_step: "cptdd_step R \<longleftrightarrow> cpt\<Lambda>_step R"
apply (rule iffI)
apply (unfold cpt\<Lambda>_step_def cptdd_step_def alg\<Lambda>_step_def o_assoc[symmetric]) [1]
apply (erule rel_funD[OF rel_funD[OF comp_transfer]])
apply transfer_prover

apply (unfold cpt\<Lambda>_step_def cptdd_step_def) [1]
unfolding rel_fun_def
apply (rule allI)+
apply (rule \<Sigma>\<Sigma>_step_rel_induct)
apply (simp only: eval_step_leaf_step')
unfolding eval_step_\<oo>\<pp>_step
apply (drule spec2)
apply (erule mp)
apply (rule iffD2[OF \<Sigma>_step_rel_\<Sigma>_step_map_\<Sigma>_step_map])
apply (subst vimage2p_def)
apply assumption
done

(* This is the definition of genCngdd_step we need to work with: *)
theorem genCngdd_step_def2: "genCngdd_step R j1 j2 \<longleftrightarrow> (\<forall> R'. R \<le> R' \<and> cng\<Lambda>_step R' \<longrightarrow> R' j1 j2)"
unfolding genCngdd_step_def cngdd_step_def cng\<Lambda>_step_def cptdd_step_iff_cpt\<Lambda>_step ..


subsection {* Incremental coinduction *}

interpretation I_step: Incremental where Retr = Retr and Cl = genCngdd_step
proof
  show "mono Retr" by (rule mono_retr)
next
  show "mono genCngdd_step" unfolding mono_def
  unfolding genCngdd_step_def[abs_def] by (smt order.trans predicate2I)
next
  fix r show "genCngdd_step (genCngdd_step r) = genCngdd_step r"
  by (metis cngdd_step_genCngdd_step genCngdd_step_minimal leq_genCngdd_step order_class.order.antisym)
next
  fix r show "r \<le> genCngdd_step r" by (metis leq_genCngdd_step)
next
  fix r assume "genCngdd_step r = r" thus "genCngdd_step (r \<sqinter> Retr r) = r \<sqinter> Retr r"
  by (metis antisym cngdd_step_Retr cngdd_step_genCngdd_step genCngdd_step_minimal
            inf.orderI inf_idem leq_genCngdd_step)
qed

definition ded_step where "ded_step r s \<equiv> I_step.ded r s"

theorems Ax = I_step.Ax'[unfolded ded_step_def[symmetric]]
theorems Split = I_step.Split[unfolded ded_step_def[symmetric]]
theorems Coind = I_step.Coind[unfolded ded_step_def[symmetric]]

theorem soundness_ded:
assumes "ded_step (op =) s"  shows "s \<le> (op =)"
unfolding gfp_Retr_eq[symmetric] apply(rule I_step.soundness_ded[unfolded ded_step_def[symmetric]] )
using assms unfolding gfp_Retr_eq[symmetric] ded_step_def .

unused_thms

end
