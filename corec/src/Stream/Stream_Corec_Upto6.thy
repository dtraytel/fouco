header {* Corecursion and coinduction up to *}

theory Stream_Corec_Upto6
imports Stream_Lift_to_Free6
begin


subsection{* The algebra associated to dd6 *}

definition "eval6 \<equiv> dtor_unfold_J (dd6 o \<Sigma>\<Sigma>6_map <id, dtor_J>)"

lemma eval6: "F_map eval6 o dd6 o \<Sigma>\<Sigma>6_map <id, dtor_J> = dtor_J o eval6"
  unfolding eval6_def dtor_unfold_J_pointfree unfolding o_assoc ..

lemma eval6_ctor_J: "ctor_J o F_map eval6 o dd6 o \<Sigma>\<Sigma>6_map <id, dtor_J> = eval6"
  unfolding o_def spec[OF eval6[unfolded o_def fun_eq_iff]] J.ctor_dtor ..

lemma eval6_leaf6: "eval6 \<circ> leaf6 = id"
proof (rule trans)
  show "eval6 \<circ> leaf6 = dtor_unfold_J dtor_J"
  apply(rule J.dtor_unfold_unique)
  unfolding o_assoc eval6[symmetric] unfolding o_assoc[symmetric] leaf6_natural
  apply(rule sym)
  unfolding F_map_comp o_assoc apply (subst o_assoc[symmetric])
  unfolding dd6_leaf6 unfolding o_assoc[symmetric] by simp
qed(metis F_map_id J.dtor_unfold_unique fun.map_id o_id)

lemma eval6_flat6: "eval6 \<circ> flat6 = eval6 \<circ> \<Sigma>\<Sigma>6_map eval6"
proof (rule trans)
  let ?K6 = "dtor_unfold_J (dd6 o \<Sigma>\<Sigma>6_map <\<Sigma>\<Sigma>6_map fst, dd6> o \<Sigma>\<Sigma>6_map (\<Sigma>\<Sigma>6_map <id, dtor_J>))"
  show "eval6 \<circ> flat6 = ?K6"
  apply(rule J.dtor_unfold_unique)
  unfolding F_map_comp o_assoc
  apply(subst o_assoc[symmetric], subst o_assoc[symmetric])
  unfolding dd6_flat6
  unfolding o_assoc[symmetric] \<Sigma>\<Sigma>6.map_comp0[symmetric] snd_convol
  unfolding flat6_natural
  unfolding o_assoc eval6 ..
  (*  *)
  have A: "<eval6, dtor_J o eval6> = <id,dtor_J> o eval6" by simp
  show "?K6 = eval6 \<circ> \<Sigma>\<Sigma>6_map eval6"
  apply(rule J.dtor_unfold_unique[symmetric])
  unfolding o_assoc[symmetric] \<Sigma>\<Sigma>6.map_comp0[symmetric] map_prod_o_convol id_o
  unfolding F_map_comp o_assoc
  apply(subst o_assoc[symmetric]) unfolding dd6_natural[symmetric]
  unfolding o_assoc[symmetric] \<Sigma>\<Sigma>6.map_comp0[symmetric]
  unfolding o_assoc unfolding map_prod_o_convol unfolding convol_o
  unfolding o_assoc[symmetric] \<Sigma>\<Sigma>6.map_comp0[symmetric] fst_convol \<Sigma>\<Sigma>6.map_id0 o_id
  unfolding o_assoc eval6 unfolding A unfolding convol_o id_o
  apply(rule sym) apply(subst eval6[symmetric])
  unfolding o_assoc[symmetric] \<Sigma>\<Sigma>6.map_comp0[symmetric] convol_o id_o ..
qed


subsection{* The correspondence between coalgebras up to and coalgebras *}

(* This correspondence, and add6 the lemmas of this subsection, make
sense not only for (J,dtor_J,eval6), but also for any dd6-bialgebra *)

(* Coalgebra-up-to to coalgebra and vice versa: *)
definition cut\<Sigma>\<Sigma>6Oc :: "('a \<Rightarrow> 'a \<Sigma>\<Sigma>6 F) \<Rightarrow> ('a \<Sigma>\<Sigma>6 \<Rightarrow> 'a \<Sigma>\<Sigma>6 F)"
where "cut\<Sigma>\<Sigma>6Oc s \<equiv> F_map flat6 o dd6 o \<Sigma>\<Sigma>6_map <leaf6, s>"
definition c\<Sigma>\<Sigma>6Ocut :: "('a \<Sigma>\<Sigma>6 \<Rightarrow> 'a \<Sigma>\<Sigma>6 F) \<Rightarrow> ('a \<Rightarrow> 'a \<Sigma>\<Sigma>6 F)"
where "c\<Sigma>\<Sigma>6Ocut s' \<equiv> s' o leaf6"

lemma c\<Sigma>\<Sigma>6Ocut_cut\<Sigma>\<Sigma>6Oc: "c\<Sigma>\<Sigma>6Ocut (cut\<Sigma>\<Sigma>6Oc s) = s"
unfolding c\<Sigma>\<Sigma>6Ocut_def cut\<Sigma>\<Sigma>6Oc_def
unfolding o_assoc[symmetric] unfolding leaf6_natural
unfolding o_assoc apply(subst o_assoc[symmetric])
unfolding dd6_leaf6 unfolding o_assoc F_map_comp[symmetric] flat6_leaf6
unfolding F_map_id id_o by simp

lemma cut\<Sigma>\<Sigma>6Oc_inj: "cut\<Sigma>\<Sigma>6Oc s6 = cut\<Sigma>\<Sigma>6Oc s2 \<longleftrightarrow> s6 = s2"
by (metis c\<Sigma>\<Sigma>6Ocut_cut\<Sigma>\<Sigma>6Oc)

lemma c\<Sigma>\<Sigma>6Ocut_surj: "\<exists> s'. c\<Sigma>\<Sigma>6Ocut s' = s"
using c\<Sigma>\<Sigma>6Ocut_cut\<Sigma>\<Sigma>6Oc by(rule exI[of _ "cut\<Sigma>\<Sigma>6Oc s"])

(* Morphism-up-to to morphism and vice versa: *)
(* The dd6-extension of a function *)
definition extdd6 :: "('a \<Rightarrow> J) \<Rightarrow> ('a \<Sigma>\<Sigma>6 \<Rightarrow> J)"
where "extdd6 f \<equiv> eval6 o \<Sigma>\<Sigma>6_map f"
(* The restriction of a function *)  term eval6
definition restr :: "('a \<Sigma>\<Sigma>6 \<Rightarrow> J) \<Rightarrow> ('a \<Rightarrow> J)"
where "restr f' \<equiv> f' o leaf6"

(* We think of extdd6 and restr as operating
extdd6 : Hom_dd6(s,dtor_J) \<rightarrow> Hom(cut\<Sigma>\<Sigma>6Oc s,dtor_J) and
restr : Hom(cut\<Sigma>\<Sigma>6Oc s,dtor_J) \<rightarrow> Hom_dd6(s,dtor_J), where
Hom(cut\<Sigma>\<Sigma>6Oc s,dtor_J) is the set of coalgebra morphisms betwee cut\<Sigma>\<Sigma>6Oc s and dtor_J and
Hom_dd6(s,dtor_J) is the set of coalgebra up-to-dd6-morphisms between s and dtor_J  *)

(* extdd6 is wedd6-defined: *)
lemma extdd6_mor:
assumes f:  "F_map (extdd6 f) o s = dtor_J o f"
shows "F_map (extdd6 f) o cut\<Sigma>\<Sigma>6Oc s = dtor_J o (extdd6 f)"
proof-
  have AA: "eval6 ** F_map eval6 \<circ> (\<Sigma>\<Sigma>6_map f ** F_map (\<Sigma>\<Sigma>6_map f) \<circ> <leaf6 , s>) =
            <f , F_map eval6 \<circ> (F_map (\<Sigma>\<Sigma>6_map f) \<circ> s)>"
  unfolding map_prod_o_convol unfolding leaf6_natural o_assoc eval6_leaf6 id_o  ..
  show ?thesis
  unfolding extdd6_def
  unfolding o_assoc eval6[symmetric]
  unfolding o_assoc[symmetric] \<Sigma>\<Sigma>6.map_comp0[symmetric]
  unfolding convol_comp[symmetric] id_o
  unfolding f[symmetric, unfolded extdd6_def]
  unfolding o_assoc
  apply(subst o_assoc[symmetric])
  unfolding F_map_comp o_assoc
  unfolding cut\<Sigma>\<Sigma>6Oc_def
  unfolding o_assoc
  unfolding F_map_comp[symmetric] unfolding o_assoc[symmetric]
  unfolding flat6_natural[symmetric]
  unfolding o_assoc F_map_comp
  apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
  unfolding dd6_natural[symmetric]
  unfolding o_assoc unfolding F_map_comp[symmetric] eval6_flat6
  unfolding F_map_comp apply(subst o_assoc[symmetric])
  unfolding dd6_natural[symmetric] unfolding o_assoc[symmetric] \<Sigma>\<Sigma>6.map_comp0[symmetric]
  unfolding o_assoc[symmetric] AA[unfolded o_assoc[symmetric]] ..
qed

lemma mor_cut\<Sigma>\<Sigma>6Oc_flat6:
assumes f': "F_map f' o cut\<Sigma>\<Sigma>6Oc s = dtor_J o f'"
shows "eval6 o \<Sigma>\<Sigma>6_map f' = f' o flat6"
proof(rule trans) (* this proof is clearly improvable: *)
  def h \<equiv> "dd6 o \<Sigma>\<Sigma>6_map <id,cut\<Sigma>\<Sigma>6Oc s>"
  have f'_id: "f' = f' o id" by simp
  show "eval6 \<circ> \<Sigma>\<Sigma>6_map f' = dtor_unfold_J h"
  apply(rule J.dtor_unfold_unique, rule sym)
  unfolding o_assoc eval6[symmetric]
  unfolding o_assoc[symmetric] \<Sigma>\<Sigma>6.map_comp0[symmetric]
  unfolding convol_comp_id1[symmetric] unfolding f'[symmetric]
  apply(subst f'_id)
  unfolding o_assoc \<Sigma>\<Sigma>6.map_comp0
  apply(subst o_assoc[symmetric])
  unfolding o_assoc[symmetric] F_map_comp
  unfolding h_def apply(rule sym)
  unfolding o_assoc apply(subst o_assoc[symmetric])
  unfolding dd6_natural[symmetric] unfolding o_assoc[symmetric]
  unfolding \<Sigma>\<Sigma>6.map_comp0[symmetric] map_prod_o_convol ..
  (*  *)
  have AA: "<id , cut\<Sigma>\<Sigma>6Oc s> = (flat6 ** F_map flat6) o (id ** dd6) o <leaf6, \<Sigma>\<Sigma>6_map <leaf6 , s>>"
  unfolding map_prod_o_convol o_assoc map_prod.comp cut\<Sigma>\<Sigma>6Oc_def o_id flat6_leaf6 ..
  have BB: "flat6 ** F_map flat6 \<circ> id ** dd6 \<circ> <leaf6 , \<Sigma>\<Sigma>6_map <leaf6 , s>> = flat6 ** F_map flat6 \<circ> id ** dd6 \<circ> <\<Sigma>\<Sigma>6_map leaf6 , \<Sigma>\<Sigma>6_map <leaf6 , s>>"
  unfolding map_prod.comp unfolding map_prod_o_convol unfolding o_id unfolding flat6_leaf6 leaf6_flat6 ..
  show "dtor_unfold_J h = f' \<circ> flat6"
  apply(rule J.dtor_unfold_unique[symmetric], rule sym)
  unfolding o_assoc f'[symmetric]
  unfolding F_map_comp o_assoc[symmetric]
  apply(rule arg_cong[of _ _ "op o (F_map f')"])
  unfolding h_def
  unfolding AA BB
  unfolding \<Sigma>\<Sigma>6.map_comp0 apply(rule sym)
  unfolding o_assoc apply(subst o_assoc[symmetric])
  unfolding dd6_natural
  unfolding o_assoc F_map_comp[symmetric]
  unfolding flat6_assoc unfolding F_map_comp
  unfolding cut\<Sigma>\<Sigma>6Oc_def o_assoc[symmetric] apply(rule arg_cong[of _ _ "op o (F_map flat6)"])
  unfolding o_assoc
  unfolding o_assoc[symmetric] unfolding \<Sigma>\<Sigma>6.map_comp0[symmetric] unfolding map_prod_o_convol id_o
  unfolding flat6_natural[symmetric] unfolding o_assoc
  unfolding dd6_flat6[symmetric] unfolding o_assoc[symmetric] unfolding \<Sigma>\<Sigma>6.map_comp0[symmetric]
  unfolding convol_o unfolding \<Sigma>\<Sigma>6.map_comp0[symmetric] unfolding fst_convol ..
qed

(* restr is wedd6-defined:  *)
lemma restr_mor:
assumes f': "F_map f' o cut\<Sigma>\<Sigma>6Oc s = dtor_J o f'"
shows "F_map (extdd6 (restr f')) o s = dtor_J o restr f'"
unfolding extdd6_def restr_def \<Sigma>\<Sigma>6.map_comp0
unfolding o_assoc mor_cut\<Sigma>\<Sigma>6Oc_flat6[OF f']
unfolding o_assoc[symmetric] leaf6_flat6 o_id
unfolding o_assoc f'[symmetric]
unfolding o_assoc[symmetric] c\<Sigma>\<Sigma>6Ocut_cut\<Sigma>\<Sigma>6Oc[unfolded c\<Sigma>\<Sigma>6Ocut_def] ..

lemma extdd6_restr:
assumes f': "F_map f' o cut\<Sigma>\<Sigma>6Oc s = dtor_J o f'"
shows "extdd6 (restr f') = f'"
proof-
  have "f' = eval6 o \<Sigma>\<Sigma>6_map f' o leaf6"
  unfolding o_assoc[symmetric] leaf6_natural
  unfolding o_assoc eval6_leaf6 by simp
  also have "... = eval6 o \<Sigma>\<Sigma>6_map (f' o leaf6)"
  unfolding \<Sigma>\<Sigma>6.map_comp0 o_assoc
  unfolding mor_cut\<Sigma>\<Sigma>6Oc_flat6[OF f'] unfolding o_assoc[symmetric] flat6_leaf6 leaf6_flat6 ..
  finally have A: "f' = eval6 o \<Sigma>\<Sigma>6_map (f' o leaf6)" .
  show ?thesis unfolding extdd6_def restr_def A[symmetric] ..
qed

lemma restr_inj:
assumes f6': "F_map f6' o cut\<Sigma>\<Sigma>6Oc s = dtor_J o f6'"
and f2': "F_map f2' o cut\<Sigma>\<Sigma>6Oc s = dtor_J o f2'"
shows "restr f6' = restr f2' \<longleftrightarrow> f6' = f2'"
using extdd6_restr[OF f6'] extdd6_restr[OF f2'] by metis

lemma extdd6_surj:
assumes f': "F_map f' o cut\<Sigma>\<Sigma>6Oc s = dtor_J o f'"
shows "\<exists> f. extdd6 f = f'"
using extdd6_restr[OF f'] by(rule exI[of _ "restr f'"])

lemma restr_extdd6:
assumes f: "F_map (extdd6 f) o s = dtor_J o f"
shows "restr (extdd6 f) = f"
proof-
  have "dtor_J o f = F_map (extdd6 f) o s" using assms unfolding extdd6_def by (rule sym)
  also have "... = dtor_J o restr (extdd6 f)"
  unfolding restr_def unfolding o_assoc extdd6_mor[OF f, symmetric]
  unfolding o_assoc[symmetric] c\<Sigma>\<Sigma>6Ocut_cut\<Sigma>\<Sigma>6Oc[unfolded c\<Sigma>\<Sigma>6Ocut_def] ..
  finally have "dtor_J o f = dtor_J \<circ> restr (extdd6 f)" .
  thus ?thesis unfolding dtor_J_o_inj by (rule sym)
qed

lemma extdd6_inj:
assumes f1: "F_map (extdd6 f1) o s = dtor_J o f1"
and f2: "F_map (extdd6 f2) o s = dtor_J o f2"
shows "extdd6 f1 = extdd6 f2 \<longleftrightarrow> f1 = f2"
using restr_extdd6[OF f1] restr_extdd6[OF f2] by metis

lemma restr_surj:
assumes f: "F_map (extdd6 f) o s = dtor_J o f"
shows "\<exists> f'. restr f' = f"
using restr_extdd6[OF f] by(rule exI[of _ "extdd6 f"])


subsection{* Coiteration up-to *}

definition "unfoldU6 s \<equiv> restr (dtor_unfold_J (cut\<Sigma>\<Sigma>6Oc s))"

theorem unfoldU6_pointfree:
"F_map (extdd6 (unfoldU6 s)) o s = dtor_J o unfoldU6 s"
unfolding unfoldU6_def apply(rule restr_mor)
unfolding dtor_unfold_J_pointfree ..

theorem unfoldU6: "F_map (extdd6 (unfoldU6 s)) (s a) = dtor_J (unfoldU6 s a)"
using unfoldU6_pointfree unfolding o_def fun_eq_iff by(rule allE)

theorem unfoldU6_ctor_J:
"ctor_J (F_map (extdd6 (unfoldU6 s)) (s a)) = unfoldU6 s a"
using unfoldU6 by (metis J.ctor_dtor)

theorem unfoldU6_unique:
assumes "F_map (extdd6 f) o s = dtor_J o f"
shows "f = unfoldU6 s"
proof-
  note f = extdd6_mor[OF assms]  note co = extdd6_mor[OF unfoldU6_pointfree]
  have A: "extdd6 f = extdd6 (unfoldU6 s)"
  proof(rule trans)
    show "extdd6 f = dtor_unfold_J (cut\<Sigma>\<Sigma>6Oc s)" apply(rule J.dtor_unfold_unique) using f .
    show "dtor_unfold_J (cut\<Sigma>\<Sigma>6Oc s) = extdd6 (unfoldU6 s)"
     apply(rule J.dtor_unfold_unique[symmetric]) using co .
  qed
  show ?thesis using A unfolding extdd6_inj[OF assms unfoldU6_pointfree] .
qed

lemma unfoldU6_ctor_J_pointfree:
"ctor_J o F_map (extdd6 (unfoldU6 s)) o s = unfoldU6 s"
unfolding o_def fun_eq_iff by (subst unfoldU6_ctor_J[symmetric]) (rule allI, rule refl)

(* Corecursion up to: *)
definition corecU6 :: "('a \<Rightarrow> (J + 'a) \<Sigma>\<Sigma>6 F) \<Rightarrow> 'a \<Rightarrow> J" where
"corecU6 s = unfoldU6 (case_sum (dd6 o leaf6 o <Inl, F_map Inl o dtor_J>) s) o Inr"

definition extddRec6 where
"extddRec6 f \<equiv> eval6 \<circ> \<Sigma>\<Sigma>6_map (case_sum id f)"

lemma unfoldU6_Inl:
"unfoldU6 (case_sum (dd6 \<circ> leaf6 \<circ> <Inl , F_map Inl \<circ> dtor_J>) s) o Inl = id"
(is "?L = ?R")
proof-
  have "?L = unfoldU6 (dd6 o leaf6 o <id, dtor_J>)"
  apply(rule unfoldU6_unique)
  unfolding o_assoc unfoldU6_pointfree[symmetric]
  unfolding o_assoc[symmetric] case_sum_o_inj extdd6_def F_map_comp \<Sigma>\<Sigma>6.map_comp0
  unfolding o_assoc apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric],
                          subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
  unfolding dd6_natural[symmetric]
  apply(subst o_assoc[symmetric]) unfolding leaf6_natural
  unfolding o_assoc[symmetric] map_prod_o_convol o_id ..
  also have "... = ?R"
  apply(rule sym, rule unfoldU6_unique)
  unfolding extdd6_def \<Sigma>\<Sigma>6.map_id0 o_id dd6_leaf6
  unfolding o_assoc[symmetric] snd_convol
  unfolding o_assoc F_map_comp[symmetric] eval6_leaf6 F_map_id id_o ..
  finally show ?thesis .
qed

theorem corecU6_pointfree:
"F_map (extddRec6 (corecU6 s)) o s = dtor_J o corecU6 s" (is "?L = ?R")
unfolding corecU6_def
unfolding o_assoc unfoldU6_pointfree[symmetric] extddRec6_def
unfolding o_assoc[symmetric] case_sum_o_inj
apply(subst unfoldU6_Inl[symmetric, of s])
unfolding o_assoc case_sum_Inl_Inr_L extdd6_def ..

theorem corecU6:
"F_map (extddRec6 (corecU6 s)) (s a) = dtor_J (corecU6 s a)"
using corecU6_pointfree unfolding o_def fun_eq_iff by(rule allE)


subsection{* Coinduction up-to *}

definition "cptdd6 R \<equiv> (\<Sigma>\<Sigma>6_rel R ===> R) eval6 eval6"

definition "cngdd6 R \<equiv> equivp R \<and> cptdd6 R"

lemma cngdd6_Retr: "cngdd6 R \<Longrightarrow> cngdd6 (R \<sqinter> Retr R)"
  unfolding cngdd6_def cptdd6_def
  apply (erule conjE)
  apply (rule conjI[OF equivp_inf[OF _ equivp_retr]])
  apply assumption
  apply assumption
  apply (rule rel_funI)
  apply (frule predicate2D[OF \<Sigma>\<Sigma>6_rel_inf])
  apply (erule inf2E)
  apply (rule inf2I)
  apply (erule rel_funE)
  apply assumption
  apply assumption
  apply (subst Retr_def)
  apply (subst eval6_def)+
  apply (subst J.dtor_unfold)+
  unfolding F_rel_F_map_F_map Grp_def relcompp.simps[abs_def] conversep.simps[abs_def]
  apply auto
  unfolding eval6_def[symmetric]
  apply (rule predicate2D[OF F_rel_mono])
  apply (rule predicate2I)
  apply (erule rel_funD)
  apply assumption
  apply (rule F_rel_\<Sigma>\<Sigma>6_rel)
  unfolding \<Sigma>\<Sigma>6_rel_\<Sigma>\<Sigma>6_map_\<Sigma>\<Sigma>6_map vimage2p_rel_prod vimage2p_id
  unfolding vimage2p_def Retr_def[symmetric]
  apply assumption
  done

(* The generated congruence: *)
definition "genCngdd6 R j1 j2 \<equiv> \<forall> R'. R \<le> R' \<and> cngdd6 R' \<longrightarrow> R' j1 j2"

lemma cngdd6_genCngdd6: "cngdd6 (genCngdd6 R)"
unfolding cngdd6_def proof safe
  show "cptdd6 (genCngdd6 R)"
  unfolding cptdd6_def rel_fun_def proof safe
    fix x y assume A: "\<Sigma>\<Sigma>6_rel (genCngdd6 R) x y"
    show "genCngdd6 R (eval6 x) (eval6 y)"
    unfolding genCngdd6_def[abs_def] proof safe
      fix R' assume "R \<le> R'" and 2: "cngdd6 R'"
      hence "\<Sigma>\<Sigma>6_rel R' x y" by (metis A \<Sigma>\<Sigma>6.rel_mono_strong genCngdd6_def)
      thus "R' (eval6 x) (eval6 y)" using 2 unfolding cngdd6_def cptdd6_def rel_fun_def by auto
    qed
  qed
qed(rule equivpI, unfold reflp_def symp_def transp_def genCngdd6_def cngdd6_def equivp_def, auto)

lemma
    genCngdd6_refl[intro,simp]: "genCngdd6 R j j"
and genCngdd6_sym[intro]: "genCngdd6 R j1 j2 \<Longrightarrow> genCngdd6 R j2 j1"
and genCngdd6_trans[intro]: "\<lbrakk>genCngdd6 R j1 j2; genCngdd6 R j2 j3\<rbrakk> \<Longrightarrow> genCngdd6 R j1 j3"
using cngdd6_genCngdd6 unfolding cngdd6_def equivp_def by auto

lemma genCngdd6_eval6_rel_fun: "(\<Sigma>\<Sigma>6_rel (genCngdd6 R) ===> genCngdd6 R) eval6 eval6"
using cngdd6_genCngdd6 unfolding cngdd6_def cptdd6_def by auto

lemma genCngdd6_eval6: "\<Sigma>\<Sigma>6_rel (genCngdd6 R) x y \<Longrightarrow> genCngdd6 R (eval6 x) (eval6 y)"
using genCngdd6_eval6_rel_fun unfolding rel_fun_def by auto

lemma leq_genCngdd6: "R \<le> genCngdd6 R"
and imp_genCngdd6[intro]: "R j1 j2 \<Longrightarrow> genCngdd6 R j1 j2"
unfolding genCngdd6_def[abs_def] by auto

lemma genCngdd6_minimal: "\<lbrakk>R \<le> R'; cngdd6 R'\<rbrakk> \<Longrightarrow> genCngdd6 R \<le> R'"
unfolding genCngdd6_def[abs_def] by (metis (lifting, no_types) predicate2I)

theorem coinductionU_genCngdd6:
assumes "\<forall> a b. R a b \<longrightarrow> F_rel (genCngdd6 R) (dtor_J a) (dtor_J b)"
shows "R a b \<longrightarrow> a = b"
proof-
  let ?R' = "genCngdd6 R"
  have "R \<le> Retr ?R'" using assms unfolding Retr_def[abs_def] by auto
  hence "R \<le> ?R' \<sqinter> Retr ?R'" using leq_genCngdd6 by auto
  moreover have "cngdd6 (?R' \<sqinter> Retr ?R')" using cngdd6_Retr[OF cngdd6_genCngdd6[of R]] .
  ultimately have "?R' \<le> ?R' \<sqinter> Retr ?R'" using genCngdd6_minimal by metis
  hence "?R' \<le> Retr ?R'" by auto
  hence "?R' a b \<longrightarrow> a = b"  unfolding Retr_def[abs_def] by (intro J.dtor_coinduct) auto
  thus ?thesis using leq_genCngdd6 by auto
qed


subsection{* Flattening from term algebra to "one-step" algebra *}

(* Since (J \<Sigma>\<Sigma>6, eval6) is an Eilenberg-Moore algebra (i.e., is compatible with
the monadic structure, it yields an algebra on the signature functor.
This is crucial for having suitable simplification rules. *)

(* The one-step algebra (naturally associated to \<Lambda>6, not to dd6): *)
definition alg\<Lambda>6 :: "J \<Sigma>6 \<Rightarrow> J" where "alg\<Lambda>6 = eval6 o \<oo>\<pp>6 o \<Sigma>6_map leaf6"

theorem eval6_comp_\<oo>\<pp>6: "eval6 o \<oo>\<pp>6 = alg\<Lambda>6 o \<Sigma>6_map eval6"
unfolding alg\<Lambda>6_def
unfolding o_assoc[symmetric] \<Sigma>6.map_comp0[symmetric]
unfolding leaf6_natural[symmetric] unfolding \<Sigma>6.map_comp0
apply(rule sym) unfolding o_assoc apply(subst o_assoc[symmetric])
unfolding \<oo>\<pp>6_natural
unfolding o_assoc eval6_flat6[symmetric]
apply(subst o_assoc[symmetric]) unfolding flat6_commute[symmetric]
unfolding o_assoc[symmetric] \<Sigma>6.map_comp0[symmetric] flat6_leaf6 \<Sigma>6.map_id0 o_id ..

theorem eval6_\<oo>\<pp>6: "eval6 (\<oo>\<pp>6 t) = alg\<Lambda>6 (\<Sigma>6_map eval6 t)"
using eval6_comp_\<oo>\<pp>6 unfolding o_def fun_eq_iff by (rule allE)

theorem eval6_leaf6': "eval6 (leaf6 j) = j"
using eval6_leaf6 unfolding o_def fun_eq_iff id_def by (rule allE)

theorem dtor_J_alg\<Lambda>6: "dtor_J o alg\<Lambda>6 = F_map eval6 o \<Lambda>6 o \<Sigma>6_map <id, dtor_J>"
  unfolding alg\<Lambda>6_def eval6_def o_assoc dtor_unfold_J_pointfree \<Lambda>6_dd6
  unfolding o_assoc[symmetric] \<oo>\<pp>6_natural[symmetric] \<Sigma>6.map_comp0[symmetric] leaf6_natural
  ..

theorem dtor_J_alg\<Lambda>6': "dtor_J (alg\<Lambda>6 t) = F_map eval6 (\<Lambda>6 (\<Sigma>6_map (<id, dtor_J>) t))"
  by (rule trans[OF o_eq_dest[OF dtor_J_alg\<Lambda>6] o_apply])

theorem ctor_J_alg\<Lambda>6: "alg\<Lambda>6 t = ctor_J (F_map eval6 (\<Lambda>6 (\<Sigma>6_map (<id, dtor_J>) t)))"
  by (rule iffD1[OF J.dtor_inject trans[OF dtor_J_alg\<Lambda>6' J.dtor_ctor[symmetric]]])

(* Note: The user wi\<Lambda>6 indicate an "equation" equ :: J \<Sigma>6 \<Rightarrow> (J \<Sigma>\<Sigma>6) F
in order to define the operation alg\<Lambda>6 :: J \<Sigma>6 \<Rightarrow> J on the final coalgebra
according to dtor_J_alg\<Lambda>6.
The package wi\<Lambda>6 identify the polymorphic function \<Lambda>6 :: ('a \<times> 'a F) \<Sigma>6 \<Rightarrow> 'a \<Sigma>\<Sigma>6 F
such that equ = \<Lambda>6 o \<Sigma>6 <id, dtor_J>. Then the package wi\<Lambda>6 attempt to prove
automatica\<Lambda>6y that \<Lambda>6 is natural.  If the proof fails, the user wi\<Lambda>6 be asked to prove it.
Upon success, the distributive law is being registered.
*)

(* Customizing coinduction up-to: *)
definition "cpt\<Lambda>6 R \<equiv> (\<Sigma>6_rel R ===> R) alg\<Lambda>6 alg\<Lambda>6"

definition "cng\<Lambda>6 R \<equiv> equivp R \<and> cpt\<Lambda>6 R"

lemma cptdd6_iff_cpt\<Lambda>6: "cptdd6 R \<longleftrightarrow> cpt\<Lambda>6 R"
apply (rule iffI)
apply (unfold cpt\<Lambda>6_def cptdd6_def alg\<Lambda>6_def o_assoc[symmetric]) [1]
apply (erule rel_funD[OF rel_funD[OF comp_transfer]])
apply transfer_prover

apply (unfold cpt\<Lambda>6_def cptdd6_def) [1]
unfolding rel_fun_def
apply (rule allI)+
apply (rule \<Sigma>\<Sigma>6_rel_induct)
apply (simp only: eval6_leaf6')
unfolding eval6_\<oo>\<pp>6
apply (drule spec2)
apply (erule mp)
apply (rule iffD2[OF \<Sigma>6_rel_\<Sigma>6_map_\<Sigma>6_map])
apply (subst vimage2p_def)
apply assumption
done

(* This is the definition of genCngdd6 we need to work with: *)
theorem genCngdd6_def2: "genCngdd6 R j1 j2 \<longleftrightarrow> (\<forall> R'. R \<le> R' \<and> cng\<Lambda>6 R' \<longrightarrow> R' j1 j2)"
unfolding genCngdd6_def cngdd6_def cng\<Lambda>6_def cptdd6_iff_cpt\<Lambda>6 ..


subsection {* Incremental coinduction *}

interpretation I6: Incremental where Retr = Retr and Cl = genCngdd6
proof
  show "mono Retr" by (rule mono_retr)
next
  show "mono genCngdd6" unfolding mono_def
  unfolding genCngdd6_def[abs_def] by (smt order.trans predicate2I)
next
  fix r show "genCngdd6 (genCngdd6 r) = genCngdd6 r"
  by (metis cngdd6_genCngdd6 genCngdd6_minimal leq_genCngdd6 order_class.order.antisym)
next
  fix r show "r \<le> genCngdd6 r" by (metis leq_genCngdd6)
next
  fix r assume "genCngdd6 r = r" thus "genCngdd6 (r \<sqinter> Retr r) = r \<sqinter> Retr r"
  by (metis antisym cngdd6_Retr cngdd6_genCngdd6 genCngdd6_minimal
            inf.orderI inf_idem leq_genCngdd6)
qed

definition ded6 where "ded6 r s \<equiv> I6.ded r s"

theorems Ax = I6.Ax'[unfolded ded6_def[symmetric]]
theorems Split = I6.Split[unfolded ded6_def[symmetric]]
theorems Coind = I6.Coind[unfolded ded6_def[symmetric]]

theorem soundness_ded:
assumes "ded6 (op =) s"  shows "s \<le> (op =)"
unfolding gfp_Retr_eq[symmetric] apply(rule I6.soundness_ded[unfolded ded6_def[symmetric]] )
using assms unfolding gfp_Retr_eq[symmetric] ded6_def .

unused_thms

end
