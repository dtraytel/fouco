header {* Corecursion and coinduction up to *}

theory Tree_Corec_Upto1
imports Tree_Lift_to_Free1
begin


subsection{* The algebra associated to dd1 *}

definition "eval1 \<equiv> dtor_unfold_J (dd1 o \<Sigma>\<Sigma>1_map <id, dtor_J>)"

lemma eval1: "F_map eval1 o dd1 o \<Sigma>\<Sigma>1_map <id, dtor_J> = dtor_J o eval1"
  unfolding eval1_def dtor_unfold_J_pointfree unfolding o_assoc ..

lemma eval1_ctor_J: "ctor_J o F_map eval1 o dd1 o \<Sigma>\<Sigma>1_map <id, dtor_J> = eval1"
  unfolding o_def spec[OF eval1[unfolded o_def fun_eq_iff]] J.ctor_dtor ..

lemma eval1_leaf1: "eval1 \<circ> leaf1 = id"
proof (rule trans)
  show "eval1 \<circ> leaf1 = dtor_unfold_J dtor_J"
  apply(rule J.dtor_unfold_unique)
  unfolding o_assoc eval1[symmetric] unfolding o_assoc[symmetric] leaf1_natural
  apply(rule sym)
  unfolding F_map_comp o_assoc apply (subst o_assoc[symmetric])
  unfolding dd1_leaf1 unfolding o_assoc[symmetric] by simp
qed(metis F_map_id J.dtor_unfold_unique fun.map_id o_id)

lemma eval1_flat1: "eval1 \<circ> flat1 = eval1 \<circ> \<Sigma>\<Sigma>1_map eval1"
proof (rule trans)
  let ?K1 = "dtor_unfold_J (dd1 o \<Sigma>\<Sigma>1_map <\<Sigma>\<Sigma>1_map fst, dd1> o \<Sigma>\<Sigma>1_map (\<Sigma>\<Sigma>1_map <id, dtor_J>))"
  show "eval1 \<circ> flat1 = ?K1"
  apply(rule J.dtor_unfold_unique)
  unfolding F_map_comp o_assoc
  apply(subst o_assoc[symmetric], subst o_assoc[symmetric])
  unfolding dd1_flat1
  unfolding o_assoc[symmetric] \<Sigma>\<Sigma>1.map_comp0[symmetric] snd_convol
  unfolding flat1_natural
  unfolding o_assoc eval1 ..
  (*  *)
  have A: "<eval1, dtor_J o eval1> = <id,dtor_J> o eval1" by simp
  show "?K1 = eval1 \<circ> \<Sigma>\<Sigma>1_map eval1"
  apply(rule J.dtor_unfold_unique[symmetric])
  unfolding o_assoc[symmetric] \<Sigma>\<Sigma>1.map_comp0[symmetric] map_prod_o_convol id_o
  unfolding F_map_comp o_assoc
  apply(subst o_assoc[symmetric]) unfolding dd1_natural[symmetric]
  unfolding o_assoc[symmetric] \<Sigma>\<Sigma>1.map_comp0[symmetric]
  unfolding o_assoc unfolding map_prod_o_convol unfolding convol_o
  unfolding o_assoc[symmetric] \<Sigma>\<Sigma>1.map_comp0[symmetric] fst_convol \<Sigma>\<Sigma>1.map_id0 o_id
  unfolding o_assoc eval1 unfolding A unfolding convol_o id_o
  apply(rule sym) apply(subst eval1[symmetric])
  unfolding o_assoc[symmetric] \<Sigma>\<Sigma>1.map_comp0[symmetric] convol_o id_o ..
qed


subsection{* The correspondence between coalgebras up to and coalgebras *}

(* This correspondence, and add1 the lemmas of this subsection, make
sense not only for (J,dtor_J,eval1), but also for any dd1-bialgebra *)

(* Coalgebra-up-to to coalgebra and vice versa: *)
definition cut\<Sigma>\<Sigma>1Oc :: "('a \<Rightarrow> 'a \<Sigma>\<Sigma>1 F) \<Rightarrow> ('a \<Sigma>\<Sigma>1 \<Rightarrow> 'a \<Sigma>\<Sigma>1 F)"
where "cut\<Sigma>\<Sigma>1Oc s \<equiv> F_map flat1 o dd1 o \<Sigma>\<Sigma>1_map <leaf1, s>"
definition c\<Sigma>\<Sigma>1Ocut :: "('a \<Sigma>\<Sigma>1 \<Rightarrow> 'a \<Sigma>\<Sigma>1 F) \<Rightarrow> ('a \<Rightarrow> 'a \<Sigma>\<Sigma>1 F)"
where "c\<Sigma>\<Sigma>1Ocut s' \<equiv> s' o leaf1"

lemma c\<Sigma>\<Sigma>1Ocut_cut\<Sigma>\<Sigma>1Oc: "c\<Sigma>\<Sigma>1Ocut (cut\<Sigma>\<Sigma>1Oc s) = s"
unfolding c\<Sigma>\<Sigma>1Ocut_def cut\<Sigma>\<Sigma>1Oc_def
unfolding o_assoc[symmetric] unfolding leaf1_natural
unfolding o_assoc apply(subst o_assoc[symmetric])
unfolding dd1_leaf1 unfolding o_assoc F_map_comp[symmetric] flat1_leaf1
unfolding F_map_id id_o by simp

lemma cut\<Sigma>\<Sigma>1Oc_inj: "cut\<Sigma>\<Sigma>1Oc s1 = cut\<Sigma>\<Sigma>1Oc s2 \<longleftrightarrow> s1 = s2"
by (metis c\<Sigma>\<Sigma>1Ocut_cut\<Sigma>\<Sigma>1Oc)

lemma c\<Sigma>\<Sigma>1Ocut_surj: "\<exists> s'. c\<Sigma>\<Sigma>1Ocut s' = s"
using c\<Sigma>\<Sigma>1Ocut_cut\<Sigma>\<Sigma>1Oc by(rule exI[of _ "cut\<Sigma>\<Sigma>1Oc s"])

(* Morphism-up-to to morphism and vice versa: *)
(* The dd1-extension of a function *)
definition extdd1 :: "('a \<Rightarrow> J) \<Rightarrow> ('a \<Sigma>\<Sigma>1 \<Rightarrow> J)"
where "extdd1 f \<equiv> eval1 o \<Sigma>\<Sigma>1_map f"
(* The restriction of a function *)  term eval1
definition restr :: "('a \<Sigma>\<Sigma>1 \<Rightarrow> J) \<Rightarrow> ('a \<Rightarrow> J)"
where "restr f' \<equiv> f' o leaf1"

(* We think of extdd1 and restr as operating
extdd1 : Hom_dd1(s,dtor_J) \<rightarrow> Hom(cut\<Sigma>\<Sigma>1Oc s,dtor_J) and
restr : Hom(cut\<Sigma>\<Sigma>1Oc s,dtor_J) \<rightarrow> Hom_dd1(s,dtor_J), where
Hom(cut\<Sigma>\<Sigma>1Oc s,dtor_J) is the set of coalgebra morphisms betwee cut\<Sigma>\<Sigma>1Oc s and dtor_J and
Hom_dd1(s,dtor_J) is the set of coalgebra up-to-dd1-morphisms between s and dtor_J  *)

(* extdd1 is wedd1-defined: *)
lemma extdd1_mor:
assumes f:  "F_map (extdd1 f) o s = dtor_J o f"
shows "F_map (extdd1 f) o cut\<Sigma>\<Sigma>1Oc s = dtor_J o (extdd1 f)"
proof-
  have AA: "eval1 ** F_map eval1 \<circ> (\<Sigma>\<Sigma>1_map f ** F_map (\<Sigma>\<Sigma>1_map f) \<circ> <leaf1 , s>) =
            <f , F_map eval1 \<circ> (F_map (\<Sigma>\<Sigma>1_map f) \<circ> s)>"
  unfolding map_prod_o_convol unfolding leaf1_natural o_assoc eval1_leaf1 id_o  ..
  show ?thesis
  unfolding extdd1_def
  unfolding o_assoc eval1[symmetric]
  unfolding o_assoc[symmetric] \<Sigma>\<Sigma>1.map_comp0[symmetric]
  unfolding convol_comp[symmetric] id_o
  unfolding f[symmetric, unfolded extdd1_def]
  unfolding o_assoc
  apply(subst o_assoc[symmetric])
  unfolding F_map_comp o_assoc
  unfolding cut\<Sigma>\<Sigma>1Oc_def
  unfolding o_assoc
  unfolding F_map_comp[symmetric] unfolding o_assoc[symmetric]
  unfolding flat1_natural[symmetric]
  unfolding o_assoc F_map_comp
  apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
  unfolding dd1_natural[symmetric]
  unfolding o_assoc unfolding F_map_comp[symmetric] eval1_flat1
  unfolding F_map_comp apply(subst o_assoc[symmetric])
  unfolding dd1_natural[symmetric] unfolding o_assoc[symmetric] \<Sigma>\<Sigma>1.map_comp0[symmetric]
  unfolding o_assoc[symmetric] AA[unfolded o_assoc[symmetric]] ..
qed

lemma mor_cut\<Sigma>\<Sigma>1Oc_flat1:
assumes f': "F_map f' o cut\<Sigma>\<Sigma>1Oc s = dtor_J o f'"
shows "eval1 o \<Sigma>\<Sigma>1_map f' = f' o flat1"
proof(rule trans) (* this proof is clearly improvable: *)
  def h \<equiv> "dd1 o \<Sigma>\<Sigma>1_map <id,cut\<Sigma>\<Sigma>1Oc s>"
  have f'_id: "f' = f' o id" by simp
  show "eval1 \<circ> \<Sigma>\<Sigma>1_map f' = dtor_unfold_J h"
  apply(rule J.dtor_unfold_unique, rule sym)
  unfolding o_assoc eval1[symmetric]
  unfolding o_assoc[symmetric] \<Sigma>\<Sigma>1.map_comp0[symmetric]
  unfolding convol_comp_id1[symmetric] unfolding f'[symmetric]
  apply(subst f'_id)
  unfolding o_assoc \<Sigma>\<Sigma>1.map_comp0
  apply(subst o_assoc[symmetric])
  unfolding o_assoc[symmetric] F_map_comp
  unfolding h_def apply(rule sym)
  unfolding o_assoc apply(subst o_assoc[symmetric])
  unfolding dd1_natural[symmetric] unfolding o_assoc[symmetric]
  unfolding \<Sigma>\<Sigma>1.map_comp0[symmetric] map_prod_o_convol ..
  (*  *)
  have AA: "<id , cut\<Sigma>\<Sigma>1Oc s> = (flat1 ** F_map flat1) o (id ** dd1) o <leaf1, \<Sigma>\<Sigma>1_map <leaf1 , s>>"
  unfolding map_prod_o_convol o_assoc map_prod.comp cut\<Sigma>\<Sigma>1Oc_def o_id flat1_leaf1 ..
  have BB: "flat1 ** F_map flat1 \<circ> id ** dd1 \<circ> <leaf1 , \<Sigma>\<Sigma>1_map <leaf1 , s>> = flat1 ** F_map flat1 \<circ> id ** dd1 \<circ> <\<Sigma>\<Sigma>1_map leaf1 , \<Sigma>\<Sigma>1_map <leaf1 , s>>"
  unfolding map_prod.comp unfolding map_prod_o_convol unfolding o_id unfolding flat1_leaf1 leaf1_flat1 ..
  show "dtor_unfold_J h = f' \<circ> flat1"
  apply(rule J.dtor_unfold_unique[symmetric], rule sym)
  unfolding o_assoc f'[symmetric]
  unfolding F_map_comp o_assoc[symmetric]
  apply(rule arg_cong[of _ _ "op o (F_map f')"])
  unfolding h_def
  unfolding AA BB
  unfolding \<Sigma>\<Sigma>1.map_comp0 apply(rule sym)
  unfolding o_assoc apply(subst o_assoc[symmetric])
  unfolding dd1_natural
  unfolding o_assoc F_map_comp[symmetric]
  unfolding flat1_assoc unfolding F_map_comp
  unfolding cut\<Sigma>\<Sigma>1Oc_def o_assoc[symmetric] apply(rule arg_cong[of _ _ "op o (F_map flat1)"])
  unfolding o_assoc
  unfolding o_assoc[symmetric] unfolding \<Sigma>\<Sigma>1.map_comp0[symmetric] unfolding map_prod_o_convol id_o
  unfolding flat1_natural[symmetric] unfolding o_assoc
  unfolding dd1_flat1[symmetric] unfolding o_assoc[symmetric] unfolding \<Sigma>\<Sigma>1.map_comp0[symmetric]
  unfolding convol_o unfolding \<Sigma>\<Sigma>1.map_comp0[symmetric] unfolding fst_convol ..
qed

(* restr is wedd1-defined:  *)
lemma restr_mor:
assumes f': "F_map f' o cut\<Sigma>\<Sigma>1Oc s = dtor_J o f'"
shows "F_map (extdd1 (restr f')) o s = dtor_J o restr f'"
unfolding extdd1_def restr_def \<Sigma>\<Sigma>1.map_comp0
unfolding o_assoc mor_cut\<Sigma>\<Sigma>1Oc_flat1[OF f']
unfolding o_assoc[symmetric] leaf1_flat1 o_id
unfolding o_assoc f'[symmetric]
unfolding o_assoc[symmetric] c\<Sigma>\<Sigma>1Ocut_cut\<Sigma>\<Sigma>1Oc[unfolded c\<Sigma>\<Sigma>1Ocut_def] ..

lemma extdd1_restr:
assumes f': "F_map f' o cut\<Sigma>\<Sigma>1Oc s = dtor_J o f'"
shows "extdd1 (restr f') = f'"
proof-
  have "f' = eval1 o \<Sigma>\<Sigma>1_map f' o leaf1"
  unfolding o_assoc[symmetric] leaf1_natural
  unfolding o_assoc eval1_leaf1 by simp
  also have "... = eval1 o \<Sigma>\<Sigma>1_map (f' o leaf1)"
  unfolding \<Sigma>\<Sigma>1.map_comp0 o_assoc
  unfolding mor_cut\<Sigma>\<Sigma>1Oc_flat1[OF f'] unfolding o_assoc[symmetric] flat1_leaf1 leaf1_flat1 ..
  finally have A: "f' = eval1 o \<Sigma>\<Sigma>1_map (f' o leaf1)" .
  show ?thesis unfolding extdd1_def restr_def A[symmetric] ..
qed

lemma restr_inj:
assumes f1': "F_map f1' o cut\<Sigma>\<Sigma>1Oc s = dtor_J o f1'"
and f2': "F_map f2' o cut\<Sigma>\<Sigma>1Oc s = dtor_J o f2'"
shows "restr f1' = restr f2' \<longleftrightarrow> f1' = f2'"
using extdd1_restr[OF f1'] extdd1_restr[OF f2'] by metis

lemma extdd1_surj:
assumes f': "F_map f' o cut\<Sigma>\<Sigma>1Oc s = dtor_J o f'"
shows "\<exists> f. extdd1 f = f'"
using extdd1_restr[OF f'] by(rule exI[of _ "restr f'"])

lemma restr_extdd1:
assumes f: "F_map (extdd1 f) o s = dtor_J o f"
shows "restr (extdd1 f) = f"
proof-
  have "dtor_J o f = F_map (extdd1 f) o s" using assms unfolding extdd1_def by (rule sym)
  also have "... = dtor_J o restr (extdd1 f)"
  unfolding restr_def unfolding o_assoc extdd1_mor[OF f, symmetric]
  unfolding o_assoc[symmetric] c\<Sigma>\<Sigma>1Ocut_cut\<Sigma>\<Sigma>1Oc[unfolded c\<Sigma>\<Sigma>1Ocut_def] ..
  finally have "dtor_J o f = dtor_J \<circ> restr (extdd1 f)" .
  thus ?thesis unfolding dtor_J_o_inj by (rule sym)
qed

lemma extdd1_inj:
assumes f1: "F_map (extdd1 f1) o s = dtor_J o f1"
and f2: "F_map (extdd1 f2) o s = dtor_J o f2"
shows "extdd1 f1 = extdd1 f2 \<longleftrightarrow> f1 = f2"
using restr_extdd1[OF f1] restr_extdd1[OF f2] by metis

lemma restr_surj:
assumes f: "F_map (extdd1 f) o s = dtor_J o f"
shows "\<exists> f'. restr f' = f"
using restr_extdd1[OF f] by(rule exI[of _ "extdd1 f"])


subsection{* Coiteration up-to *}

definition "unfoldU1 s \<equiv> restr (dtor_unfold_J (cut\<Sigma>\<Sigma>1Oc s))"

theorem unfoldU1_pointfree:
"F_map (extdd1 (unfoldU1 s)) o s = dtor_J o unfoldU1 s"
unfolding unfoldU1_def apply(rule restr_mor)
unfolding dtor_unfold_J_pointfree ..

theorem unfoldU1: "F_map (extdd1 (unfoldU1 s)) (s a) = dtor_J (unfoldU1 s a)"
using unfoldU1_pointfree unfolding o_def fun_eq_iff by(rule allE)

theorem unfoldU1_ctor_J:
"ctor_J (F_map (extdd1 (unfoldU1 s)) (s a)) = unfoldU1 s a"
using unfoldU1 by (metis J.ctor_dtor)

theorem unfoldU1_unique:
assumes "F_map (extdd1 f) o s = dtor_J o f"
shows "f = unfoldU1 s"
proof-
  note f = extdd1_mor[OF assms]  note co = extdd1_mor[OF unfoldU1_pointfree]
  have A: "extdd1 f = extdd1 (unfoldU1 s)"
  proof(rule trans)
    show "extdd1 f = dtor_unfold_J (cut\<Sigma>\<Sigma>1Oc s)" apply(rule J.dtor_unfold_unique) using f .
    show "dtor_unfold_J (cut\<Sigma>\<Sigma>1Oc s) = extdd1 (unfoldU1 s)"
     apply(rule J.dtor_unfold_unique[symmetric]) using co .
  qed
  show ?thesis using A unfolding extdd1_inj[OF assms unfoldU1_pointfree] .
qed

lemma unfoldU1_ctor_J_pointfree:
"ctor_J o F_map (extdd1 (unfoldU1 s)) o s = unfoldU1 s"
unfolding o_def fun_eq_iff by (subst unfoldU1_ctor_J[symmetric]) (rule allI, rule refl)

(* Corecursion up to: *)
definition corecU1 :: "('a \<Rightarrow> (J + 'a) \<Sigma>\<Sigma>1 F) \<Rightarrow> 'a \<Rightarrow> J" where
"corecU1 s = unfoldU1 (case_sum (dd1 o leaf1 o <Inl, F_map Inl o dtor_J>) s) o Inr"

definition extddRec1 where
"extddRec1 f \<equiv> eval1 \<circ> \<Sigma>\<Sigma>1_map (case_sum id f)"

lemma unfoldU1_Inl:
"unfoldU1 (case_sum (dd1 \<circ> leaf1 \<circ> <Inl , F_map Inl \<circ> dtor_J>) s) o Inl = id"
(is "?L = ?R")
proof-
  have "?L = unfoldU1 (dd1 o leaf1 o <id, dtor_J>)"
  apply(rule unfoldU1_unique)
  unfolding o_assoc unfoldU1_pointfree[symmetric]
  unfolding o_assoc[symmetric] case_sum_o_inj extdd1_def F_map_comp \<Sigma>\<Sigma>1.map_comp0
  unfolding o_assoc apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric],
                          subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
  unfolding dd1_natural[symmetric]
  apply(subst o_assoc[symmetric]) unfolding leaf1_natural
  unfolding o_assoc[symmetric] map_prod_o_convol o_id ..
  also have "... = ?R"
  apply(rule sym, rule unfoldU1_unique)
  unfolding extdd1_def \<Sigma>\<Sigma>1.map_id0 o_id dd1_leaf1
  unfolding o_assoc[symmetric] snd_convol
  unfolding o_assoc F_map_comp[symmetric] eval1_leaf1 F_map_id id_o ..
  finally show ?thesis .
qed

theorem corecU1_pointfree:
"F_map (extddRec1 (corecU1 s)) o s = dtor_J o corecU1 s" (is "?L = ?R")
unfolding corecU1_def
unfolding o_assoc unfoldU1_pointfree[symmetric] extddRec1_def
unfolding o_assoc[symmetric] case_sum_o_inj
apply(subst unfoldU1_Inl[symmetric, of s])
unfolding o_assoc case_sum_Inl_Inr_L extdd1_def ..

theorem corecU1:
"F_map (extddRec1 (corecU1 s)) (s a) = dtor_J (corecU1 s a)"
using corecU1_pointfree unfolding o_def fun_eq_iff by(rule allE)


subsection{* Coinduction up-to *}

definition "cptdd1 R \<equiv> (\<Sigma>\<Sigma>1_rel R ===> R) eval1 eval1"

definition "cngdd1 R \<equiv> equivp R \<and> cptdd1 R"

lemma cngdd1_Retr: "cngdd1 R \<Longrightarrow> cngdd1 (R \<sqinter> Retr R)"
  unfolding cngdd1_def cptdd1_def
  apply (erule conjE)
  apply (rule conjI[OF equivp_inf[OF _ equivp_retr]])
  apply assumption
  apply assumption
  apply (rule rel_funI)
  apply (frule predicate2D[OF \<Sigma>\<Sigma>1_rel_inf])
  apply (erule inf2E)
  apply (rule inf2I)
  apply (erule rel_funE)
  apply assumption
  apply assumption
  apply (subst Retr_def)
  apply (subst eval1_def)+
  apply (subst J.dtor_unfold)+
  unfolding F_rel_F_map_F_map Grp_def relcompp.simps[abs_def] conversep.simps[abs_def]
  apply auto
  unfolding eval1_def[symmetric]
  apply (rule predicate2D[OF F_rel_mono])
  apply (rule predicate2I)
  apply (erule rel_funD)
  apply assumption
  apply (rule F_rel_\<Sigma>\<Sigma>1_rel)
  unfolding \<Sigma>\<Sigma>1_rel_\<Sigma>\<Sigma>1_map_\<Sigma>\<Sigma>1_map vimage2p_rel_prod vimage2p_id
  unfolding vimage2p_def Retr_def[symmetric]
  apply assumption
  done

(* The generated congruence: *)
definition "genCngdd1 R j1 j2 \<equiv> \<forall> R'. R \<le> R' \<and> cngdd1 R' \<longrightarrow> R' j1 j2"

lemma cngdd1_genCngdd1: "cngdd1 (genCngdd1 R)"
unfolding cngdd1_def proof safe
  show "cptdd1 (genCngdd1 R)"
  unfolding cptdd1_def rel_fun_def proof safe
    fix x y assume A: "\<Sigma>\<Sigma>1_rel (genCngdd1 R) x y"
    show "genCngdd1 R (eval1 x) (eval1 y)"
    unfolding genCngdd1_def[abs_def] proof safe
      fix R' assume "R \<le> R'" and 2: "cngdd1 R'"
      hence "\<Sigma>\<Sigma>1_rel R' x y" by (metis A \<Sigma>\<Sigma>1.rel_mono_strong genCngdd1_def)
      thus "R' (eval1 x) (eval1 y)" using 2 unfolding cngdd1_def cptdd1_def rel_fun_def by auto
    qed
  qed
qed(rule equivpI, unfold reflp_def symp_def transp_def genCngdd1_def cngdd1_def equivp_def, auto)

lemma
    genCngdd1_refl[intro,simp]: "genCngdd1 R j j"
and genCngdd1_sym[intro]: "genCngdd1 R j1 j2 \<Longrightarrow> genCngdd1 R j2 j1"
and genCngdd1_trans[intro]: "\<lbrakk>genCngdd1 R j1 j2; genCngdd1 R j2 j3\<rbrakk> \<Longrightarrow> genCngdd1 R j1 j3"
using cngdd1_genCngdd1 unfolding cngdd1_def equivp_def by auto

lemma genCngdd1_eval1_rel_fun: "(\<Sigma>\<Sigma>1_rel (genCngdd1 R) ===> genCngdd1 R) eval1 eval1"
using cngdd1_genCngdd1 unfolding cngdd1_def cptdd1_def by auto

lemma genCngdd1_eval1: "\<Sigma>\<Sigma>1_rel (genCngdd1 R) x y \<Longrightarrow> genCngdd1 R (eval1 x) (eval1 y)"
using genCngdd1_eval1_rel_fun unfolding rel_fun_def by auto

lemma leq_genCngdd1: "R \<le> genCngdd1 R"
and imp_genCngdd1[intro]: "R j1 j2 \<Longrightarrow> genCngdd1 R j1 j2"
unfolding genCngdd1_def[abs_def] by auto

lemma genCngdd1_minimal: "\<lbrakk>R \<le> R'; cngdd1 R'\<rbrakk> \<Longrightarrow> genCngdd1 R \<le> R'"
unfolding genCngdd1_def[abs_def] by (metis (lifting, no_types) predicate2I)

theorem coinductionU_genCngdd1:
assumes "\<forall> a b. R a b \<longrightarrow> F_rel (genCngdd1 R) (dtor_J a) (dtor_J b)"
shows "R a b \<longrightarrow> a = b"
proof-
  let ?R' = "genCngdd1 R"
  have "R \<le> Retr ?R'" using assms unfolding Retr_def[abs_def] by auto
  hence "R \<le> ?R' \<sqinter> Retr ?R'" using leq_genCngdd1 by auto
  moreover have "cngdd1 (?R' \<sqinter> Retr ?R')" using cngdd1_Retr[OF cngdd1_genCngdd1[of R]] .
  ultimately have "?R' \<le> ?R' \<sqinter> Retr ?R'" using genCngdd1_minimal by metis
  hence "?R' \<le> Retr ?R'" by auto
  hence "?R' a b \<longrightarrow> a = b"  unfolding Retr_def[abs_def] by (intro J.dtor_coinduct) auto
  thus ?thesis using leq_genCngdd1 by auto
qed


subsection{* Flattening from term algebra to "one-step" algebra *}

(* Since (J \<Sigma>\<Sigma>1, eval1) is an Eilenberg-Moore algebra (i.e., is compatible with
the monadic structure, it yields an algebra on the signature functor.
This is crucial for having suitable simplification rules. *)

(* The one-step algebra (naturally associated to \<Lambda>1, not to dd1): *)
definition alg\<Lambda>1 :: "J \<Sigma>1 \<Rightarrow> J" where "alg\<Lambda>1 = eval1 o \<oo>\<pp>1 o \<Sigma>1_map leaf1"

theorem eval1_comp_\<oo>\<pp>1: "eval1 o \<oo>\<pp>1 = alg\<Lambda>1 o \<Sigma>1_map eval1"
unfolding alg\<Lambda>1_def
unfolding o_assoc[symmetric] \<Sigma>1.map_comp0[symmetric]
unfolding leaf1_natural[symmetric] unfolding \<Sigma>1.map_comp0
apply(rule sym) unfolding o_assoc apply(subst o_assoc[symmetric])
unfolding \<oo>\<pp>1_natural
unfolding o_assoc eval1_flat1[symmetric]
apply(subst o_assoc[symmetric]) unfolding flat1_commute[symmetric]
unfolding o_assoc[symmetric] \<Sigma>1.map_comp0[symmetric] flat1_leaf1 \<Sigma>1.map_id0 o_id ..

theorem eval1_\<oo>\<pp>1: "eval1 (\<oo>\<pp>1 t) = alg\<Lambda>1 (\<Sigma>1_map eval1 t)"
using eval1_comp_\<oo>\<pp>1 unfolding o_def fun_eq_iff by (rule allE)

theorem eval1_leaf1': "eval1 (leaf1 j) = j"
using eval1_leaf1 unfolding o_def fun_eq_iff id_def by (rule allE)

theorem dtor_J_alg\<Lambda>1: "dtor_J o alg\<Lambda>1 = F_map eval1 o \<Lambda>1 o \<Sigma>1_map <id, dtor_J>"
  unfolding alg\<Lambda>1_def eval1_def o_assoc dtor_unfold_J_pointfree \<Lambda>1_dd1
  unfolding o_assoc[symmetric] \<oo>\<pp>1_natural[symmetric] \<Sigma>1.map_comp0[symmetric] leaf1_natural
  ..

theorem dtor_J_alg\<Lambda>1': "dtor_J (alg\<Lambda>1 t) = F_map eval1 (\<Lambda>1 (\<Sigma>1_map (<id, dtor_J>) t))"
  by (rule trans[OF o_eq_dest[OF dtor_J_alg\<Lambda>1] o_apply])

theorem ctor_J_alg\<Lambda>1: "alg\<Lambda>1 t = ctor_J (F_map eval1 (\<Lambda>1 (\<Sigma>1_map (<id, dtor_J>) t)))"
  by (rule iffD1[OF J.dtor_inject trans[OF dtor_J_alg\<Lambda>1' J.dtor_ctor[symmetric]]])

(* Note: The user wi\<Lambda>1 indicate an "equation" equ :: J \<Sigma>1 \<Rightarrow> (J \<Sigma>\<Sigma>1) F
in order to define the operation alg\<Lambda>1 :: J \<Sigma>1 \<Rightarrow> J on the final coalgebra
according to dtor_J_alg\<Lambda>1.
The package wi\<Lambda>1 identify the polymorphic function \<Lambda>1 :: ('a \<times> 'a F) \<Sigma>1 \<Rightarrow> 'a \<Sigma>\<Sigma>1 F
such that equ = \<Lambda>1 o \<Sigma>1 <id, dtor_J>. Then the package wi\<Lambda>1 attempt to prove
automatica\<Lambda>1y that \<Lambda>1 is natural.  If the proof fails, the user wi\<Lambda>1 be asked to prove it.
Upon success, the distributive law is being registered.
*)

(* Customizing coinduction up-to: *)
definition "cpt\<Lambda>1 R \<equiv> (\<Sigma>1_rel R ===> R) alg\<Lambda>1 alg\<Lambda>1"

definition "cng\<Lambda>1 R \<equiv> equivp R \<and> cpt\<Lambda>1 R"

lemma cptdd1_iff_cpt\<Lambda>1: "cptdd1 R \<longleftrightarrow> cpt\<Lambda>1 R"
apply (rule iffI)
apply (unfold cpt\<Lambda>1_def cptdd1_def alg\<Lambda>1_def o_assoc[symmetric]) [1]
apply (erule rel_funD[OF rel_funD[OF comp_transfer]])
apply transfer_prover

apply (unfold cpt\<Lambda>1_def cptdd1_def) [1]
unfolding rel_fun_def
apply (rule allI)+
apply (rule \<Sigma>\<Sigma>1_rel_induct)
apply (simp only: eval1_leaf1')
unfolding eval1_\<oo>\<pp>1
apply (drule spec2)
apply (erule mp)
apply (rule iffD2[OF \<Sigma>1_rel_\<Sigma>1_map_\<Sigma>1_map])
apply (subst vimage2p_def)
apply assumption
done

(* This is the definition of genCngdd1 we need to work with: *)
theorem genCngdd1_def2: "genCngdd1 R j1 j2 \<longleftrightarrow> (\<forall> R'. R \<le> R' \<and> cng\<Lambda>1 R' \<longrightarrow> R' j1 j2)"
unfolding genCngdd1_def cngdd1_def cng\<Lambda>1_def cptdd1_iff_cpt\<Lambda>1 ..


subsection {* Incremental coinduction *}

interpretation I1: Incremental where Retr = Retr and Cl = genCngdd1
proof
  show "mono Retr" by (rule mono_retr)
next
  show "mono genCngdd1" unfolding mono_def
  unfolding genCngdd1_def[abs_def] by (smt order.trans predicate2I)
next
  fix r show "genCngdd1 (genCngdd1 r) = genCngdd1 r"
  by (metis cngdd1_genCngdd1 genCngdd1_minimal leq_genCngdd1 order_class.order.antisym)
next
  fix r show "r \<le> genCngdd1 r" by (metis leq_genCngdd1)
next
  fix r assume "genCngdd1 r = r" thus "genCngdd1 (r \<sqinter> Retr r) = r \<sqinter> Retr r"
  by (metis antisym cngdd1_Retr cngdd1_genCngdd1 genCngdd1_minimal
            inf.orderI inf_idem leq_genCngdd1)
qed

definition ded1 where "ded1 r s \<equiv> I1.ded r s"

theorems Ax = I1.Ax'[unfolded ded1_def[symmetric]]
theorems Split = I1.Split[unfolded ded1_def[symmetric]]
theorems Coind = I1.Coind[unfolded ded1_def[symmetric]]

theorem soundness_ded:
assumes "ded1 (op =) s"  shows "s \<le> (op =)"
unfolding gfp_Retr_eq[symmetric] apply(rule I1.soundness_ded[unfolded ded1_def[symmetric]] )
using assms unfolding gfp_Retr_eq[symmetric] ded1_def .

unused_thms

end
