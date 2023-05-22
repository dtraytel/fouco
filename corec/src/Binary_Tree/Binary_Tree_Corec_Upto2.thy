header {* Corecursion and coinduction up to *}

theory Binary_Tree_Corec_Upto2
imports Binary_Tree_Lift_to_Free2
begin


subsection{* The algebra associated to dd2 *}

definition "eval2 \<equiv> dtor_unfold_J (dd2 o \<Sigma>\<Sigma>2_map <id, dtor_J>)"

lemma eval2: "F_map eval2 o dd2 o \<Sigma>\<Sigma>2_map <id, dtor_J> = dtor_J o eval2"
  unfolding eval2_def dtor_unfold_J_pointfree unfolding o_assoc ..

lemma eval2_ctor_J: "ctor_J o F_map eval2 o dd2 o \<Sigma>\<Sigma>2_map <id, dtor_J> = eval2"
  unfolding o_def spec[OF eval2[unfolded o_def fun_eq_iff]] J.ctor_dtor ..

lemma eval2_leaf2: "eval2 \<circ> leaf2 = id"
proof (rule trans)
  show "eval2 \<circ> leaf2 = dtor_unfold_J dtor_J"
  apply(rule J.dtor_unfold_unique)
  unfolding o_assoc eval2[symmetric] unfolding o_assoc[symmetric] leaf2_natural
  apply(rule sym)
  unfolding F_map_comp o_assoc apply (subst o_assoc[symmetric])
  unfolding dd2_leaf2 unfolding o_assoc[symmetric] by simp
qed(metis F_map_id J.dtor_unfold_unique fun.map_id o_id)

lemma eval2_flat2: "eval2 \<circ> flat2 = eval2 \<circ> \<Sigma>\<Sigma>2_map eval2"
proof (rule trans)
  let ?K2 = "dtor_unfold_J (dd2 o \<Sigma>\<Sigma>2_map <\<Sigma>\<Sigma>2_map fst, dd2> o \<Sigma>\<Sigma>2_map (\<Sigma>\<Sigma>2_map <id, dtor_J>))"
  show "eval2 \<circ> flat2 = ?K2"
  apply(rule J.dtor_unfold_unique)
  unfolding F_map_comp o_assoc
  apply(subst o_assoc[symmetric], subst o_assoc[symmetric])
  unfolding dd2_flat2
  unfolding o_assoc[symmetric] \<Sigma>\<Sigma>2.map_comp0[symmetric] snd_convol
  unfolding flat2_natural
  unfolding o_assoc eval2 ..
  (*  *)
  have A: "<eval2, dtor_J o eval2> = <id,dtor_J> o eval2" by simp
  show "?K2 = eval2 \<circ> \<Sigma>\<Sigma>2_map eval2"
  apply(rule J.dtor_unfold_unique[symmetric])
  unfolding o_assoc[symmetric] \<Sigma>\<Sigma>2.map_comp0[symmetric] map_prod_o_convol id_o
  unfolding F_map_comp o_assoc
  apply(subst o_assoc[symmetric]) unfolding dd2_natural[symmetric]
  unfolding o_assoc[symmetric] \<Sigma>\<Sigma>2.map_comp0[symmetric]
  unfolding o_assoc unfolding map_prod_o_convol unfolding convol_o
  unfolding o_assoc[symmetric] \<Sigma>\<Sigma>2.map_comp0[symmetric] fst_convol \<Sigma>\<Sigma>2.map_id0 o_id
  unfolding o_assoc eval2 unfolding A unfolding convol_o id_o
  apply(rule sym) apply(subst eval2[symmetric])
  unfolding o_assoc[symmetric] \<Sigma>\<Sigma>2.map_comp0[symmetric] convol_o id_o ..
qed


subsection{* The correspondence between coalgebras up to and coalgebras *}

(* This correspondence, and add2 the lemmas of this subsection, make
sense not only for (J,dtor_J,eval2), but also for any dd2-bialgebra *)

(* Coalgebra-up-to to coalgebra and vice versa: *)
definition cut\<Sigma>\<Sigma>2Oc :: "('a \<Rightarrow> 'a \<Sigma>\<Sigma>2 F) \<Rightarrow> ('a \<Sigma>\<Sigma>2 \<Rightarrow> 'a \<Sigma>\<Sigma>2 F)"
where "cut\<Sigma>\<Sigma>2Oc s \<equiv> F_map flat2 o dd2 o \<Sigma>\<Sigma>2_map <leaf2, s>"
definition c\<Sigma>\<Sigma>2Ocut :: "('a \<Sigma>\<Sigma>2 \<Rightarrow> 'a \<Sigma>\<Sigma>2 F) \<Rightarrow> ('a \<Rightarrow> 'a \<Sigma>\<Sigma>2 F)"
where "c\<Sigma>\<Sigma>2Ocut s' \<equiv> s' o leaf2"

lemma c\<Sigma>\<Sigma>2Ocut_cut\<Sigma>\<Sigma>2Oc: "c\<Sigma>\<Sigma>2Ocut (cut\<Sigma>\<Sigma>2Oc s) = s"
unfolding c\<Sigma>\<Sigma>2Ocut_def cut\<Sigma>\<Sigma>2Oc_def
unfolding o_assoc[symmetric] unfolding leaf2_natural
unfolding o_assoc apply(subst o_assoc[symmetric])
unfolding dd2_leaf2 unfolding o_assoc F_map_comp[symmetric] flat2_leaf2
unfolding F_map_id id_o by simp

lemma cut\<Sigma>\<Sigma>2Oc_inj: "cut\<Sigma>\<Sigma>2Oc s2 = cut\<Sigma>\<Sigma>2Oc s2 \<longleftrightarrow> s2 = s2"
by (metis c\<Sigma>\<Sigma>2Ocut_cut\<Sigma>\<Sigma>2Oc)

lemma c\<Sigma>\<Sigma>2Ocut_surj: "\<exists> s'. c\<Sigma>\<Sigma>2Ocut s' = s"
using c\<Sigma>\<Sigma>2Ocut_cut\<Sigma>\<Sigma>2Oc by(rule exI[of _ "cut\<Sigma>\<Sigma>2Oc s"])

(* Morphism-up-to to morphism and vice versa: *)
(* The dd2-extension of a function *)
definition extdd2 :: "('a \<Rightarrow> J) \<Rightarrow> ('a \<Sigma>\<Sigma>2 \<Rightarrow> J)"
where "extdd2 f \<equiv> eval2 o \<Sigma>\<Sigma>2_map f"
(* The restriction of a function *)  term eval2
definition restr :: "('a \<Sigma>\<Sigma>2 \<Rightarrow> J) \<Rightarrow> ('a \<Rightarrow> J)"
where "restr f' \<equiv> f' o leaf2"

(* We think of extdd2 and restr as operating
extdd2 : Hom_dd2(s,dtor_J) \<rightarrow> Hom(cut\<Sigma>\<Sigma>2Oc s,dtor_J) and
restr : Hom(cut\<Sigma>\<Sigma>2Oc s,dtor_J) \<rightarrow> Hom_dd2(s,dtor_J), where
Hom(cut\<Sigma>\<Sigma>2Oc s,dtor_J) is the set of coalgebra morphisms betwee cut\<Sigma>\<Sigma>2Oc s and dtor_J and
Hom_dd2(s,dtor_J) is the set of coalgebra up-to-dd2-morphisms between s and dtor_J  *)

(* extdd2 is wedd2-defined: *)
lemma extdd2_mor:
assumes f:  "F_map (extdd2 f) o s = dtor_J o f"
shows "F_map (extdd2 f) o cut\<Sigma>\<Sigma>2Oc s = dtor_J o (extdd2 f)"
proof-
  have AA: "eval2 ** F_map eval2 \<circ> (\<Sigma>\<Sigma>2_map f ** F_map (\<Sigma>\<Sigma>2_map f) \<circ> <leaf2 , s>) =
            <f , F_map eval2 \<circ> (F_map (\<Sigma>\<Sigma>2_map f) \<circ> s)>"
  unfolding map_prod_o_convol unfolding leaf2_natural o_assoc eval2_leaf2 id_o  ..
  show ?thesis
  unfolding extdd2_def
  unfolding o_assoc eval2[symmetric]
  unfolding o_assoc[symmetric] \<Sigma>\<Sigma>2.map_comp0[symmetric]
  unfolding convol_comp[symmetric] id_o
  unfolding f[symmetric, unfolded extdd2_def]
  unfolding o_assoc
  apply(subst o_assoc[symmetric])
  unfolding F_map_comp o_assoc
  unfolding cut\<Sigma>\<Sigma>2Oc_def
  unfolding o_assoc
  unfolding F_map_comp[symmetric] unfolding o_assoc[symmetric]
  unfolding flat2_natural[symmetric]
  unfolding o_assoc F_map_comp
  apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
  unfolding dd2_natural[symmetric]
  unfolding o_assoc unfolding F_map_comp[symmetric] eval2_flat2
  unfolding F_map_comp apply(subst o_assoc[symmetric])
  unfolding dd2_natural[symmetric] unfolding o_assoc[symmetric] \<Sigma>\<Sigma>2.map_comp0[symmetric]
  unfolding o_assoc[symmetric] AA[unfolded o_assoc[symmetric]] ..
qed

lemma mor_cut\<Sigma>\<Sigma>2Oc_flat2:
assumes f': "F_map f' o cut\<Sigma>\<Sigma>2Oc s = dtor_J o f'"
shows "eval2 o \<Sigma>\<Sigma>2_map f' = f' o flat2"
proof(rule trans) (* this proof is clearly improvable: *)
  def h \<equiv> "dd2 o \<Sigma>\<Sigma>2_map <id,cut\<Sigma>\<Sigma>2Oc s>"
  have f'_id: "f' = f' o id" by simp
  show "eval2 \<circ> \<Sigma>\<Sigma>2_map f' = dtor_unfold_J h"
  apply(rule J.dtor_unfold_unique, rule sym)
  unfolding o_assoc eval2[symmetric]
  unfolding o_assoc[symmetric] \<Sigma>\<Sigma>2.map_comp0[symmetric]
  unfolding convol_comp_id1[symmetric] unfolding f'[symmetric]
  apply(subst f'_id)
  unfolding o_assoc \<Sigma>\<Sigma>2.map_comp0
  apply(subst o_assoc[symmetric])
  unfolding o_assoc[symmetric] F_map_comp
  unfolding h_def apply(rule sym)
  unfolding o_assoc apply(subst o_assoc[symmetric])
  unfolding dd2_natural[symmetric] unfolding o_assoc[symmetric]
  unfolding \<Sigma>\<Sigma>2.map_comp0[symmetric] map_prod_o_convol ..
  (*  *)
  have AA: "<id , cut\<Sigma>\<Sigma>2Oc s> = (flat2 ** F_map flat2) o (id ** dd2) o <leaf2, \<Sigma>\<Sigma>2_map <leaf2 , s>>"
  unfolding map_prod_o_convol o_assoc map_prod.comp cut\<Sigma>\<Sigma>2Oc_def o_id flat2_leaf2 ..
  have BB: "flat2 ** F_map flat2 \<circ> id ** dd2 \<circ> <leaf2 , \<Sigma>\<Sigma>2_map <leaf2 , s>> = flat2 ** F_map flat2 \<circ> id ** dd2 \<circ> <\<Sigma>\<Sigma>2_map leaf2 , \<Sigma>\<Sigma>2_map <leaf2 , s>>"
  unfolding map_prod.comp unfolding map_prod_o_convol unfolding o_id unfolding flat2_leaf2 leaf2_flat2 ..
  show "dtor_unfold_J h = f' \<circ> flat2"
  apply(rule J.dtor_unfold_unique[symmetric], rule sym)
  unfolding o_assoc f'[symmetric]
  unfolding F_map_comp o_assoc[symmetric]
  apply(rule arg_cong[of _ _ "op o (F_map f')"])
  unfolding h_def
  unfolding AA BB
  unfolding \<Sigma>\<Sigma>2.map_comp0 apply(rule sym)
  unfolding o_assoc apply(subst o_assoc[symmetric])
  unfolding dd2_natural
  unfolding o_assoc F_map_comp[symmetric]
  unfolding flat2_assoc unfolding F_map_comp
  unfolding cut\<Sigma>\<Sigma>2Oc_def o_assoc[symmetric] apply(rule arg_cong[of _ _ "op o (F_map flat2)"])
  unfolding o_assoc
  unfolding o_assoc[symmetric] unfolding \<Sigma>\<Sigma>2.map_comp0[symmetric] unfolding map_prod_o_convol id_o
  unfolding flat2_natural[symmetric] unfolding o_assoc
  unfolding dd2_flat2[symmetric] unfolding o_assoc[symmetric] unfolding \<Sigma>\<Sigma>2.map_comp0[symmetric]
  unfolding convol_o unfolding \<Sigma>\<Sigma>2.map_comp0[symmetric] unfolding fst_convol ..
qed

(* restr is wedd2-defined:  *)
lemma restr_mor:
assumes f': "F_map f' o cut\<Sigma>\<Sigma>2Oc s = dtor_J o f'"
shows "F_map (extdd2 (restr f')) o s = dtor_J o restr f'"
unfolding extdd2_def restr_def \<Sigma>\<Sigma>2.map_comp0
unfolding o_assoc mor_cut\<Sigma>\<Sigma>2Oc_flat2[OF f']
unfolding o_assoc[symmetric] leaf2_flat2 o_id
unfolding o_assoc f'[symmetric]
unfolding o_assoc[symmetric] c\<Sigma>\<Sigma>2Ocut_cut\<Sigma>\<Sigma>2Oc[unfolded c\<Sigma>\<Sigma>2Ocut_def] ..

lemma extdd2_restr:
assumes f': "F_map f' o cut\<Sigma>\<Sigma>2Oc s = dtor_J o f'"
shows "extdd2 (restr f') = f'"
proof-
  have "f' = eval2 o \<Sigma>\<Sigma>2_map f' o leaf2"
  unfolding o_assoc[symmetric] leaf2_natural
  unfolding o_assoc eval2_leaf2 by simp
  also have "... = eval2 o \<Sigma>\<Sigma>2_map (f' o leaf2)"
  unfolding \<Sigma>\<Sigma>2.map_comp0 o_assoc
  unfolding mor_cut\<Sigma>\<Sigma>2Oc_flat2[OF f'] unfolding o_assoc[symmetric] flat2_leaf2 leaf2_flat2 ..
  finally have A: "f' = eval2 o \<Sigma>\<Sigma>2_map (f' o leaf2)" .
  show ?thesis unfolding extdd2_def restr_def A[symmetric] ..
qed

lemma restr_inj:
assumes f2': "F_map f2' o cut\<Sigma>\<Sigma>2Oc s = dtor_J o f2'"
and f2': "F_map f2' o cut\<Sigma>\<Sigma>2Oc s = dtor_J o f2'"
shows "restr f2' = restr f2' \<longleftrightarrow> f2' = f2'"
using extdd2_restr[OF f2'] extdd2_restr[OF f2'] by metis

lemma extdd2_surj:
assumes f': "F_map f' o cut\<Sigma>\<Sigma>2Oc s = dtor_J o f'"
shows "\<exists> f. extdd2 f = f'"
using extdd2_restr[OF f'] by(rule exI[of _ "restr f'"])

lemma restr_extdd2:
assumes f: "F_map (extdd2 f) o s = dtor_J o f"
shows "restr (extdd2 f) = f"
proof-
  have "dtor_J o f = F_map (extdd2 f) o s" using assms unfolding extdd2_def by (rule sym)
  also have "... = dtor_J o restr (extdd2 f)"
  unfolding restr_def unfolding o_assoc extdd2_mor[OF f, symmetric]
  unfolding o_assoc[symmetric] c\<Sigma>\<Sigma>2Ocut_cut\<Sigma>\<Sigma>2Oc[unfolded c\<Sigma>\<Sigma>2Ocut_def] ..
  finally have "dtor_J o f = dtor_J \<circ> restr (extdd2 f)" .
  thus ?thesis unfolding dtor_J_o_inj by (rule sym)
qed

lemma extdd2_inj:
assumes f1: "F_map (extdd2 f1) o s = dtor_J o f1"
and f2: "F_map (extdd2 f2) o s = dtor_J o f2"
shows "extdd2 f1 = extdd2 f2 \<longleftrightarrow> f1 = f2"
using restr_extdd2[OF f1] restr_extdd2[OF f2] by metis

lemma restr_surj:
assumes f: "F_map (extdd2 f) o s = dtor_J o f"
shows "\<exists> f'. restr f' = f"
using restr_extdd2[OF f] by(rule exI[of _ "extdd2 f"])


subsection{* Coiteration up-to *}

definition "unfoldU2 s \<equiv> restr (dtor_unfold_J (cut\<Sigma>\<Sigma>2Oc s))"

theorem unfoldU2_pointfree:
"F_map (extdd2 (unfoldU2 s)) o s = dtor_J o unfoldU2 s"
unfolding unfoldU2_def apply(rule restr_mor)
unfolding dtor_unfold_J_pointfree ..

theorem unfoldU2: "F_map (extdd2 (unfoldU2 s)) (s a) = dtor_J (unfoldU2 s a)"
using unfoldU2_pointfree unfolding o_def fun_eq_iff by(rule allE)

theorem unfoldU2_ctor_J:
"ctor_J (F_map (extdd2 (unfoldU2 s)) (s a)) = unfoldU2 s a"
using unfoldU2 by (metis J.ctor_dtor)

theorem unfoldU2_unique:
assumes "F_map (extdd2 f) o s = dtor_J o f"
shows "f = unfoldU2 s"
proof-
  note f = extdd2_mor[OF assms]  note co = extdd2_mor[OF unfoldU2_pointfree]
  have A: "extdd2 f = extdd2 (unfoldU2 s)"
  proof(rule trans)
    show "extdd2 f = dtor_unfold_J (cut\<Sigma>\<Sigma>2Oc s)" apply(rule J.dtor_unfold_unique) using f .
    show "dtor_unfold_J (cut\<Sigma>\<Sigma>2Oc s) = extdd2 (unfoldU2 s)"
     apply(rule J.dtor_unfold_unique[symmetric]) using co .
  qed
  show ?thesis using A unfolding extdd2_inj[OF assms unfoldU2_pointfree] .
qed

lemma unfoldU2_ctor_J_pointfree:
"ctor_J o F_map (extdd2 (unfoldU2 s)) o s = unfoldU2 s"
unfolding o_def fun_eq_iff by (subst unfoldU2_ctor_J[symmetric]) (rule allI, rule refl)

(* Corecursion up to: *)
definition corecU2 :: "('a \<Rightarrow> (J + 'a) \<Sigma>\<Sigma>2 F) \<Rightarrow> 'a \<Rightarrow> J" where
"corecU2 s = unfoldU2 (case_sum (dd2 o leaf2 o <Inl, F_map Inl o dtor_J>) s) o Inr"

definition extddRec2 where
"extddRec2 f \<equiv> eval2 \<circ> \<Sigma>\<Sigma>2_map (case_sum id f)"

lemma unfoldU2_Inl:
"unfoldU2 (case_sum (dd2 \<circ> leaf2 \<circ> <Inl , F_map Inl \<circ> dtor_J>) s) o Inl = id"
(is "?L = ?R")
proof-
  have "?L = unfoldU2 (dd2 o leaf2 o <id, dtor_J>)"
  apply(rule unfoldU2_unique)
  unfolding o_assoc unfoldU2_pointfree[symmetric]
  unfolding o_assoc[symmetric] case_sum_o_inj extdd2_def F_map_comp \<Sigma>\<Sigma>2.map_comp0
  unfolding o_assoc apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric],
                          subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
  unfolding dd2_natural[symmetric]
  apply(subst o_assoc[symmetric]) unfolding leaf2_natural
  unfolding o_assoc[symmetric] map_prod_o_convol o_id ..
  also have "... = ?R"
  apply(rule sym, rule unfoldU2_unique)
  unfolding extdd2_def \<Sigma>\<Sigma>2.map_id0 o_id dd2_leaf2
  unfolding o_assoc[symmetric] snd_convol
  unfolding o_assoc F_map_comp[symmetric] eval2_leaf2 F_map_id id_o ..
  finally show ?thesis .
qed

theorem corecU2_pointfree:
"F_map (extddRec2 (corecU2 s)) o s = dtor_J o corecU2 s" (is "?L = ?R")
unfolding corecU2_def
unfolding o_assoc unfoldU2_pointfree[symmetric] extddRec2_def
unfolding o_assoc[symmetric] case_sum_o_inj
apply(subst unfoldU2_Inl[symmetric, of s])
unfolding o_assoc case_sum_Inl_Inr_L extdd2_def ..

theorem corecU2:
"F_map (extddRec2 (corecU2 s)) (s a) = dtor_J (corecU2 s a)"
using corecU2_pointfree unfolding o_def fun_eq_iff by(rule allE)


subsection{* Coinduction up-to *}

definition "cptdd2 R \<equiv> (\<Sigma>\<Sigma>2_rel R ===> R) eval2 eval2"

definition "cngdd2 R \<equiv> equivp R \<and> cptdd2 R"

lemma cngdd2_Retr: "cngdd2 R \<Longrightarrow> cngdd2 (R \<sqinter> Retr R)"
  unfolding cngdd2_def cptdd2_def
  apply (erule conjE)
  apply (rule conjI[OF equivp_inf[OF _ equivp_retr]])
  apply assumption
  apply assumption
  apply (rule rel_funI)
  apply (frule predicate2D[OF \<Sigma>\<Sigma>2_rel_inf])
  apply (erule inf2E)
  apply (rule inf2I)
  apply (erule rel_funE)
  apply assumption
  apply assumption
  apply (subst Retr_def)
  apply (subst eval2_def)+
  apply (subst J.dtor_unfold)+
  unfolding F_rel_F_map_F_map Grp_def relcompp.simps[abs_def] conversep.simps[abs_def]
  apply auto
  unfolding eval2_def[symmetric]
  apply (rule predicate2D[OF F_rel_mono])
  apply (rule predicate2I)
  apply (erule rel_funD)
  apply assumption
  apply (rule F_rel_\<Sigma>\<Sigma>2_rel)
  unfolding \<Sigma>\<Sigma>2_rel_\<Sigma>\<Sigma>2_map_\<Sigma>\<Sigma>2_map vimage2p_rel_prod vimage2p_id
  unfolding vimage2p_def Retr_def[symmetric]
  apply assumption
  done

(* The generated congruence: *)
definition "genCngdd2 R j1 j2 \<equiv> \<forall> R'. R \<le> R' \<and> cngdd2 R' \<longrightarrow> R' j1 j2"

lemma cngdd2_genCngdd2: "cngdd2 (genCngdd2 R)"
unfolding cngdd2_def proof safe
  show "cptdd2 (genCngdd2 R)"
  unfolding cptdd2_def rel_fun_def proof safe
    fix x y assume A: "\<Sigma>\<Sigma>2_rel (genCngdd2 R) x y"
    show "genCngdd2 R (eval2 x) (eval2 y)"
    unfolding genCngdd2_def[abs_def] proof safe
      fix R' assume "R \<le> R'" and 2: "cngdd2 R'"
      hence "\<Sigma>\<Sigma>2_rel R' x y" by (metis A \<Sigma>\<Sigma>2.rel_mono_strong genCngdd2_def)
      thus "R' (eval2 x) (eval2 y)" using 2 unfolding cngdd2_def cptdd2_def rel_fun_def by auto
    qed
  qed
qed(rule equivpI, unfold reflp_def symp_def transp_def genCngdd2_def cngdd2_def equivp_def, auto)

lemma
    genCngdd2_refl[intro,simp]: "genCngdd2 R j j"
and genCngdd2_sym[intro]: "genCngdd2 R j1 j2 \<Longrightarrow> genCngdd2 R j2 j1"
and genCngdd2_trans[intro]: "\<lbrakk>genCngdd2 R j1 j2; genCngdd2 R j2 j3\<rbrakk> \<Longrightarrow> genCngdd2 R j1 j3"
using cngdd2_genCngdd2 unfolding cngdd2_def equivp_def by auto

lemma genCngdd2_eval2_rel_fun: "(\<Sigma>\<Sigma>2_rel (genCngdd2 R) ===> genCngdd2 R) eval2 eval2"
using cngdd2_genCngdd2 unfolding cngdd2_def cptdd2_def by auto

lemma genCngdd2_eval2: "\<Sigma>\<Sigma>2_rel (genCngdd2 R) x y \<Longrightarrow> genCngdd2 R (eval2 x) (eval2 y)"
using genCngdd2_eval2_rel_fun unfolding rel_fun_def by auto

lemma leq_genCngdd2: "R \<le> genCngdd2 R"
and imp_genCngdd2[intro]: "R j1 j2 \<Longrightarrow> genCngdd2 R j1 j2"
unfolding genCngdd2_def[abs_def] by auto

lemma genCngdd2_minimal: "\<lbrakk>R \<le> R'; cngdd2 R'\<rbrakk> \<Longrightarrow> genCngdd2 R \<le> R'"
unfolding genCngdd2_def[abs_def] by (metis (lifting, no_types) predicate2I)

theorem coinductionU_genCngdd2:
assumes "\<forall> a b. R a b \<longrightarrow> F_rel (genCngdd2 R) (dtor_J a) (dtor_J b)"
shows "R a b \<longrightarrow> a = b"
proof-
  let ?R' = "genCngdd2 R"
  have "R \<le> Retr ?R'" using assms unfolding Retr_def[abs_def] by auto
  hence "R \<le> ?R' \<sqinter> Retr ?R'" using leq_genCngdd2 by auto
  moreover have "cngdd2 (?R' \<sqinter> Retr ?R')" using cngdd2_Retr[OF cngdd2_genCngdd2[of R]] .
  ultimately have "?R' \<le> ?R' \<sqinter> Retr ?R'" using genCngdd2_minimal by metis
  hence "?R' \<le> Retr ?R'" by auto
  hence "?R' a b \<longrightarrow> a = b"  unfolding Retr_def[abs_def] by (intro J.dtor_coinduct) auto
  thus ?thesis using leq_genCngdd2 by auto
qed


subsection{* Flattening from term algebra to "one-step" algebra *}

(* Since (J \<Sigma>\<Sigma>2, eval2) is an Eilenberg-Moore algebra (i.e., is compatible with
the monadic structure, it yields an algebra on the signature functor.
This is crucial for having suitable simplification rules. *)

(* The one-step algebra (naturally associated to \<Lambda>2, not to dd2): *)
definition alg\<Lambda>2 :: "J \<Sigma>2 \<Rightarrow> J" where "alg\<Lambda>2 = eval2 o \<oo>\<pp>2 o \<Sigma>2_map leaf2"

theorem eval2_comp_\<oo>\<pp>2: "eval2 o \<oo>\<pp>2 = alg\<Lambda>2 o \<Sigma>2_map eval2"
unfolding alg\<Lambda>2_def
unfolding o_assoc[symmetric] \<Sigma>2.map_comp0[symmetric]
unfolding leaf2_natural[symmetric] unfolding \<Sigma>2.map_comp0
apply(rule sym) unfolding o_assoc apply(subst o_assoc[symmetric])
unfolding \<oo>\<pp>2_natural
unfolding o_assoc eval2_flat2[symmetric]
apply(subst o_assoc[symmetric]) unfolding flat2_commute[symmetric]
unfolding o_assoc[symmetric] \<Sigma>2.map_comp0[symmetric] flat2_leaf2 \<Sigma>2.map_id0 o_id ..

theorem eval2_\<oo>\<pp>2: "eval2 (\<oo>\<pp>2 t) = alg\<Lambda>2 (\<Sigma>2_map eval2 t)"
using eval2_comp_\<oo>\<pp>2 unfolding o_def fun_eq_iff by (rule allE)

theorem eval2_leaf2': "eval2 (leaf2 j) = j"
using eval2_leaf2 unfolding o_def fun_eq_iff id_def by (rule allE)

theorem dtor_J_alg\<Lambda>2: "dtor_J o alg\<Lambda>2 = F_map eval2 o \<Lambda>2 o \<Sigma>2_map <id, dtor_J>"
  unfolding alg\<Lambda>2_def eval2_def o_assoc dtor_unfold_J_pointfree \<Lambda>2_dd2
  unfolding o_assoc[symmetric] \<oo>\<pp>2_natural[symmetric] \<Sigma>2.map_comp0[symmetric] leaf2_natural
  ..

theorem dtor_J_alg\<Lambda>2': "dtor_J (alg\<Lambda>2 t) = F_map eval2 (\<Lambda>2 (\<Sigma>2_map (<id, dtor_J>) t))"
  by (rule trans[OF o_eq_dest[OF dtor_J_alg\<Lambda>2] o_apply])

theorem ctor_J_alg\<Lambda>2: "alg\<Lambda>2 t = ctor_J (F_map eval2 (\<Lambda>2 (\<Sigma>2_map (<id, dtor_J>) t)))"
  by (rule iffD1[OF J.dtor_inject trans[OF dtor_J_alg\<Lambda>2' J.dtor_ctor[symmetric]]])

(* Note: The user wi\<Lambda>2 indicate an "equation" equ :: J \<Sigma>2 \<Rightarrow> (J \<Sigma>\<Sigma>2) F
in order to define the operation alg\<Lambda>2 :: J \<Sigma>2 \<Rightarrow> J on the final coalgebra
according to dtor_J_alg\<Lambda>2.
The package wi\<Lambda>2 identify the polymorphic function \<Lambda>2 :: ('a \<times> 'a F) \<Sigma>2 \<Rightarrow> 'a \<Sigma>\<Sigma>2 F
such that equ = \<Lambda>2 o \<Sigma>2 <id, dtor_J>. Then the package wi\<Lambda>2 attempt to prove
automatica\<Lambda>2y that \<Lambda>2 is natural.  If the proof fails, the user wi\<Lambda>2 be asked to prove it.
Upon success, the distributive law is being registered.
*)

(* Customizing coinduction up-to: *)
definition "cpt\<Lambda>2 R \<equiv> (\<Sigma>2_rel R ===> R) alg\<Lambda>2 alg\<Lambda>2"

definition "cng\<Lambda>2 R \<equiv> equivp R \<and> cpt\<Lambda>2 R"

lemma cptdd2_iff_cpt\<Lambda>2: "cptdd2 R \<longleftrightarrow> cpt\<Lambda>2 R"
apply (rule iffI)
apply (unfold cpt\<Lambda>2_def cptdd2_def alg\<Lambda>2_def o_assoc[symmetric]) [1]
apply (erule rel_funD[OF rel_funD[OF comp_transfer]])
apply transfer_prover

apply (unfold cpt\<Lambda>2_def cptdd2_def) [1]
unfolding rel_fun_def
apply (rule allI)+
apply (rule \<Sigma>\<Sigma>2_rel_induct)
apply (simp only: eval2_leaf2')
unfolding eval2_\<oo>\<pp>2
apply (drule spec2)
apply (erule mp)
apply (rule iffD2[OF \<Sigma>2_rel_\<Sigma>2_map_\<Sigma>2_map])
apply (subst vimage2p_def)
apply assumption
done

(* This is the definition of genCngdd2 we need to work with: *)
theorem genCngdd2_def2: "genCngdd2 R j1 j2 \<longleftrightarrow> (\<forall> R'. R \<le> R' \<and> cng\<Lambda>2 R' \<longrightarrow> R' j1 j2)"
unfolding genCngdd2_def cngdd2_def cng\<Lambda>2_def cptdd2_iff_cpt\<Lambda>2 ..


subsection {* Incremental coinduction *}

interpretation I2: Incremental where Retr = Retr and Cl = genCngdd2
proof
  show "mono Retr" by (rule mono_retr)
next
  show "mono genCngdd2" unfolding mono_def
  unfolding genCngdd2_def[abs_def] by (smt order.trans predicate2I)
next
  fix r show "genCngdd2 (genCngdd2 r) = genCngdd2 r"
  by (metis cngdd2_genCngdd2 genCngdd2_minimal leq_genCngdd2 order_class.order.antisym)
next
  fix r show "r \<le> genCngdd2 r" by (metis leq_genCngdd2)
next
  fix r assume "genCngdd2 r = r" thus "genCngdd2 (r \<sqinter> Retr r) = r \<sqinter> Retr r"
  by (metis antisym cngdd2_Retr cngdd2_genCngdd2 genCngdd2_minimal
            inf.orderI inf_idem leq_genCngdd2)
qed

definition ded2 where "ded2 r s \<equiv> I2.ded r s"

theorems Ax = I2.Ax'[unfolded ded2_def[symmetric]]
theorems Split = I2.Split[unfolded ded2_def[symmetric]]
theorems Coind = I2.Coind[unfolded ded2_def[symmetric]]

theorem soundness_ded:
assumes "ded2 (op =) s"  shows "s \<le> (op =)"
unfolding gfp_Retr_eq[symmetric] apply(rule I2.soundness_ded[unfolded ded2_def[symmetric]] )
using assms unfolding gfp_Retr_eq[symmetric] ded2_def .

unused_thms

end
