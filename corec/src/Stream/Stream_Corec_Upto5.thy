header {* Corecursion and coinduction up to *}

theory Stream_Corec_Upto5
imports Stream_Lift_to_Free5
begin


subsection{* The algebra associated to dd5 *}

definition "eval5 \<equiv> dtor_unfold_J (dd5 o \<Sigma>\<Sigma>5_map <id, dtor_J>)"

lemma eval5: "F_map eval5 o dd5 o \<Sigma>\<Sigma>5_map <id, dtor_J> = dtor_J o eval5"
  unfolding eval5_def dtor_unfold_J_pointfree unfolding o_assoc ..

lemma eval5_ctor_J: "ctor_J o F_map eval5 o dd5 o \<Sigma>\<Sigma>5_map <id, dtor_J> = eval5"
  unfolding o_def spec[OF eval5[unfolded o_def fun_eq_iff]] J.ctor_dtor ..

lemma eval5_leaf5: "eval5 \<circ> leaf5 = id"
proof (rule trans)
  show "eval5 \<circ> leaf5 = dtor_unfold_J dtor_J"
  apply(rule J.dtor_unfold_unique)
  unfolding o_assoc eval5[symmetric] unfolding o_assoc[symmetric] leaf5_natural
  apply(rule sym)
  unfolding F_map_comp o_assoc apply (subst o_assoc[symmetric])
  unfolding dd5_leaf5 unfolding o_assoc[symmetric] by simp
qed(metis F_map_id J.dtor_unfold_unique fun.map_id o_id)

lemma eval5_flat5: "eval5 \<circ> flat5 = eval5 \<circ> \<Sigma>\<Sigma>5_map eval5"
proof (rule trans)
  let ?K5 = "dtor_unfold_J (dd5 o \<Sigma>\<Sigma>5_map <\<Sigma>\<Sigma>5_map fst, dd5> o \<Sigma>\<Sigma>5_map (\<Sigma>\<Sigma>5_map <id, dtor_J>))"
  show "eval5 \<circ> flat5 = ?K5"
  apply(rule J.dtor_unfold_unique)
  unfolding F_map_comp o_assoc
  apply(subst o_assoc[symmetric], subst o_assoc[symmetric])
  unfolding dd5_flat5
  unfolding o_assoc[symmetric] \<Sigma>\<Sigma>5.map_comp0[symmetric] snd_convol
  unfolding flat5_natural
  unfolding o_assoc eval5 ..
  (*  *)
  have A: "<eval5, dtor_J o eval5> = <id,dtor_J> o eval5" by simp
  show "?K5 = eval5 \<circ> \<Sigma>\<Sigma>5_map eval5"
  apply(rule J.dtor_unfold_unique[symmetric])
  unfolding o_assoc[symmetric] \<Sigma>\<Sigma>5.map_comp0[symmetric] map_prod_o_convol id_o
  unfolding F_map_comp o_assoc
  apply(subst o_assoc[symmetric]) unfolding dd5_natural[symmetric]
  unfolding o_assoc[symmetric] \<Sigma>\<Sigma>5.map_comp0[symmetric]
  unfolding o_assoc unfolding map_prod_o_convol unfolding convol_o
  unfolding o_assoc[symmetric] \<Sigma>\<Sigma>5.map_comp0[symmetric] fst_convol \<Sigma>\<Sigma>5.map_id0 o_id
  unfolding o_assoc eval5 unfolding A unfolding convol_o id_o
  apply(rule sym) apply(subst eval5[symmetric])
  unfolding o_assoc[symmetric] \<Sigma>\<Sigma>5.map_comp0[symmetric] convol_o id_o ..
qed


subsection{* The correspondence between coalgebras up to and coalgebras *}

(* This correspondence, and add5 the lemmas of this subsection, make
sense not only for (J,dtor_J,eval5), but also for any dd5-bialgebra *)

(* Coalgebra-up-to to coalgebra and vice versa: *)
definition cut\<Sigma>\<Sigma>5Oc :: "('a \<Rightarrow> 'a \<Sigma>\<Sigma>5 F) \<Rightarrow> ('a \<Sigma>\<Sigma>5 \<Rightarrow> 'a \<Sigma>\<Sigma>5 F)"
where "cut\<Sigma>\<Sigma>5Oc s \<equiv> F_map flat5 o dd5 o \<Sigma>\<Sigma>5_map <leaf5, s>"
definition c\<Sigma>\<Sigma>5Ocut :: "('a \<Sigma>\<Sigma>5 \<Rightarrow> 'a \<Sigma>\<Sigma>5 F) \<Rightarrow> ('a \<Rightarrow> 'a \<Sigma>\<Sigma>5 F)"
where "c\<Sigma>\<Sigma>5Ocut s' \<equiv> s' o leaf5"

lemma c\<Sigma>\<Sigma>5Ocut_cut\<Sigma>\<Sigma>5Oc: "c\<Sigma>\<Sigma>5Ocut (cut\<Sigma>\<Sigma>5Oc s) = s"
unfolding c\<Sigma>\<Sigma>5Ocut_def cut\<Sigma>\<Sigma>5Oc_def
unfolding o_assoc[symmetric] unfolding leaf5_natural
unfolding o_assoc apply(subst o_assoc[symmetric])
unfolding dd5_leaf5 unfolding o_assoc F_map_comp[symmetric] flat5_leaf5
unfolding F_map_id id_o by simp

lemma cut\<Sigma>\<Sigma>5Oc_inj: "cut\<Sigma>\<Sigma>5Oc s5 = cut\<Sigma>\<Sigma>5Oc s2 \<longleftrightarrow> s5 = s2"
by (metis c\<Sigma>\<Sigma>5Ocut_cut\<Sigma>\<Sigma>5Oc)

lemma c\<Sigma>\<Sigma>5Ocut_surj: "\<exists> s'. c\<Sigma>\<Sigma>5Ocut s' = s"
using c\<Sigma>\<Sigma>5Ocut_cut\<Sigma>\<Sigma>5Oc by(rule exI[of _ "cut\<Sigma>\<Sigma>5Oc s"])

(* Morphism-up-to to morphism and vice versa: *)
(* The dd5-extension of a function *)
definition extdd5 :: "('a \<Rightarrow> J) \<Rightarrow> ('a \<Sigma>\<Sigma>5 \<Rightarrow> J)"
where "extdd5 f \<equiv> eval5 o \<Sigma>\<Sigma>5_map f"
(* The restriction of a function *)  term eval5
definition restr :: "('a \<Sigma>\<Sigma>5 \<Rightarrow> J) \<Rightarrow> ('a \<Rightarrow> J)"
where "restr f' \<equiv> f' o leaf5"

(* We think of extdd5 and restr as operating
extdd5 : Hom_dd5(s,dtor_J) \<rightarrow> Hom(cut\<Sigma>\<Sigma>5Oc s,dtor_J) and
restr : Hom(cut\<Sigma>\<Sigma>5Oc s,dtor_J) \<rightarrow> Hom_dd5(s,dtor_J), where
Hom(cut\<Sigma>\<Sigma>5Oc s,dtor_J) is the set of coalgebra morphisms betwee cut\<Sigma>\<Sigma>5Oc s and dtor_J and
Hom_dd5(s,dtor_J) is the set of coalgebra up-to-dd5-morphisms between s and dtor_J  *)

(* extdd5 is wedd5-defined: *)
lemma extdd5_mor:
assumes f:  "F_map (extdd5 f) o s = dtor_J o f"
shows "F_map (extdd5 f) o cut\<Sigma>\<Sigma>5Oc s = dtor_J o (extdd5 f)"
proof-
  have AA: "eval5 ** F_map eval5 \<circ> (\<Sigma>\<Sigma>5_map f ** F_map (\<Sigma>\<Sigma>5_map f) \<circ> <leaf5 , s>) =
            <f , F_map eval5 \<circ> (F_map (\<Sigma>\<Sigma>5_map f) \<circ> s)>"
  unfolding map_prod_o_convol unfolding leaf5_natural o_assoc eval5_leaf5 id_o  ..
  show ?thesis
  unfolding extdd5_def
  unfolding o_assoc eval5[symmetric]
  unfolding o_assoc[symmetric] \<Sigma>\<Sigma>5.map_comp0[symmetric]
  unfolding convol_comp[symmetric] id_o
  unfolding f[symmetric, unfolded extdd5_def]
  unfolding o_assoc
  apply(subst o_assoc[symmetric])
  unfolding F_map_comp o_assoc
  unfolding cut\<Sigma>\<Sigma>5Oc_def
  unfolding o_assoc
  unfolding F_map_comp[symmetric] unfolding o_assoc[symmetric]
  unfolding flat5_natural[symmetric]
  unfolding o_assoc F_map_comp
  apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
  unfolding dd5_natural[symmetric]
  unfolding o_assoc unfolding F_map_comp[symmetric] eval5_flat5
  unfolding F_map_comp apply(subst o_assoc[symmetric])
  unfolding dd5_natural[symmetric] unfolding o_assoc[symmetric] \<Sigma>\<Sigma>5.map_comp0[symmetric]
  unfolding o_assoc[symmetric] AA[unfolded o_assoc[symmetric]] ..
qed

lemma mor_cut\<Sigma>\<Sigma>5Oc_flat5:
assumes f': "F_map f' o cut\<Sigma>\<Sigma>5Oc s = dtor_J o f'"
shows "eval5 o \<Sigma>\<Sigma>5_map f' = f' o flat5"
proof(rule trans) (* this proof is clearly improvable: *)
  def h \<equiv> "dd5 o \<Sigma>\<Sigma>5_map <id,cut\<Sigma>\<Sigma>5Oc s>"
  have f'_id: "f' = f' o id" by simp
  show "eval5 \<circ> \<Sigma>\<Sigma>5_map f' = dtor_unfold_J h"
  apply(rule J.dtor_unfold_unique, rule sym)
  unfolding o_assoc eval5[symmetric]
  unfolding o_assoc[symmetric] \<Sigma>\<Sigma>5.map_comp0[symmetric]
  unfolding convol_comp_id1[symmetric] unfolding f'[symmetric]
  apply(subst f'_id)
  unfolding o_assoc \<Sigma>\<Sigma>5.map_comp0
  apply(subst o_assoc[symmetric])
  unfolding o_assoc[symmetric] F_map_comp
  unfolding h_def apply(rule sym)
  unfolding o_assoc apply(subst o_assoc[symmetric])
  unfolding dd5_natural[symmetric] unfolding o_assoc[symmetric]
  unfolding \<Sigma>\<Sigma>5.map_comp0[symmetric] map_prod_o_convol ..
  (*  *)
  have AA: "<id , cut\<Sigma>\<Sigma>5Oc s> = (flat5 ** F_map flat5) o (id ** dd5) o <leaf5, \<Sigma>\<Sigma>5_map <leaf5 , s>>"
  unfolding map_prod_o_convol o_assoc map_prod.comp cut\<Sigma>\<Sigma>5Oc_def o_id flat5_leaf5 ..
  have BB: "flat5 ** F_map flat5 \<circ> id ** dd5 \<circ> <leaf5 , \<Sigma>\<Sigma>5_map <leaf5 , s>> = flat5 ** F_map flat5 \<circ> id ** dd5 \<circ> <\<Sigma>\<Sigma>5_map leaf5 , \<Sigma>\<Sigma>5_map <leaf5 , s>>"
  unfolding map_prod.comp unfolding map_prod_o_convol unfolding o_id unfolding flat5_leaf5 leaf5_flat5 ..
  show "dtor_unfold_J h = f' \<circ> flat5"
  apply(rule J.dtor_unfold_unique[symmetric], rule sym)
  unfolding o_assoc f'[symmetric]
  unfolding F_map_comp o_assoc[symmetric]
  apply(rule arg_cong[of _ _ "op o (F_map f')"])
  unfolding h_def
  unfolding AA BB
  unfolding \<Sigma>\<Sigma>5.map_comp0 apply(rule sym)
  unfolding o_assoc apply(subst o_assoc[symmetric])
  unfolding dd5_natural
  unfolding o_assoc F_map_comp[symmetric]
  unfolding flat5_assoc unfolding F_map_comp
  unfolding cut\<Sigma>\<Sigma>5Oc_def o_assoc[symmetric] apply(rule arg_cong[of _ _ "op o (F_map flat5)"])
  unfolding o_assoc
  unfolding o_assoc[symmetric] unfolding \<Sigma>\<Sigma>5.map_comp0[symmetric] unfolding map_prod_o_convol id_o
  unfolding flat5_natural[symmetric] unfolding o_assoc
  unfolding dd5_flat5[symmetric] unfolding o_assoc[symmetric] unfolding \<Sigma>\<Sigma>5.map_comp0[symmetric]
  unfolding convol_o unfolding \<Sigma>\<Sigma>5.map_comp0[symmetric] unfolding fst_convol ..
qed

(* restr is wedd5-defined:  *)
lemma restr_mor:
assumes f': "F_map f' o cut\<Sigma>\<Sigma>5Oc s = dtor_J o f'"
shows "F_map (extdd5 (restr f')) o s = dtor_J o restr f'"
unfolding extdd5_def restr_def \<Sigma>\<Sigma>5.map_comp0
unfolding o_assoc mor_cut\<Sigma>\<Sigma>5Oc_flat5[OF f']
unfolding o_assoc[symmetric] leaf5_flat5 o_id
unfolding o_assoc f'[symmetric]
unfolding o_assoc[symmetric] c\<Sigma>\<Sigma>5Ocut_cut\<Sigma>\<Sigma>5Oc[unfolded c\<Sigma>\<Sigma>5Ocut_def] ..

lemma extdd5_restr:
assumes f': "F_map f' o cut\<Sigma>\<Sigma>5Oc s = dtor_J o f'"
shows "extdd5 (restr f') = f'"
proof-
  have "f' = eval5 o \<Sigma>\<Sigma>5_map f' o leaf5"
  unfolding o_assoc[symmetric] leaf5_natural
  unfolding o_assoc eval5_leaf5 by simp
  also have "... = eval5 o \<Sigma>\<Sigma>5_map (f' o leaf5)"
  unfolding \<Sigma>\<Sigma>5.map_comp0 o_assoc
  unfolding mor_cut\<Sigma>\<Sigma>5Oc_flat5[OF f'] unfolding o_assoc[symmetric] flat5_leaf5 leaf5_flat5 ..
  finally have A: "f' = eval5 o \<Sigma>\<Sigma>5_map (f' o leaf5)" .
  show ?thesis unfolding extdd5_def restr_def A[symmetric] ..
qed

lemma restr_inj:
assumes f5': "F_map f5' o cut\<Sigma>\<Sigma>5Oc s = dtor_J o f5'"
and f2': "F_map f2' o cut\<Sigma>\<Sigma>5Oc s = dtor_J o f2'"
shows "restr f5' = restr f2' \<longleftrightarrow> f5' = f2'"
using extdd5_restr[OF f5'] extdd5_restr[OF f2'] by metis

lemma extdd5_surj:
assumes f': "F_map f' o cut\<Sigma>\<Sigma>5Oc s = dtor_J o f'"
shows "\<exists> f. extdd5 f = f'"
using extdd5_restr[OF f'] by(rule exI[of _ "restr f'"])

lemma restr_extdd5:
assumes f: "F_map (extdd5 f) o s = dtor_J o f"
shows "restr (extdd5 f) = f"
proof-
  have "dtor_J o f = F_map (extdd5 f) o s" using assms unfolding extdd5_def by (rule sym)
  also have "... = dtor_J o restr (extdd5 f)"
  unfolding restr_def unfolding o_assoc extdd5_mor[OF f, symmetric]
  unfolding o_assoc[symmetric] c\<Sigma>\<Sigma>5Ocut_cut\<Sigma>\<Sigma>5Oc[unfolded c\<Sigma>\<Sigma>5Ocut_def] ..
  finally have "dtor_J o f = dtor_J \<circ> restr (extdd5 f)" .
  thus ?thesis unfolding dtor_J_o_inj by (rule sym)
qed

lemma extdd5_inj:
assumes f1: "F_map (extdd5 f1) o s = dtor_J o f1"
and f2: "F_map (extdd5 f2) o s = dtor_J o f2"
shows "extdd5 f1 = extdd5 f2 \<longleftrightarrow> f1 = f2"
using restr_extdd5[OF f1] restr_extdd5[OF f2] by metis

lemma restr_surj:
assumes f: "F_map (extdd5 f) o s = dtor_J o f"
shows "\<exists> f'. restr f' = f"
using restr_extdd5[OF f] by(rule exI[of _ "extdd5 f"])


subsection{* Coiteration up-to *}

definition "unfoldU5 s \<equiv> restr (dtor_unfold_J (cut\<Sigma>\<Sigma>5Oc s))"

theorem unfoldU5_pointfree:
"F_map (extdd5 (unfoldU5 s)) o s = dtor_J o unfoldU5 s"
unfolding unfoldU5_def apply(rule restr_mor)
unfolding dtor_unfold_J_pointfree ..

theorem unfoldU5: "F_map (extdd5 (unfoldU5 s)) (s a) = dtor_J (unfoldU5 s a)"
using unfoldU5_pointfree unfolding o_def fun_eq_iff by(rule allE)

theorem unfoldU5_ctor_J:
"ctor_J (F_map (extdd5 (unfoldU5 s)) (s a)) = unfoldU5 s a"
using unfoldU5 by (metis J.ctor_dtor)

theorem unfoldU5_unique:
assumes "F_map (extdd5 f) o s = dtor_J o f"
shows "f = unfoldU5 s"
proof-
  note f = extdd5_mor[OF assms]  note co = extdd5_mor[OF unfoldU5_pointfree]
  have A: "extdd5 f = extdd5 (unfoldU5 s)"
  proof(rule trans)
    show "extdd5 f = dtor_unfold_J (cut\<Sigma>\<Sigma>5Oc s)" apply(rule J.dtor_unfold_unique) using f .
    show "dtor_unfold_J (cut\<Sigma>\<Sigma>5Oc s) = extdd5 (unfoldU5 s)"
     apply(rule J.dtor_unfold_unique[symmetric]) using co .
  qed
  show ?thesis using A unfolding extdd5_inj[OF assms unfoldU5_pointfree] .
qed

lemma unfoldU5_ctor_J_pointfree:
"ctor_J o F_map (extdd5 (unfoldU5 s)) o s = unfoldU5 s"
unfolding o_def fun_eq_iff by (subst unfoldU5_ctor_J[symmetric]) (rule allI, rule refl)

(* Corecursion up to: *)
definition corecU5 :: "('a \<Rightarrow> (J + 'a) \<Sigma>\<Sigma>5 F) \<Rightarrow> 'a \<Rightarrow> J" where
"corecU5 s = unfoldU5 (case_sum (dd5 o leaf5 o <Inl, F_map Inl o dtor_J>) s) o Inr"

definition extddRec5 where
"extddRec5 f \<equiv> eval5 \<circ> \<Sigma>\<Sigma>5_map (case_sum id f)"

lemma unfoldU5_Inl:
"unfoldU5 (case_sum (dd5 \<circ> leaf5 \<circ> <Inl , F_map Inl \<circ> dtor_J>) s) o Inl = id"
(is "?L = ?R")
proof-
  have "?L = unfoldU5 (dd5 o leaf5 o <id, dtor_J>)"
  apply(rule unfoldU5_unique)
  unfolding o_assoc unfoldU5_pointfree[symmetric]
  unfolding o_assoc[symmetric] case_sum_o_inj extdd5_def F_map_comp \<Sigma>\<Sigma>5.map_comp0
  unfolding o_assoc apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric],
                          subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
  unfolding dd5_natural[symmetric]
  apply(subst o_assoc[symmetric]) unfolding leaf5_natural
  unfolding o_assoc[symmetric] map_prod_o_convol o_id ..
  also have "... = ?R"
  apply(rule sym, rule unfoldU5_unique)
  unfolding extdd5_def \<Sigma>\<Sigma>5.map_id0 o_id dd5_leaf5
  unfolding o_assoc[symmetric] snd_convol
  unfolding o_assoc F_map_comp[symmetric] eval5_leaf5 F_map_id id_o ..
  finally show ?thesis .
qed

theorem corecU5_pointfree:
"F_map (extddRec5 (corecU5 s)) o s = dtor_J o corecU5 s" (is "?L = ?R")
unfolding corecU5_def
unfolding o_assoc unfoldU5_pointfree[symmetric] extddRec5_def
unfolding o_assoc[symmetric] case_sum_o_inj
apply(subst unfoldU5_Inl[symmetric, of s])
unfolding o_assoc case_sum_Inl_Inr_L extdd5_def ..

theorem corecU5:
"F_map (extddRec5 (corecU5 s)) (s a) = dtor_J (corecU5 s a)"
using corecU5_pointfree unfolding o_def fun_eq_iff by(rule allE)


subsection{* Coinduction up-to *}

definition "cptdd5 R \<equiv> (\<Sigma>\<Sigma>5_rel R ===> R) eval5 eval5"

definition "cngdd5 R \<equiv> equivp R \<and> cptdd5 R"

lemma cngdd5_Retr: "cngdd5 R \<Longrightarrow> cngdd5 (R \<sqinter> Retr R)"
  unfolding cngdd5_def cptdd5_def
  apply (erule conjE)
  apply (rule conjI[OF equivp_inf[OF _ equivp_retr]])
  apply assumption
  apply assumption
  apply (rule rel_funI)
  apply (frule predicate2D[OF \<Sigma>\<Sigma>5_rel_inf])
  apply (erule inf2E)
  apply (rule inf2I)
  apply (erule rel_funE)
  apply assumption
  apply assumption
  apply (subst Retr_def)
  apply (subst eval5_def)+
  apply (subst J.dtor_unfold)+
  unfolding F_rel_F_map_F_map Grp_def relcompp.simps[abs_def] conversep.simps[abs_def]
  apply auto
  unfolding eval5_def[symmetric]
  apply (rule predicate2D[OF F_rel_mono])
  apply (rule predicate2I)
  apply (erule rel_funD)
  apply assumption
  apply (rule F_rel_\<Sigma>\<Sigma>5_rel)
  unfolding \<Sigma>\<Sigma>5_rel_\<Sigma>\<Sigma>5_map_\<Sigma>\<Sigma>5_map vimage2p_rel_prod vimage2p_id
  unfolding vimage2p_def Retr_def[symmetric]
  apply assumption
  done

(* The generated congruence: *)
definition "genCngdd5 R j1 j2 \<equiv> \<forall> R'. R \<le> R' \<and> cngdd5 R' \<longrightarrow> R' j1 j2"

lemma cngdd5_genCngdd5: "cngdd5 (genCngdd5 R)"
unfolding cngdd5_def proof safe
  show "cptdd5 (genCngdd5 R)"
  unfolding cptdd5_def rel_fun_def proof safe
    fix x y assume A: "\<Sigma>\<Sigma>5_rel (genCngdd5 R) x y"
    show "genCngdd5 R (eval5 x) (eval5 y)"
    unfolding genCngdd5_def[abs_def] proof safe
      fix R' assume "R \<le> R'" and 2: "cngdd5 R'"
      hence "\<Sigma>\<Sigma>5_rel R' x y" by (metis A \<Sigma>\<Sigma>5.rel_mono_strong genCngdd5_def)
      thus "R' (eval5 x) (eval5 y)" using 2 unfolding cngdd5_def cptdd5_def rel_fun_def by auto
    qed
  qed
qed(rule equivpI, unfold reflp_def symp_def transp_def genCngdd5_def cngdd5_def equivp_def, auto)

lemma
    genCngdd5_refl[intro,simp]: "genCngdd5 R j j"
and genCngdd5_sym[intro]: "genCngdd5 R j1 j2 \<Longrightarrow> genCngdd5 R j2 j1"
and genCngdd5_trans[intro]: "\<lbrakk>genCngdd5 R j1 j2; genCngdd5 R j2 j3\<rbrakk> \<Longrightarrow> genCngdd5 R j1 j3"
using cngdd5_genCngdd5 unfolding cngdd5_def equivp_def by auto

lemma genCngdd5_eval5_rel_fun: "(\<Sigma>\<Sigma>5_rel (genCngdd5 R) ===> genCngdd5 R) eval5 eval5"
using cngdd5_genCngdd5 unfolding cngdd5_def cptdd5_def by auto

lemma genCngdd5_eval5: "\<Sigma>\<Sigma>5_rel (genCngdd5 R) x y \<Longrightarrow> genCngdd5 R (eval5 x) (eval5 y)"
using genCngdd5_eval5_rel_fun unfolding rel_fun_def by auto

lemma leq_genCngdd5: "R \<le> genCngdd5 R"
and imp_genCngdd5[intro]: "R j1 j2 \<Longrightarrow> genCngdd5 R j1 j2"
unfolding genCngdd5_def[abs_def] by auto

lemma genCngdd5_minimal: "\<lbrakk>R \<le> R'; cngdd5 R'\<rbrakk> \<Longrightarrow> genCngdd5 R \<le> R'"
unfolding genCngdd5_def[abs_def] by (metis (lifting, no_types) predicate2I)

theorem coinductionU_genCngdd5:
assumes "\<forall> a b. R a b \<longrightarrow> F_rel (genCngdd5 R) (dtor_J a) (dtor_J b)"
shows "R a b \<longrightarrow> a = b"
proof-
  let ?R' = "genCngdd5 R"
  have "R \<le> Retr ?R'" using assms unfolding Retr_def[abs_def] by auto
  hence "R \<le> ?R' \<sqinter> Retr ?R'" using leq_genCngdd5 by auto
  moreover have "cngdd5 (?R' \<sqinter> Retr ?R')" using cngdd5_Retr[OF cngdd5_genCngdd5[of R]] .
  ultimately have "?R' \<le> ?R' \<sqinter> Retr ?R'" using genCngdd5_minimal by metis
  hence "?R' \<le> Retr ?R'" by auto
  hence "?R' a b \<longrightarrow> a = b"  unfolding Retr_def[abs_def] by (intro J.dtor_coinduct) auto
  thus ?thesis using leq_genCngdd5 by auto
qed


subsection{* Flattening from term algebra to "one-step" algebra *}

(* Since (J \<Sigma>\<Sigma>5, eval5) is an Eilenberg-Moore algebra (i.e., is compatible with
the monadic structure, it yields an algebra on the signature functor.
This is crucial for having suitable simplification rules. *)

(* The one-step algebra (naturally associated to \<Lambda>5, not to dd5): *)
definition alg\<Lambda>5 :: "J \<Sigma>5 \<Rightarrow> J" where "alg\<Lambda>5 = eval5 o \<oo>\<pp>5 o \<Sigma>5_map leaf5"

theorem eval5_comp_\<oo>\<pp>5: "eval5 o \<oo>\<pp>5 = alg\<Lambda>5 o \<Sigma>5_map eval5"
unfolding alg\<Lambda>5_def
unfolding o_assoc[symmetric] \<Sigma>5.map_comp0[symmetric]
unfolding leaf5_natural[symmetric] unfolding \<Sigma>5.map_comp0
apply(rule sym) unfolding o_assoc apply(subst o_assoc[symmetric])
unfolding \<oo>\<pp>5_natural
unfolding o_assoc eval5_flat5[symmetric]
apply(subst o_assoc[symmetric]) unfolding flat5_commute[symmetric]
unfolding o_assoc[symmetric] \<Sigma>5.map_comp0[symmetric] flat5_leaf5 \<Sigma>5.map_id0 o_id ..

theorem eval5_\<oo>\<pp>5: "eval5 (\<oo>\<pp>5 t) = alg\<Lambda>5 (\<Sigma>5_map eval5 t)"
using eval5_comp_\<oo>\<pp>5 unfolding o_def fun_eq_iff by (rule allE)

theorem eval5_leaf5': "eval5 (leaf5 j) = j"
using eval5_leaf5 unfolding o_def fun_eq_iff id_def by (rule allE)

theorem dtor_J_alg\<Lambda>5: "dtor_J o alg\<Lambda>5 = F_map eval5 o \<Lambda>5 o \<Sigma>5_map <id, dtor_J>"
  unfolding alg\<Lambda>5_def eval5_def o_assoc dtor_unfold_J_pointfree \<Lambda>5_dd5
  unfolding o_assoc[symmetric] \<oo>\<pp>5_natural[symmetric] \<Sigma>5.map_comp0[symmetric] leaf5_natural
  ..

theorem dtor_J_alg\<Lambda>5': "dtor_J (alg\<Lambda>5 t) = F_map eval5 (\<Lambda>5 (\<Sigma>5_map (<id, dtor_J>) t))"
  by (rule trans[OF o_eq_dest[OF dtor_J_alg\<Lambda>5] o_apply])

theorem ctor_J_alg\<Lambda>5: "alg\<Lambda>5 t = ctor_J (F_map eval5 (\<Lambda>5 (\<Sigma>5_map (<id, dtor_J>) t)))"
  by (rule iffD1[OF J.dtor_inject trans[OF dtor_J_alg\<Lambda>5' J.dtor_ctor[symmetric]]])

(* Note: The user wi\<Lambda>5 indicate an "equation" equ :: J \<Sigma>5 \<Rightarrow> (J \<Sigma>\<Sigma>5) F
in order to define the operation alg\<Lambda>5 :: J \<Sigma>5 \<Rightarrow> J on the final coalgebra
according to dtor_J_alg\<Lambda>5.
The package wi\<Lambda>5 identify the polymorphic function \<Lambda>5 :: ('a \<times> 'a F) \<Sigma>5 \<Rightarrow> 'a \<Sigma>\<Sigma>5 F
such that equ = \<Lambda>5 o \<Sigma>5 <id, dtor_J>. Then the package wi\<Lambda>5 attempt to prove
automatica\<Lambda>5y that \<Lambda>5 is natural.  If the proof fails, the user wi\<Lambda>5 be asked to prove it.
Upon success, the distributive law is being registered.
*)

(* Customizing coinduction up-to: *)
definition "cpt\<Lambda>5 R \<equiv> (\<Sigma>5_rel R ===> R) alg\<Lambda>5 alg\<Lambda>5"

definition "cng\<Lambda>5 R \<equiv> equivp R \<and> cpt\<Lambda>5 R"

lemma cptdd5_iff_cpt\<Lambda>5: "cptdd5 R \<longleftrightarrow> cpt\<Lambda>5 R"
apply (rule iffI)
apply (unfold cpt\<Lambda>5_def cptdd5_def alg\<Lambda>5_def o_assoc[symmetric]) [1]
apply (erule rel_funD[OF rel_funD[OF comp_transfer]])
apply transfer_prover

apply (unfold cpt\<Lambda>5_def cptdd5_def) [1]
unfolding rel_fun_def
apply (rule allI)+
apply (rule \<Sigma>\<Sigma>5_rel_induct)
apply (simp only: eval5_leaf5')
unfolding eval5_\<oo>\<pp>5
apply (drule spec2)
apply (erule mp)
apply (rule iffD2[OF \<Sigma>5_rel_\<Sigma>5_map_\<Sigma>5_map])
apply (subst vimage2p_def)
apply assumption
done

(* This is the definition of genCngdd5 we need to work with: *)
theorem genCngdd5_def2: "genCngdd5 R j1 j2 \<longleftrightarrow> (\<forall> R'. R \<le> R' \<and> cng\<Lambda>5 R' \<longrightarrow> R' j1 j2)"
unfolding genCngdd5_def cngdd5_def cng\<Lambda>5_def cptdd5_iff_cpt\<Lambda>5 ..


subsection {* Incremental coinduction *}

interpretation I5: Incremental where Retr = Retr and Cl = genCngdd5
proof
  show "mono Retr" by (rule mono_retr)
next
  show "mono genCngdd5" unfolding mono_def
  unfolding genCngdd5_def[abs_def] by (smt order.trans predicate2I)
next
  fix r show "genCngdd5 (genCngdd5 r) = genCngdd5 r"
  by (metis cngdd5_genCngdd5 genCngdd5_minimal leq_genCngdd5 order_class.order.antisym)
next
  fix r show "r \<le> genCngdd5 r" by (metis leq_genCngdd5)
next
  fix r assume "genCngdd5 r = r" thus "genCngdd5 (r \<sqinter> Retr r) = r \<sqinter> Retr r"
  by (metis antisym cngdd5_Retr cngdd5_genCngdd5 genCngdd5_minimal
            inf.orderI inf_idem leq_genCngdd5)
qed

definition ded5 where "ded5 r s \<equiv> I5.ded r s"

theorems Ax = I5.Ax'[unfolded ded5_def[symmetric]]
theorems Split = I5.Split[unfolded ded5_def[symmetric]]
theorems Coind = I5.Coind[unfolded ded5_def[symmetric]]

theorem soundness_ded:
assumes "ded5 (op =) s"  shows "s \<le> (op =)"
unfolding gfp_Retr_eq[symmetric] apply(rule I5.soundness_ded[unfolded ded5_def[symmetric]] )
using assms unfolding gfp_Retr_eq[symmetric] ded5_def .

unused_thms

end
