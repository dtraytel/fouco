header {* Corecursion and coinduction up to *}

theory Stream_Corec_Upto9
imports Stream_Lift_to_Free9
begin


subsection{* The algebra associated to dd9 *}

definition "eval9 \<equiv> dtor_unfold_J (dd9 o \<Sigma>\<Sigma>9_map <id, dtor_J>)"

lemma eval9: "F_map eval9 o dd9 o \<Sigma>\<Sigma>9_map <id, dtor_J> = dtor_J o eval9"
  unfolding eval9_def dtor_unfold_J_pointfree unfolding o_assoc ..

lemma eval9_ctor_J: "ctor_J o F_map eval9 o dd9 o \<Sigma>\<Sigma>9_map <id, dtor_J> = eval9"
  unfolding o_def spec[OF eval9[unfolded o_def fun_eq_iff]] J.ctor_dtor ..

lemma eval9_leaf9: "eval9 \<circ> leaf9 = id"
proof (rule trans)
  show "eval9 \<circ> leaf9 = dtor_unfold_J dtor_J"
  apply(rule J.dtor_unfold_unique)
  unfolding o_assoc eval9[symmetric] unfolding o_assoc[symmetric] leaf9_natural
  apply(rule sym)
  unfolding F_map_comp o_assoc apply (subst o_assoc[symmetric])
  unfolding dd9_leaf9 unfolding o_assoc[symmetric] by simp
qed(metis F_map_id J.dtor_unfold_unique fun.map_id o_id)

lemma eval9_flat9: "eval9 \<circ> flat9 = eval9 \<circ> \<Sigma>\<Sigma>9_map eval9"
proof (rule trans)
  let ?K9 = "dtor_unfold_J (dd9 o \<Sigma>\<Sigma>9_map <\<Sigma>\<Sigma>9_map fst, dd9> o \<Sigma>\<Sigma>9_map (\<Sigma>\<Sigma>9_map <id, dtor_J>))"
  show "eval9 \<circ> flat9 = ?K9"
  apply(rule J.dtor_unfold_unique)
  unfolding F_map_comp o_assoc
  apply(subst o_assoc[symmetric], subst o_assoc[symmetric])
  unfolding dd9_flat9
  unfolding o_assoc[symmetric] \<Sigma>\<Sigma>9.map_comp0[symmetric] snd_convol
  unfolding flat9_natural
  unfolding o_assoc eval9 ..
  (*  *)
  have A: "<eval9, dtor_J o eval9> = <id,dtor_J> o eval9" by simp
  show "?K9 = eval9 \<circ> \<Sigma>\<Sigma>9_map eval9"
  apply(rule J.dtor_unfold_unique[symmetric])
  unfolding o_assoc[symmetric] \<Sigma>\<Sigma>9.map_comp0[symmetric] map_prod_o_convol id_o
  unfolding F_map_comp o_assoc
  apply(subst o_assoc[symmetric]) unfolding dd9_natural[symmetric]
  unfolding o_assoc[symmetric] \<Sigma>\<Sigma>9.map_comp0[symmetric]
  unfolding o_assoc unfolding map_prod_o_convol unfolding convol_o
  unfolding o_assoc[symmetric] \<Sigma>\<Sigma>9.map_comp0[symmetric] fst_convol \<Sigma>\<Sigma>9.map_id0 o_id
  unfolding o_assoc eval9 unfolding A unfolding convol_o id_o
  apply(rule sym) apply(subst eval9[symmetric])
  unfolding o_assoc[symmetric] \<Sigma>\<Sigma>9.map_comp0[symmetric] convol_o id_o ..
qed


subsection{* The correspondence between coalgebras up to and coalgebras *}

(* This correspondence, and add9 the lemmas of this subsection, make
sense not only for (J,dtor_J,eval9), but also for any dd9-bialgebra *)

(* Coalgebra-up-to to coalgebra and vice versa: *)
definition cut\<Sigma>\<Sigma>9Oc :: "('a \<Rightarrow> 'a \<Sigma>\<Sigma>9 F) \<Rightarrow> ('a \<Sigma>\<Sigma>9 \<Rightarrow> 'a \<Sigma>\<Sigma>9 F)"
where "cut\<Sigma>\<Sigma>9Oc s \<equiv> F_map flat9 o dd9 o \<Sigma>\<Sigma>9_map <leaf9, s>"
definition c\<Sigma>\<Sigma>9Ocut :: "('a \<Sigma>\<Sigma>9 \<Rightarrow> 'a \<Sigma>\<Sigma>9 F) \<Rightarrow> ('a \<Rightarrow> 'a \<Sigma>\<Sigma>9 F)"
where "c\<Sigma>\<Sigma>9Ocut s' \<equiv> s' o leaf9"

lemma c\<Sigma>\<Sigma>9Ocut_cut\<Sigma>\<Sigma>9Oc: "c\<Sigma>\<Sigma>9Ocut (cut\<Sigma>\<Sigma>9Oc s) = s"
unfolding c\<Sigma>\<Sigma>9Ocut_def cut\<Sigma>\<Sigma>9Oc_def
unfolding o_assoc[symmetric] unfolding leaf9_natural
unfolding o_assoc apply(subst o_assoc[symmetric])
unfolding dd9_leaf9 unfolding o_assoc F_map_comp[symmetric] flat9_leaf9
unfolding F_map_id id_o by simp

lemma cut\<Sigma>\<Sigma>9Oc_inj: "cut\<Sigma>\<Sigma>9Oc s9 = cut\<Sigma>\<Sigma>9Oc s2 \<longleftrightarrow> s9 = s2"
by (metis c\<Sigma>\<Sigma>9Ocut_cut\<Sigma>\<Sigma>9Oc)

lemma c\<Sigma>\<Sigma>9Ocut_surj: "\<exists> s'. c\<Sigma>\<Sigma>9Ocut s' = s"
using c\<Sigma>\<Sigma>9Ocut_cut\<Sigma>\<Sigma>9Oc by(rule exI[of _ "cut\<Sigma>\<Sigma>9Oc s"])

(* Morphism-up-to to morphism and vice versa: *)
(* The dd9-extension of a function *)
definition extdd9 :: "('a \<Rightarrow> J) \<Rightarrow> ('a \<Sigma>\<Sigma>9 \<Rightarrow> J)"
where "extdd9 f \<equiv> eval9 o \<Sigma>\<Sigma>9_map f"
(* The restriction of a function *)  term eval9
definition restr :: "('a \<Sigma>\<Sigma>9 \<Rightarrow> J) \<Rightarrow> ('a \<Rightarrow> J)"
where "restr f' \<equiv> f' o leaf9"

(* We think of extdd9 and restr as operating
extdd9 : Hom_dd9(s,dtor_J) \<rightarrow> Hom(cut\<Sigma>\<Sigma>9Oc s,dtor_J) and
restr : Hom(cut\<Sigma>\<Sigma>9Oc s,dtor_J) \<rightarrow> Hom_dd9(s,dtor_J), where
Hom(cut\<Sigma>\<Sigma>9Oc s,dtor_J) is the set of coalgebra morphisms betwee cut\<Sigma>\<Sigma>9Oc s and dtor_J and
Hom_dd9(s,dtor_J) is the set of coalgebra up-to-dd9-morphisms between s and dtor_J  *)

(* extdd9 is wedd9-defined: *)
lemma extdd9_mor:
assumes f:  "F_map (extdd9 f) o s = dtor_J o f"
shows "F_map (extdd9 f) o cut\<Sigma>\<Sigma>9Oc s = dtor_J o (extdd9 f)"
proof-
  have AA: "eval9 ** F_map eval9 \<circ> (\<Sigma>\<Sigma>9_map f ** F_map (\<Sigma>\<Sigma>9_map f) \<circ> <leaf9 , s>) =
            <f , F_map eval9 \<circ> (F_map (\<Sigma>\<Sigma>9_map f) \<circ> s)>"
  unfolding map_prod_o_convol unfolding leaf9_natural o_assoc eval9_leaf9 id_o  ..
  show ?thesis
  unfolding extdd9_def
  unfolding o_assoc eval9[symmetric]
  unfolding o_assoc[symmetric] \<Sigma>\<Sigma>9.map_comp0[symmetric]
  unfolding convol_comp[symmetric] id_o
  unfolding f[symmetric, unfolded extdd9_def]
  unfolding o_assoc
  apply(subst o_assoc[symmetric])
  unfolding F_map_comp o_assoc
  unfolding cut\<Sigma>\<Sigma>9Oc_def
  unfolding o_assoc
  unfolding F_map_comp[symmetric] unfolding o_assoc[symmetric]
  unfolding flat9_natural[symmetric]
  unfolding o_assoc F_map_comp
  apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
  unfolding dd9_natural[symmetric]
  unfolding o_assoc unfolding F_map_comp[symmetric] eval9_flat9
  unfolding F_map_comp apply(subst o_assoc[symmetric])
  unfolding dd9_natural[symmetric] unfolding o_assoc[symmetric] \<Sigma>\<Sigma>9.map_comp0[symmetric]
  unfolding o_assoc[symmetric] AA[unfolded o_assoc[symmetric]] ..
qed

lemma mor_cut\<Sigma>\<Sigma>9Oc_flat9:
assumes f': "F_map f' o cut\<Sigma>\<Sigma>9Oc s = dtor_J o f'"
shows "eval9 o \<Sigma>\<Sigma>9_map f' = f' o flat9"
proof(rule trans) (* this proof is clearly improvable: *)
  def h \<equiv> "dd9 o \<Sigma>\<Sigma>9_map <id,cut\<Sigma>\<Sigma>9Oc s>"
  have f'_id: "f' = f' o id" by simp
  show "eval9 \<circ> \<Sigma>\<Sigma>9_map f' = dtor_unfold_J h"
  apply(rule J.dtor_unfold_unique, rule sym)
  unfolding o_assoc eval9[symmetric]
  unfolding o_assoc[symmetric] \<Sigma>\<Sigma>9.map_comp0[symmetric]
  unfolding convol_comp_id1[symmetric] unfolding f'[symmetric]
  apply(subst f'_id)
  unfolding o_assoc \<Sigma>\<Sigma>9.map_comp0
  apply(subst o_assoc[symmetric])
  unfolding o_assoc[symmetric] F_map_comp
  unfolding h_def apply(rule sym)
  unfolding o_assoc apply(subst o_assoc[symmetric])
  unfolding dd9_natural[symmetric] unfolding o_assoc[symmetric]
  unfolding \<Sigma>\<Sigma>9.map_comp0[symmetric] map_prod_o_convol ..
  (*  *)
  have AA: "<id , cut\<Sigma>\<Sigma>9Oc s> = (flat9 ** F_map flat9) o (id ** dd9) o <leaf9, \<Sigma>\<Sigma>9_map <leaf9 , s>>"
  unfolding map_prod_o_convol o_assoc map_prod.comp cut\<Sigma>\<Sigma>9Oc_def o_id flat9_leaf9 ..
  have BB: "flat9 ** F_map flat9 \<circ> id ** dd9 \<circ> <leaf9 , \<Sigma>\<Sigma>9_map <leaf9 , s>> = flat9 ** F_map flat9 \<circ> id ** dd9 \<circ> <\<Sigma>\<Sigma>9_map leaf9 , \<Sigma>\<Sigma>9_map <leaf9 , s>>"
  unfolding map_prod.comp unfolding map_prod_o_convol unfolding o_id unfolding flat9_leaf9 leaf9_flat9 ..
  show "dtor_unfold_J h = f' \<circ> flat9"
  apply(rule J.dtor_unfold_unique[symmetric], rule sym)
  unfolding o_assoc f'[symmetric]
  unfolding F_map_comp o_assoc[symmetric]
  apply(rule arg_cong[of _ _ "op o (F_map f')"])
  unfolding h_def
  unfolding AA BB
  unfolding \<Sigma>\<Sigma>9.map_comp0 apply(rule sym)
  unfolding o_assoc apply(subst o_assoc[symmetric])
  unfolding dd9_natural
  unfolding o_assoc F_map_comp[symmetric]
  unfolding flat9_assoc unfolding F_map_comp
  unfolding cut\<Sigma>\<Sigma>9Oc_def o_assoc[symmetric] apply(rule arg_cong[of _ _ "op o (F_map flat9)"])
  unfolding o_assoc
  unfolding o_assoc[symmetric] unfolding \<Sigma>\<Sigma>9.map_comp0[symmetric] unfolding map_prod_o_convol id_o
  unfolding flat9_natural[symmetric] unfolding o_assoc
  unfolding dd9_flat9[symmetric] unfolding o_assoc[symmetric] unfolding \<Sigma>\<Sigma>9.map_comp0[symmetric]
  unfolding convol_o unfolding \<Sigma>\<Sigma>9.map_comp0[symmetric] unfolding fst_convol ..
qed

(* restr is wedd9-defined:  *)
lemma restr_mor:
assumes f': "F_map f' o cut\<Sigma>\<Sigma>9Oc s = dtor_J o f'"
shows "F_map (extdd9 (restr f')) o s = dtor_J o restr f'"
unfolding extdd9_def restr_def \<Sigma>\<Sigma>9.map_comp0
unfolding o_assoc mor_cut\<Sigma>\<Sigma>9Oc_flat9[OF f']
unfolding o_assoc[symmetric] leaf9_flat9 o_id
unfolding o_assoc f'[symmetric]
unfolding o_assoc[symmetric] c\<Sigma>\<Sigma>9Ocut_cut\<Sigma>\<Sigma>9Oc[unfolded c\<Sigma>\<Sigma>9Ocut_def] ..

lemma extdd9_restr:
assumes f': "F_map f' o cut\<Sigma>\<Sigma>9Oc s = dtor_J o f'"
shows "extdd9 (restr f') = f'"
proof-
  have "f' = eval9 o \<Sigma>\<Sigma>9_map f' o leaf9"
  unfolding o_assoc[symmetric] leaf9_natural
  unfolding o_assoc eval9_leaf9 by simp
  also have "... = eval9 o \<Sigma>\<Sigma>9_map (f' o leaf9)"
  unfolding \<Sigma>\<Sigma>9.map_comp0 o_assoc
  unfolding mor_cut\<Sigma>\<Sigma>9Oc_flat9[OF f'] unfolding o_assoc[symmetric] flat9_leaf9 leaf9_flat9 ..
  finally have A: "f' = eval9 o \<Sigma>\<Sigma>9_map (f' o leaf9)" .
  show ?thesis unfolding extdd9_def restr_def A[symmetric] ..
qed

lemma restr_inj:
assumes f9': "F_map f9' o cut\<Sigma>\<Sigma>9Oc s = dtor_J o f9'"
and f2': "F_map f2' o cut\<Sigma>\<Sigma>9Oc s = dtor_J o f2'"
shows "restr f9' = restr f2' \<longleftrightarrow> f9' = f2'"
using extdd9_restr[OF f9'] extdd9_restr[OF f2'] by metis

lemma extdd9_surj:
assumes f': "F_map f' o cut\<Sigma>\<Sigma>9Oc s = dtor_J o f'"
shows "\<exists> f. extdd9 f = f'"
using extdd9_restr[OF f'] by(rule exI[of _ "restr f'"])

lemma restr_extdd9:
assumes f: "F_map (extdd9 f) o s = dtor_J o f"
shows "restr (extdd9 f) = f"
proof-
  have "dtor_J o f = F_map (extdd9 f) o s" using assms unfolding extdd9_def by (rule sym)
  also have "... = dtor_J o restr (extdd9 f)"
  unfolding restr_def unfolding o_assoc extdd9_mor[OF f, symmetric]
  unfolding o_assoc[symmetric] c\<Sigma>\<Sigma>9Ocut_cut\<Sigma>\<Sigma>9Oc[unfolded c\<Sigma>\<Sigma>9Ocut_def] ..
  finally have "dtor_J o f = dtor_J \<circ> restr (extdd9 f)" .
  thus ?thesis unfolding dtor_J_o_inj by (rule sym)
qed

lemma extdd9_inj:
assumes f1: "F_map (extdd9 f1) o s = dtor_J o f1"
and f2: "F_map (extdd9 f2) o s = dtor_J o f2"
shows "extdd9 f1 = extdd9 f2 \<longleftrightarrow> f1 = f2"
using restr_extdd9[OF f1] restr_extdd9[OF f2] by metis

lemma restr_surj:
assumes f: "F_map (extdd9 f) o s = dtor_J o f"
shows "\<exists> f'. restr f' = f"
using restr_extdd9[OF f] by(rule exI[of _ "extdd9 f"])


subsection{* Coiteration up-to *}

definition "unfoldU9 s \<equiv> restr (dtor_unfold_J (cut\<Sigma>\<Sigma>9Oc s))"

theorem unfoldU9_pointfree:
"F_map (extdd9 (unfoldU9 s)) o s = dtor_J o unfoldU9 s"
unfolding unfoldU9_def apply(rule restr_mor)
unfolding dtor_unfold_J_pointfree ..

theorem unfoldU9: "F_map (extdd9 (unfoldU9 s)) (s a) = dtor_J (unfoldU9 s a)"
using unfoldU9_pointfree unfolding o_def fun_eq_iff by(rule allE)

theorem unfoldU9_ctor_J:
"ctor_J (F_map (extdd9 (unfoldU9 s)) (s a)) = unfoldU9 s a"
using unfoldU9 by (metis J.ctor_dtor)

theorem unfoldU9_unique:
assumes "F_map (extdd9 f) o s = dtor_J o f"
shows "f = unfoldU9 s"
proof-
  note f = extdd9_mor[OF assms]  note co = extdd9_mor[OF unfoldU9_pointfree]
  have A: "extdd9 f = extdd9 (unfoldU9 s)"
  proof(rule trans)
    show "extdd9 f = dtor_unfold_J (cut\<Sigma>\<Sigma>9Oc s)" apply(rule J.dtor_unfold_unique) using f .
    show "dtor_unfold_J (cut\<Sigma>\<Sigma>9Oc s) = extdd9 (unfoldU9 s)"
     apply(rule J.dtor_unfold_unique[symmetric]) using co .
  qed
  show ?thesis using A unfolding extdd9_inj[OF assms unfoldU9_pointfree] .
qed

lemma unfoldU9_ctor_J_pointfree:
"ctor_J o F_map (extdd9 (unfoldU9 s)) o s = unfoldU9 s"
unfolding o_def fun_eq_iff by (subst unfoldU9_ctor_J[symmetric]) (rule allI, rule refl)

(* Corecursion up to: *)
definition corecU9 :: "('a \<Rightarrow> (J + 'a) \<Sigma>\<Sigma>9 F) \<Rightarrow> 'a \<Rightarrow> J" where
"corecU9 s = unfoldU9 (case_sum (dd9 o leaf9 o <Inl, F_map Inl o dtor_J>) s) o Inr"

definition extddRec9 where
"extddRec9 f \<equiv> eval9 \<circ> \<Sigma>\<Sigma>9_map (case_sum id f)"

lemma unfoldU9_Inl:
"unfoldU9 (case_sum (dd9 \<circ> leaf9 \<circ> <Inl , F_map Inl \<circ> dtor_J>) s) o Inl = id"
(is "?L = ?R")
proof-
  have "?L = unfoldU9 (dd9 o leaf9 o <id, dtor_J>)"
  apply(rule unfoldU9_unique)
  unfolding o_assoc unfoldU9_pointfree[symmetric]
  unfolding o_assoc[symmetric] case_sum_o_inj extdd9_def F_map_comp \<Sigma>\<Sigma>9.map_comp0
  unfolding o_assoc apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric],
                          subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
  unfolding dd9_natural[symmetric]
  apply(subst o_assoc[symmetric]) unfolding leaf9_natural
  unfolding o_assoc[symmetric] map_prod_o_convol o_id ..
  also have "... = ?R"
  apply(rule sym, rule unfoldU9_unique)
  unfolding extdd9_def \<Sigma>\<Sigma>9.map_id0 o_id dd9_leaf9
  unfolding o_assoc[symmetric] snd_convol
  unfolding o_assoc F_map_comp[symmetric] eval9_leaf9 F_map_id id_o ..
  finally show ?thesis .
qed

theorem corecU9_pointfree:
"F_map (extddRec9 (corecU9 s)) o s = dtor_J o corecU9 s" (is "?L = ?R")
unfolding corecU9_def
unfolding o_assoc unfoldU9_pointfree[symmetric] extddRec9_def
unfolding o_assoc[symmetric] case_sum_o_inj
apply(subst unfoldU9_Inl[symmetric, of s])
unfolding o_assoc case_sum_Inl_Inr_L extdd9_def ..

theorem corecU9:
"F_map (extddRec9 (corecU9 s)) (s a) = dtor_J (corecU9 s a)"
using corecU9_pointfree unfolding o_def fun_eq_iff by(rule allE)


subsection{* Coinduction up-to *}

definition "cptdd9 R \<equiv> (\<Sigma>\<Sigma>9_rel R ===> R) eval9 eval9"

definition "cngdd9 R \<equiv> equivp R \<and> cptdd9 R"

lemma cngdd9_Retr: "cngdd9 R \<Longrightarrow> cngdd9 (R \<sqinter> Retr R)"
  unfolding cngdd9_def cptdd9_def
  apply (erule conjE)
  apply (rule conjI[OF equivp_inf[OF _ equivp_retr]])
  apply assumption
  apply assumption
  apply (rule rel_funI)
  apply (frule predicate2D[OF \<Sigma>\<Sigma>9_rel_inf])
  apply (erule inf2E)
  apply (rule inf2I)
  apply (erule rel_funE)
  apply assumption
  apply assumption
  apply (subst Retr_def)
  apply (subst eval9_def)+
  apply (subst J.dtor_unfold)+
  unfolding F_rel_F_map_F_map Grp_def relcompp.simps[abs_def] conversep.simps[abs_def]
  apply auto
  unfolding eval9_def[symmetric]
  apply (rule predicate2D[OF F_rel_mono])
  apply (rule predicate2I)
  apply (erule rel_funD)
  apply assumption
  apply (rule F_rel_\<Sigma>\<Sigma>9_rel)
  unfolding \<Sigma>\<Sigma>9_rel_\<Sigma>\<Sigma>9_map_\<Sigma>\<Sigma>9_map vimage2p_rel_prod vimage2p_id
  unfolding vimage2p_def Retr_def[symmetric]
  apply assumption
  done

(* The generated congruence: *)
definition "genCngdd9 R j1 j2 \<equiv> \<forall> R'. R \<le> R' \<and> cngdd9 R' \<longrightarrow> R' j1 j2"

lemma cngdd9_genCngdd9: "cngdd9 (genCngdd9 R)"
unfolding cngdd9_def proof safe
  show "cptdd9 (genCngdd9 R)"
  unfolding cptdd9_def rel_fun_def proof safe
    fix x y assume A: "\<Sigma>\<Sigma>9_rel (genCngdd9 R) x y"
    show "genCngdd9 R (eval9 x) (eval9 y)"
    unfolding genCngdd9_def[abs_def] proof safe
      fix R' assume "R \<le> R'" and 2: "cngdd9 R'"
      hence "\<Sigma>\<Sigma>9_rel R' x y" by (metis A \<Sigma>\<Sigma>9.rel_mono_strong genCngdd9_def)
      thus "R' (eval9 x) (eval9 y)" using 2 unfolding cngdd9_def cptdd9_def rel_fun_def by auto
    qed
  qed
qed(rule equivpI, unfold reflp_def symp_def transp_def genCngdd9_def cngdd9_def equivp_def, auto)

lemma
    genCngdd9_refl[intro,simp]: "genCngdd9 R j j"
and genCngdd9_sym[intro]: "genCngdd9 R j1 j2 \<Longrightarrow> genCngdd9 R j2 j1"
and genCngdd9_trans[intro]: "\<lbrakk>genCngdd9 R j1 j2; genCngdd9 R j2 j3\<rbrakk> \<Longrightarrow> genCngdd9 R j1 j3"
using cngdd9_genCngdd9 unfolding cngdd9_def equivp_def by auto

lemma genCngdd9_eval9_rel_fun: "(\<Sigma>\<Sigma>9_rel (genCngdd9 R) ===> genCngdd9 R) eval9 eval9"
using cngdd9_genCngdd9 unfolding cngdd9_def cptdd9_def by auto

lemma genCngdd9_eval9: "\<Sigma>\<Sigma>9_rel (genCngdd9 R) x y \<Longrightarrow> genCngdd9 R (eval9 x) (eval9 y)"
using genCngdd9_eval9_rel_fun unfolding rel_fun_def by auto

lemma leq_genCngdd9: "R \<le> genCngdd9 R"
and imp_genCngdd9[intro]: "R j1 j2 \<Longrightarrow> genCngdd9 R j1 j2"
unfolding genCngdd9_def[abs_def] by auto

lemma genCngdd9_minimal: "\<lbrakk>R \<le> R'; cngdd9 R'\<rbrakk> \<Longrightarrow> genCngdd9 R \<le> R'"
unfolding genCngdd9_def[abs_def] by (metis (lifting, no_types) predicate2I)

theorem coinductionU_genCngdd9:
assumes "\<forall> a b. R a b \<longrightarrow> F_rel (genCngdd9 R) (dtor_J a) (dtor_J b)"
shows "R a b \<longrightarrow> a = b"
proof-
  let ?R' = "genCngdd9 R"
  have "R \<le> Retr ?R'" using assms unfolding Retr_def[abs_def] by auto
  hence "R \<le> ?R' \<sqinter> Retr ?R'" using leq_genCngdd9 by auto
  moreover have "cngdd9 (?R' \<sqinter> Retr ?R')" using cngdd9_Retr[OF cngdd9_genCngdd9[of R]] .
  ultimately have "?R' \<le> ?R' \<sqinter> Retr ?R'" using genCngdd9_minimal by metis
  hence "?R' \<le> Retr ?R'" by auto
  hence "?R' a b \<longrightarrow> a = b"  unfolding Retr_def[abs_def] by (intro J.dtor_coinduct) auto
  thus ?thesis using leq_genCngdd9 by auto
qed


subsection{* Flattening from term algebra to "one-step" algebra *}

(* Since (J \<Sigma>\<Sigma>9, eval9) is an Eilenberg-Moore algebra (i.e., is compatible with
the monadic structure, it yields an algebra on the signature functor.
This is crucial for having suitable simplification rules. *)

(* The one-step algebra (naturally associated to \<Lambda>9, not to dd9): *)
definition alg\<Lambda>9 :: "J \<Sigma>9 \<Rightarrow> J" where "alg\<Lambda>9 = eval9 o \<oo>\<pp>9 o \<Sigma>9_map leaf9"

theorem eval9_comp_\<oo>\<pp>9: "eval9 o \<oo>\<pp>9 = alg\<Lambda>9 o \<Sigma>9_map eval9"
unfolding alg\<Lambda>9_def
unfolding o_assoc[symmetric] \<Sigma>9.map_comp0[symmetric]
unfolding leaf9_natural[symmetric] unfolding \<Sigma>9.map_comp0
apply(rule sym) unfolding o_assoc apply(subst o_assoc[symmetric])
unfolding \<oo>\<pp>9_natural
unfolding o_assoc eval9_flat9[symmetric]
apply(subst o_assoc[symmetric]) unfolding flat9_commute[symmetric]
unfolding o_assoc[symmetric] \<Sigma>9.map_comp0[symmetric] flat9_leaf9 \<Sigma>9.map_id0 o_id ..

theorem eval9_\<oo>\<pp>9: "eval9 (\<oo>\<pp>9 t) = alg\<Lambda>9 (\<Sigma>9_map eval9 t)"
using eval9_comp_\<oo>\<pp>9 unfolding o_def fun_eq_iff by (rule allE)

theorem eval9_leaf9': "eval9 (leaf9 j) = j"
using eval9_leaf9 unfolding o_def fun_eq_iff id_def by (rule allE)

theorem dtor_J_alg\<Lambda>9: "dtor_J o alg\<Lambda>9 = F_map eval9 o \<Lambda>9 o \<Sigma>9_map <id, dtor_J>"
  unfolding alg\<Lambda>9_def eval9_def o_assoc dtor_unfold_J_pointfree \<Lambda>9_dd9
  unfolding o_assoc[symmetric] \<oo>\<pp>9_natural[symmetric] \<Sigma>9.map_comp0[symmetric] leaf9_natural
  ..

theorem dtor_J_alg\<Lambda>9': "dtor_J (alg\<Lambda>9 t) = F_map eval9 (\<Lambda>9 (\<Sigma>9_map (<id, dtor_J>) t))"
  by (rule trans[OF o_eq_dest[OF dtor_J_alg\<Lambda>9] o_apply])

theorem ctor_J_alg\<Lambda>9: "alg\<Lambda>9 t = ctor_J (F_map eval9 (\<Lambda>9 (\<Sigma>9_map (<id, dtor_J>) t)))"
  by (rule iffD1[OF J.dtor_inject trans[OF dtor_J_alg\<Lambda>9' J.dtor_ctor[symmetric]]])

(* Note: The user wi\<Lambda>9 indicate an "equation" equ :: J \<Sigma>9 \<Rightarrow> (J \<Sigma>\<Sigma>9) F
in order to define the operation alg\<Lambda>9 :: J \<Sigma>9 \<Rightarrow> J on the final coalgebra
according to dtor_J_alg\<Lambda>9.
The package wi\<Lambda>9 identify the polymorphic function \<Lambda>9 :: ('a \<times> 'a F) \<Sigma>9 \<Rightarrow> 'a \<Sigma>\<Sigma>9 F
such that equ = \<Lambda>9 o \<Sigma>9 <id, dtor_J>. Then the package wi\<Lambda>9 attempt to prove
automatica\<Lambda>9y that \<Lambda>9 is natural.  If the proof fails, the user wi\<Lambda>9 be asked to prove it.
Upon success, the distributive law is being registered.
*)

(* Customizing coinduction up-to: *)
definition "cpt\<Lambda>9 R \<equiv> (\<Sigma>9_rel R ===> R) alg\<Lambda>9 alg\<Lambda>9"

definition "cng\<Lambda>9 R \<equiv> equivp R \<and> cpt\<Lambda>9 R"

lemma cptdd9_iff_cpt\<Lambda>9: "cptdd9 R \<longleftrightarrow> cpt\<Lambda>9 R"
apply (rule iffI)
apply (unfold cpt\<Lambda>9_def cptdd9_def alg\<Lambda>9_def o_assoc[symmetric]) [1]
apply (erule rel_funD[OF rel_funD[OF comp_transfer]])
apply transfer_prover

apply (unfold cpt\<Lambda>9_def cptdd9_def) [1]
unfolding rel_fun_def
apply (rule allI)+
apply (rule \<Sigma>\<Sigma>9_rel_induct)
apply (simp only: eval9_leaf9')
unfolding eval9_\<oo>\<pp>9
apply (drule spec2)
apply (erule mp)
apply (rule iffD2[OF \<Sigma>9_rel_\<Sigma>9_map_\<Sigma>9_map])
apply (subst vimage2p_def)
apply assumption
done

(* This is the definition of genCngdd9 we need to work with: *)
theorem genCngdd9_def2: "genCngdd9 R j1 j2 \<longleftrightarrow> (\<forall> R'. R \<le> R' \<and> cng\<Lambda>9 R' \<longrightarrow> R' j1 j2)"
unfolding genCngdd9_def cngdd9_def cng\<Lambda>9_def cptdd9_iff_cpt\<Lambda>9 ..


subsection {* Incremental coinduction *}

interpretation I9: Incremental where Retr = Retr and Cl = genCngdd9
proof
  show "mono Retr" by (rule mono_retr)
next
  show "mono genCngdd9" unfolding mono_def
  unfolding genCngdd9_def[abs_def] by (smt order.trans predicate2I)
next
  fix r show "genCngdd9 (genCngdd9 r) = genCngdd9 r"
  by (metis cngdd9_genCngdd9 genCngdd9_minimal leq_genCngdd9 order_class.order.antisym)
next
  fix r show "r \<le> genCngdd9 r" by (metis leq_genCngdd9)
next
  fix r assume "genCngdd9 r = r" thus "genCngdd9 (r \<sqinter> Retr r) = r \<sqinter> Retr r"
  by (metis antisym cngdd9_Retr cngdd9_genCngdd9 genCngdd9_minimal
            inf.orderI inf_idem leq_genCngdd9)
qed

definition ded9 where "ded9 r s \<equiv> I9.ded r s"

theorems Ax = I9.Ax'[unfolded ded9_def[symmetric]]
theorems Split = I9.Split[unfolded ded9_def[symmetric]]
theorems Coind = I9.Coind[unfolded ded9_def[symmetric]]

theorem soundness_ded:
assumes "ded9 (op =) s"  shows "s \<le> (op =)"
unfolding gfp_Retr_eq[symmetric] apply(rule I9.soundness_ded[unfolded ded9_def[symmetric]] )
using assms unfolding gfp_Retr_eq[symmetric] ded9_def .

unused_thms

end
