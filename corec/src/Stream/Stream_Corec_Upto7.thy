header {* Corecursion and coinduction up to *}

theory Stream_Corec_Upto7
imports Stream_Lift_to_Free7
begin


subsection{* The algebra associated to dd7 *}

definition "eval7 \<equiv> dtor_unfold_J (dd7 o \<Sigma>\<Sigma>7_map <id, dtor_J>)"

lemma eval7: "F_map eval7 o dd7 o \<Sigma>\<Sigma>7_map <id, dtor_J> = dtor_J o eval7"
  unfolding eval7_def dtor_unfold_J_pointfree unfolding o_assoc ..

lemma eval7_ctor_J: "ctor_J o F_map eval7 o dd7 o \<Sigma>\<Sigma>7_map <id, dtor_J> = eval7"
  unfolding o_def spec[OF eval7[unfolded o_def fun_eq_iff]] J.ctor_dtor ..

lemma eval7_leaf7: "eval7 \<circ> leaf7 = id"
proof (rule trans)
  show "eval7 \<circ> leaf7 = dtor_unfold_J dtor_J"
  apply(rule J.dtor_unfold_unique)
  unfolding o_assoc eval7[symmetric] unfolding o_assoc[symmetric] leaf7_natural
  apply(rule sym)
  unfolding F_map_comp o_assoc apply (subst o_assoc[symmetric])
  unfolding dd7_leaf7 unfolding o_assoc[symmetric] by simp
qed(metis F_map_id J.dtor_unfold_unique fun.map_id o_id)

lemma eval7_flat7: "eval7 \<circ> flat7 = eval7 \<circ> \<Sigma>\<Sigma>7_map eval7"
proof (rule trans)
  let ?K7 = "dtor_unfold_J (dd7 o \<Sigma>\<Sigma>7_map <\<Sigma>\<Sigma>7_map fst, dd7> o \<Sigma>\<Sigma>7_map (\<Sigma>\<Sigma>7_map <id, dtor_J>))"
  show "eval7 \<circ> flat7 = ?K7"
  apply(rule J.dtor_unfold_unique)
  unfolding F_map_comp o_assoc
  apply(subst o_assoc[symmetric], subst o_assoc[symmetric])
  unfolding dd7_flat7
  unfolding o_assoc[symmetric] \<Sigma>\<Sigma>7.map_comp0[symmetric] snd_convol
  unfolding flat7_natural
  unfolding o_assoc eval7 ..
  (*  *)
  have A: "<eval7, dtor_J o eval7> = <id,dtor_J> o eval7" by simp
  show "?K7 = eval7 \<circ> \<Sigma>\<Sigma>7_map eval7"
  apply(rule J.dtor_unfold_unique[symmetric])
  unfolding o_assoc[symmetric] \<Sigma>\<Sigma>7.map_comp0[symmetric] map_prod_o_convol id_o
  unfolding F_map_comp o_assoc
  apply(subst o_assoc[symmetric]) unfolding dd7_natural[symmetric]
  unfolding o_assoc[symmetric] \<Sigma>\<Sigma>7.map_comp0[symmetric]
  unfolding o_assoc unfolding map_prod_o_convol unfolding convol_o
  unfolding o_assoc[symmetric] \<Sigma>\<Sigma>7.map_comp0[symmetric] fst_convol \<Sigma>\<Sigma>7.map_id0 o_id
  unfolding o_assoc eval7 unfolding A unfolding convol_o id_o
  apply(rule sym) apply(subst eval7[symmetric])
  unfolding o_assoc[symmetric] \<Sigma>\<Sigma>7.map_comp0[symmetric] convol_o id_o ..
qed


subsection{* The correspondence between coalgebras up to and coalgebras *}

(* This correspondence, and add7 the lemmas of this subsection, make
sense not only for (J,dtor_J,eval7), but also for any dd7-bialgebra *)

(* Coalgebra-up-to to coalgebra and vice versa: *)
definition cut\<Sigma>\<Sigma>7Oc :: "('a \<Rightarrow> 'a \<Sigma>\<Sigma>7 F) \<Rightarrow> ('a \<Sigma>\<Sigma>7 \<Rightarrow> 'a \<Sigma>\<Sigma>7 F)"
where "cut\<Sigma>\<Sigma>7Oc s \<equiv> F_map flat7 o dd7 o \<Sigma>\<Sigma>7_map <leaf7, s>"
definition c\<Sigma>\<Sigma>7Ocut :: "('a \<Sigma>\<Sigma>7 \<Rightarrow> 'a \<Sigma>\<Sigma>7 F) \<Rightarrow> ('a \<Rightarrow> 'a \<Sigma>\<Sigma>7 F)"
where "c\<Sigma>\<Sigma>7Ocut s' \<equiv> s' o leaf7"

lemma c\<Sigma>\<Sigma>7Ocut_cut\<Sigma>\<Sigma>7Oc: "c\<Sigma>\<Sigma>7Ocut (cut\<Sigma>\<Sigma>7Oc s) = s"
unfolding c\<Sigma>\<Sigma>7Ocut_def cut\<Sigma>\<Sigma>7Oc_def
unfolding o_assoc[symmetric] unfolding leaf7_natural
unfolding o_assoc apply(subst o_assoc[symmetric])
unfolding dd7_leaf7 unfolding o_assoc F_map_comp[symmetric] flat7_leaf7
unfolding F_map_id id_o by simp

lemma cut\<Sigma>\<Sigma>7Oc_inj: "cut\<Sigma>\<Sigma>7Oc s7 = cut\<Sigma>\<Sigma>7Oc s2 \<longleftrightarrow> s7 = s2"
by (metis c\<Sigma>\<Sigma>7Ocut_cut\<Sigma>\<Sigma>7Oc)

lemma c\<Sigma>\<Sigma>7Ocut_surj: "\<exists> s'. c\<Sigma>\<Sigma>7Ocut s' = s"
using c\<Sigma>\<Sigma>7Ocut_cut\<Sigma>\<Sigma>7Oc by(rule exI[of _ "cut\<Sigma>\<Sigma>7Oc s"])

(* Morphism-up-to to morphism and vice versa: *)
(* The dd7-extension of a function *)
definition extdd7 :: "('a \<Rightarrow> J) \<Rightarrow> ('a \<Sigma>\<Sigma>7 \<Rightarrow> J)"
where "extdd7 f \<equiv> eval7 o \<Sigma>\<Sigma>7_map f"
(* The restriction of a function *)  term eval7
definition restr :: "('a \<Sigma>\<Sigma>7 \<Rightarrow> J) \<Rightarrow> ('a \<Rightarrow> J)"
where "restr f' \<equiv> f' o leaf7"

(* We think of extdd7 and restr as operating
extdd7 : Hom_dd7(s,dtor_J) \<rightarrow> Hom(cut\<Sigma>\<Sigma>7Oc s,dtor_J) and
restr : Hom(cut\<Sigma>\<Sigma>7Oc s,dtor_J) \<rightarrow> Hom_dd7(s,dtor_J), where
Hom(cut\<Sigma>\<Sigma>7Oc s,dtor_J) is the set of coalgebra morphisms betwee cut\<Sigma>\<Sigma>7Oc s and dtor_J and
Hom_dd7(s,dtor_J) is the set of coalgebra up-to-dd7-morphisms between s and dtor_J  *)

(* extdd7 is wedd7-defined: *)
lemma extdd7_mor:
assumes f:  "F_map (extdd7 f) o s = dtor_J o f"
shows "F_map (extdd7 f) o cut\<Sigma>\<Sigma>7Oc s = dtor_J o (extdd7 f)"
proof-
  have AA: "eval7 ** F_map eval7 \<circ> (\<Sigma>\<Sigma>7_map f ** F_map (\<Sigma>\<Sigma>7_map f) \<circ> <leaf7 , s>) =
            <f , F_map eval7 \<circ> (F_map (\<Sigma>\<Sigma>7_map f) \<circ> s)>"
  unfolding map_prod_o_convol unfolding leaf7_natural o_assoc eval7_leaf7 id_o  ..
  show ?thesis
  unfolding extdd7_def
  unfolding o_assoc eval7[symmetric]
  unfolding o_assoc[symmetric] \<Sigma>\<Sigma>7.map_comp0[symmetric]
  unfolding convol_comp[symmetric] id_o
  unfolding f[symmetric, unfolded extdd7_def]
  unfolding o_assoc
  apply(subst o_assoc[symmetric])
  unfolding F_map_comp o_assoc
  unfolding cut\<Sigma>\<Sigma>7Oc_def
  unfolding o_assoc
  unfolding F_map_comp[symmetric] unfolding o_assoc[symmetric]
  unfolding flat7_natural[symmetric]
  unfolding o_assoc F_map_comp
  apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
  unfolding dd7_natural[symmetric]
  unfolding o_assoc unfolding F_map_comp[symmetric] eval7_flat7
  unfolding F_map_comp apply(subst o_assoc[symmetric])
  unfolding dd7_natural[symmetric] unfolding o_assoc[symmetric] \<Sigma>\<Sigma>7.map_comp0[symmetric]
  unfolding o_assoc[symmetric] AA[unfolded o_assoc[symmetric]] ..
qed

lemma mor_cut\<Sigma>\<Sigma>7Oc_flat7:
assumes f': "F_map f' o cut\<Sigma>\<Sigma>7Oc s = dtor_J o f'"
shows "eval7 o \<Sigma>\<Sigma>7_map f' = f' o flat7"
proof(rule trans) (* this proof is clearly improvable: *)
  def h \<equiv> "dd7 o \<Sigma>\<Sigma>7_map <id,cut\<Sigma>\<Sigma>7Oc s>"
  have f'_id: "f' = f' o id" by simp
  show "eval7 \<circ> \<Sigma>\<Sigma>7_map f' = dtor_unfold_J h"
  apply(rule J.dtor_unfold_unique, rule sym)
  unfolding o_assoc eval7[symmetric]
  unfolding o_assoc[symmetric] \<Sigma>\<Sigma>7.map_comp0[symmetric]
  unfolding convol_comp_id1[symmetric] unfolding f'[symmetric]
  apply(subst f'_id)
  unfolding o_assoc \<Sigma>\<Sigma>7.map_comp0
  apply(subst o_assoc[symmetric])
  unfolding o_assoc[symmetric] F_map_comp
  unfolding h_def apply(rule sym)
  unfolding o_assoc apply(subst o_assoc[symmetric])
  unfolding dd7_natural[symmetric] unfolding o_assoc[symmetric]
  unfolding \<Sigma>\<Sigma>7.map_comp0[symmetric] map_prod_o_convol ..
  (*  *)
  have AA: "<id , cut\<Sigma>\<Sigma>7Oc s> = (flat7 ** F_map flat7) o (id ** dd7) o <leaf7, \<Sigma>\<Sigma>7_map <leaf7 , s>>"
  unfolding map_prod_o_convol o_assoc map_prod.comp cut\<Sigma>\<Sigma>7Oc_def o_id flat7_leaf7 ..
  have BB: "flat7 ** F_map flat7 \<circ> id ** dd7 \<circ> <leaf7 , \<Sigma>\<Sigma>7_map <leaf7 , s>> = flat7 ** F_map flat7 \<circ> id ** dd7 \<circ> <\<Sigma>\<Sigma>7_map leaf7 , \<Sigma>\<Sigma>7_map <leaf7 , s>>"
  unfolding map_prod.comp unfolding map_prod_o_convol unfolding o_id unfolding flat7_leaf7 leaf7_flat7 ..
  show "dtor_unfold_J h = f' \<circ> flat7"
  apply(rule J.dtor_unfold_unique[symmetric], rule sym)
  unfolding o_assoc f'[symmetric]
  unfolding F_map_comp o_assoc[symmetric]
  apply(rule arg_cong[of _ _ "op o (F_map f')"])
  unfolding h_def
  unfolding AA BB
  unfolding \<Sigma>\<Sigma>7.map_comp0 apply(rule sym)
  unfolding o_assoc apply(subst o_assoc[symmetric])
  unfolding dd7_natural
  unfolding o_assoc F_map_comp[symmetric]
  unfolding flat7_assoc unfolding F_map_comp
  unfolding cut\<Sigma>\<Sigma>7Oc_def o_assoc[symmetric] apply(rule arg_cong[of _ _ "op o (F_map flat7)"])
  unfolding o_assoc
  unfolding o_assoc[symmetric] unfolding \<Sigma>\<Sigma>7.map_comp0[symmetric] unfolding map_prod_o_convol id_o
  unfolding flat7_natural[symmetric] unfolding o_assoc
  unfolding dd7_flat7[symmetric] unfolding o_assoc[symmetric] unfolding \<Sigma>\<Sigma>7.map_comp0[symmetric]
  unfolding convol_o unfolding \<Sigma>\<Sigma>7.map_comp0[symmetric] unfolding fst_convol ..
qed

(* restr is wedd7-defined:  *)
lemma restr_mor:
assumes f': "F_map f' o cut\<Sigma>\<Sigma>7Oc s = dtor_J o f'"
shows "F_map (extdd7 (restr f')) o s = dtor_J o restr f'"
unfolding extdd7_def restr_def \<Sigma>\<Sigma>7.map_comp0
unfolding o_assoc mor_cut\<Sigma>\<Sigma>7Oc_flat7[OF f']
unfolding o_assoc[symmetric] leaf7_flat7 o_id
unfolding o_assoc f'[symmetric]
unfolding o_assoc[symmetric] c\<Sigma>\<Sigma>7Ocut_cut\<Sigma>\<Sigma>7Oc[unfolded c\<Sigma>\<Sigma>7Ocut_def] ..

lemma extdd7_restr:
assumes f': "F_map f' o cut\<Sigma>\<Sigma>7Oc s = dtor_J o f'"
shows "extdd7 (restr f') = f'"
proof-
  have "f' = eval7 o \<Sigma>\<Sigma>7_map f' o leaf7"
  unfolding o_assoc[symmetric] leaf7_natural
  unfolding o_assoc eval7_leaf7 by simp
  also have "... = eval7 o \<Sigma>\<Sigma>7_map (f' o leaf7)"
  unfolding \<Sigma>\<Sigma>7.map_comp0 o_assoc
  unfolding mor_cut\<Sigma>\<Sigma>7Oc_flat7[OF f'] unfolding o_assoc[symmetric] flat7_leaf7 leaf7_flat7 ..
  finally have A: "f' = eval7 o \<Sigma>\<Sigma>7_map (f' o leaf7)" .
  show ?thesis unfolding extdd7_def restr_def A[symmetric] ..
qed

lemma restr_inj:
assumes f7': "F_map f7' o cut\<Sigma>\<Sigma>7Oc s = dtor_J o f7'"
and f2': "F_map f2' o cut\<Sigma>\<Sigma>7Oc s = dtor_J o f2'"
shows "restr f7' = restr f2' \<longleftrightarrow> f7' = f2'"
using extdd7_restr[OF f7'] extdd7_restr[OF f2'] by metis

lemma extdd7_surj:
assumes f': "F_map f' o cut\<Sigma>\<Sigma>7Oc s = dtor_J o f'"
shows "\<exists> f. extdd7 f = f'"
using extdd7_restr[OF f'] by(rule exI[of _ "restr f'"])

lemma restr_extdd7:
assumes f: "F_map (extdd7 f) o s = dtor_J o f"
shows "restr (extdd7 f) = f"
proof-
  have "dtor_J o f = F_map (extdd7 f) o s" using assms unfolding extdd7_def by (rule sym)
  also have "... = dtor_J o restr (extdd7 f)"
  unfolding restr_def unfolding o_assoc extdd7_mor[OF f, symmetric]
  unfolding o_assoc[symmetric] c\<Sigma>\<Sigma>7Ocut_cut\<Sigma>\<Sigma>7Oc[unfolded c\<Sigma>\<Sigma>7Ocut_def] ..
  finally have "dtor_J o f = dtor_J \<circ> restr (extdd7 f)" .
  thus ?thesis unfolding dtor_J_o_inj by (rule sym)
qed

lemma extdd7_inj:
assumes f1: "F_map (extdd7 f1) o s = dtor_J o f1"
and f2: "F_map (extdd7 f2) o s = dtor_J o f2"
shows "extdd7 f1 = extdd7 f2 \<longleftrightarrow> f1 = f2"
using restr_extdd7[OF f1] restr_extdd7[OF f2] by metis

lemma restr_surj:
assumes f: "F_map (extdd7 f) o s = dtor_J o f"
shows "\<exists> f'. restr f' = f"
using restr_extdd7[OF f] by(rule exI[of _ "extdd7 f"])


subsection{* Coiteration up-to *}

definition "unfoldU7 s \<equiv> restr (dtor_unfold_J (cut\<Sigma>\<Sigma>7Oc s))"

theorem unfoldU7_pointfree:
"F_map (extdd7 (unfoldU7 s)) o s = dtor_J o unfoldU7 s"
unfolding unfoldU7_def apply(rule restr_mor)
unfolding dtor_unfold_J_pointfree ..

theorem unfoldU7: "F_map (extdd7 (unfoldU7 s)) (s a) = dtor_J (unfoldU7 s a)"
using unfoldU7_pointfree unfolding o_def fun_eq_iff by(rule allE)

theorem unfoldU7_ctor_J:
"ctor_J (F_map (extdd7 (unfoldU7 s)) (s a)) = unfoldU7 s a"
using unfoldU7 by (metis J.ctor_dtor)

theorem unfoldU7_unique:
assumes "F_map (extdd7 f) o s = dtor_J o f"
shows "f = unfoldU7 s"
proof-
  note f = extdd7_mor[OF assms]  note co = extdd7_mor[OF unfoldU7_pointfree]
  have A: "extdd7 f = extdd7 (unfoldU7 s)"
  proof(rule trans)
    show "extdd7 f = dtor_unfold_J (cut\<Sigma>\<Sigma>7Oc s)" apply(rule J.dtor_unfold_unique) using f .
    show "dtor_unfold_J (cut\<Sigma>\<Sigma>7Oc s) = extdd7 (unfoldU7 s)"
     apply(rule J.dtor_unfold_unique[symmetric]) using co .
  qed
  show ?thesis using A unfolding extdd7_inj[OF assms unfoldU7_pointfree] .
qed

lemma unfoldU7_ctor_J_pointfree:
"ctor_J o F_map (extdd7 (unfoldU7 s)) o s = unfoldU7 s"
unfolding o_def fun_eq_iff by (subst unfoldU7_ctor_J[symmetric]) (rule allI, rule refl)

(* Corecursion up to: *)
definition corecU7 :: "('a \<Rightarrow> (J + 'a) \<Sigma>\<Sigma>7 F) \<Rightarrow> 'a \<Rightarrow> J" where
"corecU7 s = unfoldU7 (case_sum (dd7 o leaf7 o <Inl, F_map Inl o dtor_J>) s) o Inr"

definition extddRec7 where
"extddRec7 f \<equiv> eval7 \<circ> \<Sigma>\<Sigma>7_map (case_sum id f)"

lemma unfoldU7_Inl:
"unfoldU7 (case_sum (dd7 \<circ> leaf7 \<circ> <Inl , F_map Inl \<circ> dtor_J>) s) o Inl = id"
(is "?L = ?R")
proof-
  have "?L = unfoldU7 (dd7 o leaf7 o <id, dtor_J>)"
  apply(rule unfoldU7_unique)
  unfolding o_assoc unfoldU7_pointfree[symmetric]
  unfolding o_assoc[symmetric] case_sum_o_inj extdd7_def F_map_comp \<Sigma>\<Sigma>7.map_comp0
  unfolding o_assoc apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric],
                          subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
  unfolding dd7_natural[symmetric]
  apply(subst o_assoc[symmetric]) unfolding leaf7_natural
  unfolding o_assoc[symmetric] map_prod_o_convol o_id ..
  also have "... = ?R"
  apply(rule sym, rule unfoldU7_unique)
  unfolding extdd7_def \<Sigma>\<Sigma>7.map_id0 o_id dd7_leaf7
  unfolding o_assoc[symmetric] snd_convol
  unfolding o_assoc F_map_comp[symmetric] eval7_leaf7 F_map_id id_o ..
  finally show ?thesis .
qed

theorem corecU7_pointfree:
"F_map (extddRec7 (corecU7 s)) o s = dtor_J o corecU7 s" (is "?L = ?R")
unfolding corecU7_def
unfolding o_assoc unfoldU7_pointfree[symmetric] extddRec7_def
unfolding o_assoc[symmetric] case_sum_o_inj
apply(subst unfoldU7_Inl[symmetric, of s])
unfolding o_assoc case_sum_Inl_Inr_L extdd7_def ..

theorem corecU7:
"F_map (extddRec7 (corecU7 s)) (s a) = dtor_J (corecU7 s a)"
using corecU7_pointfree unfolding o_def fun_eq_iff by(rule allE)


subsection{* Coinduction up-to *}

definition "cptdd7 R \<equiv> (\<Sigma>\<Sigma>7_rel R ===> R) eval7 eval7"

definition "cngdd7 R \<equiv> equivp R \<and> cptdd7 R"

lemma cngdd7_Retr: "cngdd7 R \<Longrightarrow> cngdd7 (R \<sqinter> Retr R)"
  unfolding cngdd7_def cptdd7_def
  apply (erule conjE)
  apply (rule conjI[OF equivp_inf[OF _ equivp_retr]])
  apply assumption
  apply assumption
  apply (rule rel_funI)
  apply (frule predicate2D[OF \<Sigma>\<Sigma>7_rel_inf])
  apply (erule inf2E)
  apply (rule inf2I)
  apply (erule rel_funE)
  apply assumption
  apply assumption
  apply (subst Retr_def)
  apply (subst eval7_def)+
  apply (subst J.dtor_unfold)+
  unfolding F_rel_F_map_F_map Grp_def relcompp.simps[abs_def] conversep.simps[abs_def]
  apply auto
  unfolding eval7_def[symmetric]
  apply (rule predicate2D[OF F_rel_mono])
  apply (rule predicate2I)
  apply (erule rel_funD)
  apply assumption
  apply (rule F_rel_\<Sigma>\<Sigma>7_rel)
  unfolding \<Sigma>\<Sigma>7_rel_\<Sigma>\<Sigma>7_map_\<Sigma>\<Sigma>7_map vimage2p_rel_prod vimage2p_id
  unfolding vimage2p_def Retr_def[symmetric]
  apply assumption
  done

(* The generated congruence: *)
definition "genCngdd7 R j1 j2 \<equiv> \<forall> R'. R \<le> R' \<and> cngdd7 R' \<longrightarrow> R' j1 j2"

lemma cngdd7_genCngdd7: "cngdd7 (genCngdd7 R)"
unfolding cngdd7_def proof safe
  show "cptdd7 (genCngdd7 R)"
  unfolding cptdd7_def rel_fun_def proof safe
    fix x y assume A: "\<Sigma>\<Sigma>7_rel (genCngdd7 R) x y"
    show "genCngdd7 R (eval7 x) (eval7 y)"
    unfolding genCngdd7_def[abs_def] proof safe
      fix R' assume "R \<le> R'" and 2: "cngdd7 R'"
      hence "\<Sigma>\<Sigma>7_rel R' x y" by (metis A \<Sigma>\<Sigma>7.rel_mono_strong genCngdd7_def)
      thus "R' (eval7 x) (eval7 y)" using 2 unfolding cngdd7_def cptdd7_def rel_fun_def by auto
    qed
  qed
qed(rule equivpI, unfold reflp_def symp_def transp_def genCngdd7_def cngdd7_def equivp_def, auto)

lemma
    genCngdd7_refl[intro,simp]: "genCngdd7 R j j"
and genCngdd7_sym[intro]: "genCngdd7 R j1 j2 \<Longrightarrow> genCngdd7 R j2 j1"
and genCngdd7_trans[intro]: "\<lbrakk>genCngdd7 R j1 j2; genCngdd7 R j2 j3\<rbrakk> \<Longrightarrow> genCngdd7 R j1 j3"
using cngdd7_genCngdd7 unfolding cngdd7_def equivp_def by auto

lemma genCngdd7_eval7_rel_fun: "(\<Sigma>\<Sigma>7_rel (genCngdd7 R) ===> genCngdd7 R) eval7 eval7"
using cngdd7_genCngdd7 unfolding cngdd7_def cptdd7_def by auto

lemma genCngdd7_eval7: "\<Sigma>\<Sigma>7_rel (genCngdd7 R) x y \<Longrightarrow> genCngdd7 R (eval7 x) (eval7 y)"
using genCngdd7_eval7_rel_fun unfolding rel_fun_def by auto

lemma leq_genCngdd7: "R \<le> genCngdd7 R"
and imp_genCngdd7[intro]: "R j1 j2 \<Longrightarrow> genCngdd7 R j1 j2"
unfolding genCngdd7_def[abs_def] by auto

lemma genCngdd7_minimal: "\<lbrakk>R \<le> R'; cngdd7 R'\<rbrakk> \<Longrightarrow> genCngdd7 R \<le> R'"
unfolding genCngdd7_def[abs_def] by (metis (lifting, no_types) predicate2I)

theorem coinductionU_genCngdd7:
assumes "\<forall> a b. R a b \<longrightarrow> F_rel (genCngdd7 R) (dtor_J a) (dtor_J b)"
shows "R a b \<longrightarrow> a = b"
proof-
  let ?R' = "genCngdd7 R"
  have "R \<le> Retr ?R'" using assms unfolding Retr_def[abs_def] by auto
  hence "R \<le> ?R' \<sqinter> Retr ?R'" using leq_genCngdd7 by auto
  moreover have "cngdd7 (?R' \<sqinter> Retr ?R')" using cngdd7_Retr[OF cngdd7_genCngdd7[of R]] .
  ultimately have "?R' \<le> ?R' \<sqinter> Retr ?R'" using genCngdd7_minimal by metis
  hence "?R' \<le> Retr ?R'" by auto
  hence "?R' a b \<longrightarrow> a = b"  unfolding Retr_def[abs_def] by (intro J.dtor_coinduct) auto
  thus ?thesis using leq_genCngdd7 by auto
qed


subsection{* Flattening from term algebra to "one-step" algebra *}

(* Since (J \<Sigma>\<Sigma>7, eval7) is an Eilenberg-Moore algebra (i.e., is compatible with
the monadic structure, it yields an algebra on the signature functor.
This is crucial for having suitable simplification rules. *)

(* The one-step algebra (naturally associated to \<Lambda>7, not to dd7): *)
definition alg\<Lambda>7 :: "J \<Sigma>7 \<Rightarrow> J" where "alg\<Lambda>7 = eval7 o \<oo>\<pp>7 o \<Sigma>7_map leaf7"

theorem eval7_comp_\<oo>\<pp>7: "eval7 o \<oo>\<pp>7 = alg\<Lambda>7 o \<Sigma>7_map eval7"
unfolding alg\<Lambda>7_def
unfolding o_assoc[symmetric] \<Sigma>7.map_comp0[symmetric]
unfolding leaf7_natural[symmetric] unfolding \<Sigma>7.map_comp0
apply(rule sym) unfolding o_assoc apply(subst o_assoc[symmetric])
unfolding \<oo>\<pp>7_natural
unfolding o_assoc eval7_flat7[symmetric]
apply(subst o_assoc[symmetric]) unfolding flat7_commute[symmetric]
unfolding o_assoc[symmetric] \<Sigma>7.map_comp0[symmetric] flat7_leaf7 \<Sigma>7.map_id0 o_id ..

theorem eval7_\<oo>\<pp>7: "eval7 (\<oo>\<pp>7 t) = alg\<Lambda>7 (\<Sigma>7_map eval7 t)"
using eval7_comp_\<oo>\<pp>7 unfolding o_def fun_eq_iff by (rule allE)

theorem eval7_leaf7': "eval7 (leaf7 j) = j"
using eval7_leaf7 unfolding o_def fun_eq_iff id_def by (rule allE)

theorem dtor_J_alg\<Lambda>7: "dtor_J o alg\<Lambda>7 = F_map eval7 o \<Lambda>7 o \<Sigma>7_map <id, dtor_J>"
  unfolding alg\<Lambda>7_def eval7_def o_assoc dtor_unfold_J_pointfree \<Lambda>7_dd7
  unfolding o_assoc[symmetric] \<oo>\<pp>7_natural[symmetric] \<Sigma>7.map_comp0[symmetric] leaf7_natural
  ..

theorem dtor_J_alg\<Lambda>7': "dtor_J (alg\<Lambda>7 t) = F_map eval7 (\<Lambda>7 (\<Sigma>7_map (<id, dtor_J>) t))"
  by (rule trans[OF o_eq_dest[OF dtor_J_alg\<Lambda>7] o_apply])

theorem ctor_J_alg\<Lambda>7: "alg\<Lambda>7 t = ctor_J (F_map eval7 (\<Lambda>7 (\<Sigma>7_map (<id, dtor_J>) t)))"
  by (rule iffD1[OF J.dtor_inject trans[OF dtor_J_alg\<Lambda>7' J.dtor_ctor[symmetric]]])

(* Note: The user wi\<Lambda>7 indicate an "equation" equ :: J \<Sigma>7 \<Rightarrow> (J \<Sigma>\<Sigma>7) F
in order to define the operation alg\<Lambda>7 :: J \<Sigma>7 \<Rightarrow> J on the final coalgebra
according to dtor_J_alg\<Lambda>7.
The package wi\<Lambda>7 identify the polymorphic function \<Lambda>7 :: ('a \<times> 'a F) \<Sigma>7 \<Rightarrow> 'a \<Sigma>\<Sigma>7 F
such that equ = \<Lambda>7 o \<Sigma>7 <id, dtor_J>. Then the package wi\<Lambda>7 attempt to prove
automatica\<Lambda>7y that \<Lambda>7 is natural.  If the proof fails, the user wi\<Lambda>7 be asked to prove it.
Upon success, the distributive law is being registered.
*)

(* Customizing coinduction up-to: *)
definition "cpt\<Lambda>7 R \<equiv> (\<Sigma>7_rel R ===> R) alg\<Lambda>7 alg\<Lambda>7"

definition "cng\<Lambda>7 R \<equiv> equivp R \<and> cpt\<Lambda>7 R"

lemma cptdd7_iff_cpt\<Lambda>7: "cptdd7 R \<longleftrightarrow> cpt\<Lambda>7 R"
apply (rule iffI)
apply (unfold cpt\<Lambda>7_def cptdd7_def alg\<Lambda>7_def o_assoc[symmetric]) [1]
apply (erule rel_funD[OF rel_funD[OF comp_transfer]])
apply transfer_prover

apply (unfold cpt\<Lambda>7_def cptdd7_def) [1]
unfolding rel_fun_def
apply (rule allI)+
apply (rule \<Sigma>\<Sigma>7_rel_induct)
apply (simp only: eval7_leaf7')
unfolding eval7_\<oo>\<pp>7
apply (drule spec2)
apply (erule mp)
apply (rule iffD2[OF \<Sigma>7_rel_\<Sigma>7_map_\<Sigma>7_map])
apply (subst vimage2p_def)
apply assumption
done

(* This is the definition of genCngdd7 we need to work with: *)
theorem genCngdd7_def2: "genCngdd7 R j1 j2 \<longleftrightarrow> (\<forall> R'. R \<le> R' \<and> cng\<Lambda>7 R' \<longrightarrow> R' j1 j2)"
unfolding genCngdd7_def cngdd7_def cng\<Lambda>7_def cptdd7_iff_cpt\<Lambda>7 ..


subsection {* Incremental coinduction *}

interpretation I7: Incremental where Retr = Retr and Cl = genCngdd7
proof
  show "mono Retr" by (rule mono_retr)
next
  show "mono genCngdd7" unfolding mono_def
  unfolding genCngdd7_def[abs_def] by (smt order.trans predicate2I)
next
  fix r show "genCngdd7 (genCngdd7 r) = genCngdd7 r"
  by (metis cngdd7_genCngdd7 genCngdd7_minimal leq_genCngdd7 order_class.order.antisym)
next
  fix r show "r \<le> genCngdd7 r" by (metis leq_genCngdd7)
next
  fix r assume "genCngdd7 r = r" thus "genCngdd7 (r \<sqinter> Retr r) = r \<sqinter> Retr r"
  by (metis antisym cngdd7_Retr cngdd7_genCngdd7 genCngdd7_minimal
            inf.orderI inf_idem leq_genCngdd7)
qed

definition ded7 where "ded7 r s \<equiv> I7.ded r s"

theorems Ax = I7.Ax'[unfolded ded7_def[symmetric]]
theorems Split = I7.Split[unfolded ded7_def[symmetric]]
theorems Coind = I7.Coind[unfolded ded7_def[symmetric]]

theorem soundness_ded:
assumes "ded7 (op =) s"  shows "s \<le> (op =)"
unfolding gfp_Retr_eq[symmetric] apply(rule I7.soundness_ded[unfolded ded7_def[symmetric]] )
using assms unfolding gfp_Retr_eq[symmetric] ded7_def .

unused_thms

end
