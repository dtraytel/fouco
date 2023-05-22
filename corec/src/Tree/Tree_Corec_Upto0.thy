header {* Corecursion and coinduction up to for the initial law *}

theory Tree_Corec_Upto0
imports Tree_Lift_to_Free0
begin


(* This theory works more generally, for any BNFs \<Sigma>\<Sigma>0 and F such that
\<Sigma>\<Sigma>0 is a monad and dd is a (pointed) (\<Sigma>\<Sigma>0,\<Sigma>\<Sigma>0,F)-distributive law compatible with the monadic structure.  *)

subsection{* The algebra associated to dd0 *}

definition "eval0 \<equiv> dtor_unfold_J (dd0 o \<Sigma>\<Sigma>0_map <id, dtor_J>)"

lemma eval0: "F_map eval0 o dd0 o \<Sigma>\<Sigma>0_map <id, dtor_J> = dtor_J o eval0"
  unfolding eval0_def dtor_unfold_J_pointfree unfolding o_assoc ..

lemma eval0_ctor_J: "ctor_J o F_map eval0 o dd0 o \<Sigma>\<Sigma>0_map <id, dtor_J> = eval0"
  unfolding o_def spec[OF eval0[unfolded o_def fun_eq_iff]] J.ctor_dtor ..

lemma eval0_leaf0: "eval0 \<circ> leaf0 = id"
proof (rule trans)
  show "eval0 \<circ> leaf0 = dtor_unfold_J dtor_J"
  apply(rule J.dtor_unfold_unique)
  unfolding o_assoc eval0[symmetric] unfolding o_assoc[symmetric] leaf0_natural
  apply(rule sym)
  unfolding F_map_comp o_assoc apply (subst o_assoc[symmetric])
  unfolding dd0_leaf0 unfolding o_assoc[symmetric] by simp
qed(metis F_map_id J.dtor_unfold_unique fun.map_id o_id)

lemma eval0_flat0: "eval0 \<circ> flat0 = eval0 \<circ> \<Sigma>\<Sigma>0_map eval0" term "eval0 o flat0"
proof (rule trans)
  let ?K = "dtor_unfold_J (dd0 o \<Sigma>\<Sigma>0_map <\<Sigma>\<Sigma>0_map fst, dd0> o \<Sigma>\<Sigma>0_map (\<Sigma>\<Sigma>0_map <id, dtor_J>))"
  show "eval0 \<circ> flat0 = ?K"
  apply(rule J.dtor_unfold_unique)
  unfolding F_map_comp o_assoc
  apply(subst o_assoc[symmetric], subst o_assoc[symmetric])
  unfolding dd0_flat0
  unfolding o_assoc[symmetric] \<Sigma>\<Sigma>0.map_comp[symmetric] snd_convol
  unfolding flat0_natural
  unfolding o_assoc eval0 ..
  (*  *)
  have A: "<eval0, dtor_J o eval0> = <id,dtor_J> o eval0" by simp
  show "?K = eval0 \<circ> \<Sigma>\<Sigma>0_map eval0"
  apply(rule J.dtor_unfold_unique[symmetric])
  unfolding o_assoc[symmetric] map_prod_o_convol id_o
  unfolding F_map_comp o_assoc
  apply(subst o_assoc[symmetric]) unfolding dd0_natural[symmetric]
  unfolding o_assoc[symmetric] \<Sigma>\<Sigma>0.map_comp0[symmetric]
  unfolding o_assoc unfolding map_prod_o_convol unfolding convol_o
  unfolding o_assoc[symmetric] \<Sigma>\<Sigma>0.map_comp0[symmetric] fst_convol \<Sigma>\<Sigma>0.map_id0 o_id
  unfolding o_assoc eval0 unfolding A unfolding convol_o id_o
  apply(rule sym) apply(subst eval0[symmetric])
  unfolding o_assoc[symmetric] \<Sigma>\<Sigma>0.map_comp0[symmetric] convol_o id_o ..
qed


subsection{* The correspondence between coalgebras up to and coalgebras *}

(* This correspondence, and add0 the lemmas of this subsection, make
sense not only for (J,dtor_J,eval0), but also for any dd0-bialgebra *)

(* Coalgebra-up-to to coalgebra and vice versa: *)
definition cut\<Sigma>\<Sigma>0Oc :: "('a \<Rightarrow> 'a \<Sigma>\<Sigma>0 F) \<Rightarrow> ('a \<Sigma>\<Sigma>0 \<Rightarrow> 'a \<Sigma>\<Sigma>0 F)"
where "cut\<Sigma>\<Sigma>0Oc s \<equiv> F_map flat0 o dd0 o \<Sigma>\<Sigma>0_map <leaf0, s>"
definition c\<Sigma>\<Sigma>0Ocut :: "('a \<Sigma>\<Sigma>0 \<Rightarrow> 'a \<Sigma>\<Sigma>0 F) \<Rightarrow> ('a \<Rightarrow> 'a \<Sigma>\<Sigma>0 F)"
where "c\<Sigma>\<Sigma>0Ocut s' \<equiv> s' o leaf0"

lemma c\<Sigma>\<Sigma>0Ocut_cut\<Sigma>\<Sigma>0Oc: "c\<Sigma>\<Sigma>0Ocut (cut\<Sigma>\<Sigma>0Oc s) = s"
unfolding c\<Sigma>\<Sigma>0Ocut_def cut\<Sigma>\<Sigma>0Oc_def
unfolding o_assoc[symmetric] unfolding leaf0_natural
unfolding o_assoc apply(subst o_assoc[symmetric])
unfolding dd0_leaf0 unfolding o_assoc F_map_comp[symmetric] flat0_leaf0
unfolding F_map_id id_o by simp

lemma cut\<Sigma>\<Sigma>0Oc_inj: "cut\<Sigma>\<Sigma>0Oc s1 = cut\<Sigma>\<Sigma>0Oc s2 \<longleftrightarrow> s1 = s2"
by (metis c\<Sigma>\<Sigma>0Ocut_cut\<Sigma>\<Sigma>0Oc)

lemma c\<Sigma>\<Sigma>0Ocut_surj: "\<exists> s'. c\<Sigma>\<Sigma>0Ocut s' = s"
using c\<Sigma>\<Sigma>0Ocut_cut\<Sigma>\<Sigma>0Oc by(rule exI[of _ "cut\<Sigma>\<Sigma>0Oc s"])

(* Morphism-up-to to morphism and vice versa: *)
(* The dd0-ext0ension of a function *)
definition extdd0 :: "('a \<Rightarrow> J) \<Rightarrow> ('a \<Sigma>\<Sigma>0 \<Rightarrow> J)"
where "extdd0 f \<equiv> eval0 o \<Sigma>\<Sigma>0_map f"
(* The restriction of a function *)  term eval0
definition restr :: "('a \<Sigma>\<Sigma>0 \<Rightarrow> J) \<Rightarrow> ('a \<Rightarrow> J)"
where "restr f' \<equiv> f' o leaf0"

(* We think of extdd0 and restr as operating
extdd0 : Hom_dd0(s,dtor_J) \<rightarrow> Hom(cut\<Sigma>\<Sigma>0Oc s,dtor_J) and
restr : Hom(cut\<Sigma>\<Sigma>0Oc s,dtor_J) \<rightarrow> Hom_dd0(s,dtor_J), where
Hom(cut\<Sigma>\<Sigma>0Oc s,dtor_J) is the set of coalgebra morphisms betwee cut\<Sigma>\<Sigma>0Oc s and dtor_J and
Hom_dd0(s,dtor_J) is the set of coalgebra up-to-dd0-morphisms between s and dtor_J  *)

(* extdd0 is wedd0-defined: *)
lemma extdd0_mor:
assumes f:  "F_map (extdd0 f) o s = dtor_J o f"
shows "F_map (extdd0 f) o cut\<Sigma>\<Sigma>0Oc s = dtor_J o (extdd0 f)"
proof-
  have AA: "eval0 ** F_map eval0 \<circ> (\<Sigma>\<Sigma>0_map f ** F_map (\<Sigma>\<Sigma>0_map f) \<circ> <leaf0 , s>) =
            <f , F_map eval0 \<circ> (F_map (\<Sigma>\<Sigma>0_map f) \<circ> s)>"
  unfolding map_prod_o_convol unfolding leaf0_natural o_assoc eval0_leaf0 id_o  ..
  show ?thesis
  unfolding extdd0_def
  unfolding o_assoc eval0[symmetric]
  unfolding o_assoc[symmetric] \<Sigma>\<Sigma>0.map_comp0[symmetric]
  unfolding convol_comp[symmetric] id_o
  unfolding f[symmetric, unfolded extdd0_def]
  unfolding o_assoc
  apply(subst o_assoc[symmetric])
  unfolding F_map_comp o_assoc
  unfolding cut\<Sigma>\<Sigma>0Oc_def
  unfolding o_assoc
  unfolding F_map_comp[symmetric] unfolding o_assoc[symmetric]
  unfolding flat0_natural[symmetric]
  unfolding o_assoc F_map_comp
  apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
  unfolding dd0_natural[symmetric]
  unfolding o_assoc unfolding F_map_comp[symmetric] eval0_flat0
  unfolding F_map_comp apply(subst o_assoc[symmetric])
  unfolding dd0_natural[symmetric] unfolding o_assoc[symmetric] \<Sigma>\<Sigma>0.map_comp0[symmetric]
  unfolding o_assoc[symmetric] AA[unfolded o_assoc[symmetric]] ..
qed

lemma mor_cut\<Sigma>\<Sigma>0Oc_flat0:
assumes f': "F_map f' o cut\<Sigma>\<Sigma>0Oc s = dtor_J o f'"
shows "eval0 o \<Sigma>\<Sigma>0_map f' = f' o flat0"
proof(rule trans) (* this proof is clearly improvable: *)
  def h \<equiv> "dd0 o \<Sigma>\<Sigma>0_map <id,cut\<Sigma>\<Sigma>0Oc s>"
  have f'_id: "f' = f' o id" by simp
  show "eval0 \<circ> \<Sigma>\<Sigma>0_map f' = dtor_unfold_J h"
  apply(rule J.dtor_unfold_unique, rule sym)
  unfolding o_assoc eval0[symmetric]
  unfolding o_assoc[symmetric] \<Sigma>\<Sigma>0.map_comp0[symmetric]
  unfolding convol_comp_id1[symmetric] unfolding f'[symmetric]
  apply(subst f'_id)
  unfolding o_assoc \<Sigma>\<Sigma>0.map_comp
  apply(subst o_assoc[symmetric])
  unfolding o_assoc[symmetric] F_map_comp
  unfolding h_def apply(rule sym)
  unfolding o_assoc apply(subst o_assoc[symmetric])
  unfolding dd0_natural[symmetric] unfolding o_assoc[symmetric]
  unfolding \<Sigma>\<Sigma>0.map_comp0[symmetric] map_prod_o_convol ..
  (*  *)
  have AA: "<id , cut\<Sigma>\<Sigma>0Oc s> = (flat0 ** F_map flat0) o (id ** dd0) o <leaf0, \<Sigma>\<Sigma>0_map <leaf0 , s>>"
  unfolding map_prod_o_convol o_assoc map_prod.comp cut\<Sigma>\<Sigma>0Oc_def o_id flat0_leaf0 ..
  have BB: "flat0 ** F_map flat0 \<circ> id ** dd0 \<circ> <leaf0 , \<Sigma>\<Sigma>0_map <leaf0 , s>> = flat0 ** F_map flat0 \<circ> id ** dd0 \<circ> <\<Sigma>\<Sigma>0_map leaf0 , \<Sigma>\<Sigma>0_map <leaf0 , s>>"
  unfolding map_prod.comp unfolding map_prod_o_convol unfolding o_id unfolding flat0_leaf0 leaf0_flat0 ..
  show "dtor_unfold_J h = f' \<circ> flat0"
  apply(rule J.dtor_unfold_unique[symmetric], rule sym)
  unfolding o_assoc f'[symmetric]
  unfolding F_map_comp o_assoc[symmetric]
  apply(rule arg_cong[of _ _ "op o (F_map f')"])
  unfolding h_def
  unfolding AA BB
  unfolding \<Sigma>\<Sigma>0.map_comp0 apply(rule sym)
  unfolding o_assoc apply(subst o_assoc[symmetric])
  unfolding dd0_natural
  unfolding o_assoc F_map_comp[symmetric]
  unfolding flat0_assoc unfolding F_map_comp
  unfolding cut\<Sigma>\<Sigma>0Oc_def o_assoc[symmetric] apply(rule arg_cong[of _ _ "op o (F_map flat0)"])
  unfolding o_assoc
  unfolding o_assoc[symmetric] unfolding \<Sigma>\<Sigma>0.map_comp0[symmetric] unfolding map_prod_o_convol id_o
  unfolding flat0_natural[symmetric] unfolding o_assoc
  unfolding dd0_flat0[symmetric] unfolding o_assoc[symmetric] unfolding \<Sigma>\<Sigma>0.map_comp0[symmetric]
  unfolding convol_o unfolding \<Sigma>\<Sigma>0.map_comp0[symmetric] unfolding fst_convol ..
qed

(* restr is wedd0-defined:  *)
lemma restr_mor:
assumes f': "F_map f' o cut\<Sigma>\<Sigma>0Oc s = dtor_J o f'"
shows "F_map (extdd0 (restr f')) o s = dtor_J o restr f'"
unfolding extdd0_def restr_def \<Sigma>\<Sigma>0.map_comp0
unfolding o_assoc mor_cut\<Sigma>\<Sigma>0Oc_flat0[OF f']
unfolding o_assoc[symmetric] leaf0_flat0 o_id
unfolding o_assoc f'[symmetric]
unfolding o_assoc[symmetric] c\<Sigma>\<Sigma>0Ocut_cut\<Sigma>\<Sigma>0Oc[unfolded c\<Sigma>\<Sigma>0Ocut_def] ..

lemma extdd0_restr:
assumes f': "F_map f' o cut\<Sigma>\<Sigma>0Oc s = dtor_J o f'"
shows "extdd0 (restr f') = f'"
proof-
  have "f' = eval0 o \<Sigma>\<Sigma>0_map f' o leaf0"
  unfolding o_assoc[symmetric] leaf0_natural
  unfolding o_assoc eval0_leaf0 by simp
  also have "... = eval0 o \<Sigma>\<Sigma>0_map (f' o leaf0)"
  unfolding \<Sigma>\<Sigma>0.map_comp0 o_assoc
  unfolding mor_cut\<Sigma>\<Sigma>0Oc_flat0[OF f'] unfolding o_assoc[symmetric] flat0_leaf0 leaf0_flat0 ..
  finally have A: "f' = eval0 o \<Sigma>\<Sigma>0_map (f' o leaf0)" .
  show ?thesis unfolding extdd0_def restr_def A[symmetric] ..
qed

lemma restr_inj:
assumes f1': "F_map f1' o cut\<Sigma>\<Sigma>0Oc s = dtor_J o f1'"
and f2': "F_map f2' o cut\<Sigma>\<Sigma>0Oc s = dtor_J o f2'"
shows "restr f1' = restr f2' \<longleftrightarrow> f1' = f2'"
using extdd0_restr[OF f1'] extdd0_restr[OF f2'] by metis

lemma extdd0_surj:
assumes f': "F_map f' o cut\<Sigma>\<Sigma>0Oc s = dtor_J o f'"
shows "\<exists> f. extdd0 f = f'"
using extdd0_restr[OF f'] by(rule exI[of _ "restr f'"])

lemma restr_extdd0:
assumes f: "F_map (extdd0 f) o s = dtor_J o f"
shows "restr (extdd0 f) = f"
proof-
  have "dtor_J o f = F_map (extdd0 f) o s" using assms unfolding extdd0_def by (rule sym)
  also have "... = dtor_J o restr (extdd0 f)"
  unfolding restr_def unfolding o_assoc extdd0_mor[OF f, symmetric]
  unfolding o_assoc[symmetric] c\<Sigma>\<Sigma>0Ocut_cut\<Sigma>\<Sigma>0Oc[unfolded c\<Sigma>\<Sigma>0Ocut_def] ..
  finally have "dtor_J o f = dtor_J \<circ> restr (extdd0 f)" .
  thus ?thesis unfolding dtor_J_o_inj by (rule sym)
qed

lemma extdd0_inj:
assumes f1: "F_map (extdd0 f1) o s = dtor_J o f1"
and f2: "F_map (extdd0 f2) o s = dtor_J o f2"
shows "extdd0 f1 = extdd0 f2 \<longleftrightarrow> f1 = f2"
using restr_extdd0[OF f1] restr_extdd0[OF f2] by metis

lemma restr_surj:
assumes f: "F_map (extdd0 f) o s = dtor_J o f"
shows "\<exists> f'. restr f' = f"
using restr_extdd0[OF f] by(rule exI[of _ "extdd0 f"])


subsection{* Coiteration up-to *}

definition "unfoldU0 s \<equiv> restr (dtor_unfold_J (cut\<Sigma>\<Sigma>0Oc s))"

theorem unfoldU0_pointfree:
"F_map (extdd0 (unfoldU0 s)) o s = dtor_J o unfoldU0 s"
unfolding unfoldU0_def apply(rule restr_mor)
unfolding dtor_unfold_J_pointfree ..

theorem unfoldU0: "F_map (extdd0 (unfoldU0 s)) (s a) = dtor_J (unfoldU0 s a)"
using unfoldU0_pointfree unfolding o_def fun_eq_iff by(rule allE)

theorem unfoldU0_ctor_J:
"ctor_J (F_map (extdd0 (unfoldU0 s)) (s a)) = unfoldU0 s a"
using unfoldU0 by (metis J.ctor_dtor)

theorem unfoldU0_unique:
assumes "F_map (extdd0 f) o s = dtor_J o f"
shows "f = unfoldU0 s"
proof-
  note f = extdd0_mor[OF assms]  note co = extdd0_mor[OF unfoldU0_pointfree]
  have A: "extdd0 f = extdd0 (unfoldU0 s)"
  proof(rule trans)
    show "extdd0 f = dtor_unfold_J (cut\<Sigma>\<Sigma>0Oc s)" apply(rule J.dtor_unfold_unique) using f .
    show "dtor_unfold_J (cut\<Sigma>\<Sigma>0Oc s) = extdd0 (unfoldU0 s)"
     apply(rule J.dtor_unfold_unique[symmetric]) using co .
  qed
  show ?thesis using A unfolding extdd0_inj[OF assms unfoldU0_pointfree] .
qed

lemma unfoldU0_ctor_J_pointfree:
"ctor_J o F_map (extdd0 (unfoldU0 s)) o s = unfoldU0 s"
unfolding o_def fun_eq_iff by (subst unfoldU0_ctor_J[symmetric]) (rule allI, rule refl)

(* Corecursion up to: *)
definition corecU0 :: "('a \<Rightarrow> (J + 'a) \<Sigma>\<Sigma>0 F) \<Rightarrow> 'a \<Rightarrow> J" where
"corecU0 s = unfoldU0 (case_sum (dd0 o leaf0 o <Inl, F_map Inl o dtor_J>) s) o Inr"

definition extddRec0 where
"extddRec0 f \<equiv> eval0 \<circ> \<Sigma>\<Sigma>0_map (case_sum id f)"

lemma unfoldU0_Inl:
"unfoldU0 (case_sum (dd0 \<circ> leaf0 \<circ> <Inl , F_map Inl \<circ> dtor_J>) s) o Inl = id"
(is "?L = ?R")
proof-
  have "?L = unfoldU0 (dd0 o leaf0 o <id, dtor_J>)"
  apply(rule unfoldU0_unique)
  unfolding o_assoc unfoldU0_pointfree[symmetric]
  unfolding o_assoc[symmetric] case_sum_o_inj extdd0_def F_map_comp \<Sigma>\<Sigma>0.map_comp0
  unfolding o_assoc apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric],
                          subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
  unfolding dd0_natural[symmetric]
  apply(subst o_assoc[symmetric]) unfolding leaf0_natural
  unfolding o_assoc[symmetric] map_prod_o_convol o_id ..
  also have "... = ?R"
  apply(rule sym, rule unfoldU0_unique)
  unfolding extdd0_def \<Sigma>\<Sigma>0.map_id0 o_id dd0_leaf0
  unfolding o_assoc[symmetric] snd_convol
  unfolding o_assoc F_map_comp[symmetric] eval0_leaf0 F_map_id id_o ..
  finally show ?thesis .
qed

theorem corecU0_pointfree:
"F_map (extddRec0 (corecU0 s)) o s = dtor_J o corecU0 s" (is "?L = ?R")
unfolding corecU0_def
unfolding o_assoc unfoldU0_pointfree[symmetric] extddRec0_def
unfolding o_assoc[symmetric] case_sum_o_inj
apply(subst unfoldU0_Inl[symmetric, of s])
unfolding o_assoc case_sum_Inl_Inr_L extdd0_def ..

theorem corecU0:
"F_map (extddRec0 (corecU0 s)) (s a) = dtor_J (corecU0 s a)"
using corecU0_pointfree unfolding o_def fun_eq_iff by(rule allE)


subsection{* Coinduction up-to *}

definition "cptdd0 R \<equiv> (\<Sigma>\<Sigma>0_rel R ===> R) eval0 eval0"

definition "cngdd0 R \<equiv> equivp R \<and> cptdd0 R"

lemma cngdd0_Retr: "cngdd0 R \<Longrightarrow> cngdd0 (R \<sqinter> Retr R)"
  unfolding cngdd0_def cptdd0_def
  apply (erule conjE)
  apply (rule conjI[OF equivp_inf[OF _ equivp_retr]])
  apply assumption
  apply assumption
  apply (rule rel_funI)
  apply (frule predicate2D[OF \<Sigma>\<Sigma>0_rel_inf])
  apply (erule inf2E)
  apply (rule inf2I)
  apply (erule rel_funE)
  apply assumption
  apply assumption
  apply (subst Retr_def)
  apply (subst eval0_def)+
  apply (subst J.dtor_unfold)+
  unfolding F_rel_F_map_F_map Grp_def relcompp.simps[abs_def] conversep.simps[abs_def]
  apply auto
  unfolding eval0_def[symmetric]
  apply (rule predicate2D[OF F_rel_mono])
  apply (rule predicate2I)
  apply (erule rel_funD)
  apply assumption
  apply (rule F_rel_\<Sigma>\<Sigma>0_rel)
  unfolding \<Sigma>\<Sigma>0_rel_\<Sigma>\<Sigma>0_map_\<Sigma>\<Sigma>0_map vimage2p_rel_prod vimage2p_id
  unfolding vimage2p_def Retr_def[symmetric]
  apply assumption
  done

(* The generated congruence: *)
definition "genCngdd0 R j1 j2 \<equiv> \<forall> R'. R \<le> R' \<and> cngdd0 R' \<longrightarrow> R' j1 j2"

lemma cngdd0_genCngdd0: "cngdd0 (genCngdd0 R)"
unfolding cngdd0_def proof safe
  show "cptdd0 (genCngdd0 R)"
  unfolding cptdd0_def rel_fun_def proof safe
    fix x y assume 1: "\<Sigma>\<Sigma>0_rel (genCngdd0 R) x y"
    show "genCngdd0 R (eval0 x) (eval0 y)"
    unfolding genCngdd0_def[abs_def] proof safe
      fix R' assume "R \<le> R'" and 2: "cngdd0 R'"
      hence "\<Sigma>\<Sigma>0_rel R' x y" by (metis 1 \<Sigma>\<Sigma>0.rel_mono_strong genCngdd0_def)
      thus "R' (eval0 x) (eval0 y)" using 2 unfolding cngdd0_def cptdd0_def rel_fun_def by auto
    qed
  qed
qed(rule equivpI, unfold reflp_def symp_def transp_def genCngdd0_def cngdd0_def equivp_def, auto)

lemma
    genCngdd0_refl[intro,simp]: "genCngdd0 R j j"
and genCngdd0_sym[intro]: "genCngdd0 R j1 j2 \<Longrightarrow> genCngdd0 R j2 j1"
and genCngdd0_trans[intro]: "\<lbrakk>genCngdd0 R j1 j2; genCngdd0 R j2 j3\<rbrakk> \<Longrightarrow> genCngdd0 R j1 j3"
using cngdd0_genCngdd0 unfolding cngdd0_def equivp_def by auto

lemma genCngdd0_eval0_rel_fun: "(\<Sigma>\<Sigma>0_rel (genCngdd0 R) ===> genCngdd0 R) eval0 eval0"
using cngdd0_genCngdd0 unfolding cngdd0_def cptdd0_def by auto

lemma genCngdd0_eval0: "\<Sigma>\<Sigma>0_rel (genCngdd0 R) x y \<Longrightarrow> genCngdd0 R (eval0 x) (eval0 y)"
using genCngdd0_eval0_rel_fun unfolding rel_fun_def by auto

lemma leq_genCngdd0: "R \<le> genCngdd0 R"
and imp_genCngdd0[intro]: "R j1 j2 \<Longrightarrow> genCngdd0 R j1 j2"
unfolding genCngdd0_def[abs_def] by auto

lemma genCngdd0_minimal: "\<lbrakk>R \<le> R'; cngdd0 R'\<rbrakk> \<Longrightarrow> genCngdd0 R \<le> R'"
unfolding genCngdd0_def[abs_def] by (metis (lifting, no_types) predicate2I)

theorem coinductionU_genCngdd0:
assumes "\<forall> a b. R a b \<longrightarrow> F_rel (genCngdd0 R) (dtor_J a) (dtor_J b)"
shows "R a b \<longrightarrow> a = b"
proof-
  let ?R' = "genCngdd0 R"
  have "R \<le> Retr ?R'" using assms unfolding Retr_def[abs_def] by auto
  hence "R \<le> ?R' \<sqinter> Retr ?R'" using leq_genCngdd0 by auto
  moreover have "cngdd0 (?R' \<sqinter> Retr ?R')" using cngdd0_Retr[OF cngdd0_genCngdd0[of R]] .
  ultimately have "?R' \<le> ?R' \<sqinter> Retr ?R'" using genCngdd0_minimal by metis
  hence "?R' \<le> Retr ?R'" by auto
  hence "?R' a b \<longrightarrow> a = b" unfolding Retr_def[abs_def] by (intro J.dtor_coinduct) auto
  thus ?thesis using leq_genCngdd0 by auto
qed

(* Since (J \<Sigma>\<Sigma>0, eval0) is an Eilenberg-Moore algebra (i.e., is compatible with
the monadic structure, it yields an algebra on the signature functor.
This is crucial for having suitable simplification rules. *)
definition alg\<Lambda>0 :: "J \<Sigma>0 \<Rightarrow> J" where
"alg\<Lambda>0 = eval0 o \<oo>\<pp>0 o \<Sigma>0_map leaf0"

theorem eval0_comp_\<oo>\<pp>0: "eval0 o \<oo>\<pp>0 = alg\<Lambda>0 o \<Sigma>0_map eval0"
unfolding alg\<Lambda>0_def
unfolding o_assoc[symmetric] \<Sigma>0.map_comp0[symmetric]
unfolding leaf0_natural[symmetric] unfolding \<Sigma>0.map_comp0
apply(rule sym) unfolding o_assoc apply(subst o_assoc[symmetric])
unfolding \<oo>\<pp>0_natural
unfolding o_assoc eval0_flat0[symmetric]
apply(subst o_assoc[symmetric]) unfolding flat0_commute[symmetric]
unfolding o_assoc[symmetric] \<Sigma>0.map_comp0[symmetric] flat0_leaf0 \<Sigma>0.map_id0 o_id ..

theorem eval0_\<oo>\<pp>0: "eval0 (\<oo>\<pp>0 t) = alg\<Lambda>0 (\<Sigma>0_map eval0 t)"
using eval0_comp_\<oo>\<pp>0 unfolding o_def fun_eq_iff by (rule allE)

theorem eval0_leaf0': "eval0 (leaf0 j) = j"
using eval0_leaf0 unfolding o_def fun_eq_iff id_def by (rule allE)

theorem dtor_J_alg\<Lambda>0: "dtor_J o alg\<Lambda>0 = F_map eval0 o \<Lambda>0 o \<Sigma>0_map <id, dtor_J>"
  unfolding alg\<Lambda>0_def eval0_def o_assoc dtor_unfold_J_pointfree \<Lambda>0_dd0
  unfolding o_assoc[symmetric] \<oo>\<pp>0_natural[symmetric] \<Sigma>0.map_comp0[symmetric] leaf0_natural
  ..

theorem dtor_J_alg\<Lambda>0': "dtor_J (alg\<Lambda>0 t) = F_map eval0 (\<Lambda>0 (\<Sigma>0_map (<id, dtor_J>) t))"
  by (rule trans[OF o_eq_dest[OF dtor_J_alg\<Lambda>0] o_apply])

theorem ctor_J_alg\<Lambda>0: "alg\<Lambda>0 t = ctor_J (F_map eval0 (\<Lambda>0 (\<Sigma>0_map (<id, dtor_J>) t)))"
  by (rule iffD1[OF J.dtor_inject trans[OF dtor_J_alg\<Lambda>0' J.dtor_ctor[symmetric]]])

(* Customizing coinduction up-to: *)
definition "cpt\<Lambda>0 R \<equiv> (\<Sigma>0_rel R ===> R) alg\<Lambda>0 alg\<Lambda>0"

definition "cng\<Lambda>0 R \<equiv> equivp R \<and> cpt\<Lambda>0 R"

lemma cptdd0_iff_cpt\<Lambda>0: "cptdd0 R \<longleftrightarrow> cpt\<Lambda>0 R"
apply (rule iffI)
apply (unfold cpt\<Lambda>0_def cptdd0_def alg\<Lambda>0_def o_assoc[symmetric]) [1]
apply (erule rel_funD[OF rel_funD[OF comp_transfer]])
apply transfer_prover

apply (unfold cpt\<Lambda>0_def cptdd0_def) [1]
unfolding rel_fun_def
apply (rule allI)+
apply (rule \<Sigma>\<Sigma>0_rel_induct)
apply (simp only: eval0_leaf0')
unfolding eval0_\<oo>\<pp>0
apply (drule spec2)
apply (erule mp)
apply (rule iffD2[OF \<Sigma>0_rel_\<Sigma>0_map_\<Sigma>0_map])
apply (subst vimage2p_def)
apply assumption
done

(* This is the definition of genCngdd we need to work with: *)
theorem genCngdd0_def2: "genCngdd0 R j1 j2 \<longleftrightarrow> (\<forall> R'. R \<le> R' \<and> cng\<Lambda>0 R' \<longrightarrow> R' j1 j2)"
unfolding genCngdd0_def cngdd0_def cng\<Lambda>0_def cptdd0_iff_cpt\<Lambda>0 ..


subsection {* Incremental coinduction *}

interpretation I0: Incremental where Retr = Retr and Cl = genCngdd0
proof
  show "mono Retr" by (rule mono_retr)
next
  show "mono genCngdd0" unfolding mono_def
  unfolding genCngdd0_def[abs_def] by (smt order.trans predicate2I)
next
  fix r show "genCngdd0 (genCngdd0 r) = genCngdd0 r"
  by (metis cngdd0_genCngdd0 genCngdd0_minimal leq_genCngdd0 order_class.order.antisym)
next
  fix r show "r \<le> genCngdd0 r" by (metis leq_genCngdd0)
next
  fix r assume "genCngdd0 r = r" thus "genCngdd0 (r \<sqinter> Retr r) = r \<sqinter> Retr r"
  by (metis antisym cngdd0_Retr cngdd0_genCngdd0 genCngdd0_minimal
            inf.orderI inf_idem leq_genCngdd0)
qed

definition ded0 where "ded0 r s \<equiv> I0.ded r s"

theorems Ax = I0.Ax'[unfolded ded0_def[symmetric]]
theorems Split = I0.Split[unfolded ded0_def[symmetric]]
theorems Coind = I0.Coind[unfolded ded0_def[symmetric]]

theorem soundness_ded:
assumes "ded0 (op =) s"  shows "s \<le> (op =)"
unfolding gfp_Retr_eq[symmetric] apply(rule I0.soundness_ded[unfolded ded0_def[symmetric]] )
using assms unfolding gfp_Retr_eq[symmetric] ded0_def .

unused_thms

end
