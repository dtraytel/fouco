header {* Corecursion and coinduction up to *}

theory Stream_Corec_Upto8
imports Stream_Lift_to_Free8
begin


subsection{* The algebra associated to dd8 *}

definition "eval8 \<equiv> dtor_unfold_J (dd8 o \<Sigma>\<Sigma>8_map <id, dtor_J>)"

lemma eval8: "F_map eval8 o dd8 o \<Sigma>\<Sigma>8_map <id, dtor_J> = dtor_J o eval8"
  unfolding eval8_def dtor_unfold_J_pointfree unfolding o_assoc ..

lemma eval8_ctor_J: "ctor_J o F_map eval8 o dd8 o \<Sigma>\<Sigma>8_map <id, dtor_J> = eval8"
  unfolding o_def spec[OF eval8[unfolded o_def fun_eq_iff]] J.ctor_dtor ..

lemma eval8_leaf8: "eval8 \<circ> leaf8 = id"
proof (rule trans)
  show "eval8 \<circ> leaf8 = dtor_unfold_J dtor_J"
  apply(rule J.dtor_unfold_unique)
  unfolding o_assoc eval8[symmetric] unfolding o_assoc[symmetric] leaf8_natural
  apply(rule sym)
  unfolding F_map_comp o_assoc apply (subst o_assoc[symmetric])
  unfolding dd8_leaf8 unfolding o_assoc[symmetric] by simp
qed(metis F_map_id J.dtor_unfold_unique fun.map_id o_id)

lemma eval8_flat8: "eval8 \<circ> flat8 = eval8 \<circ> \<Sigma>\<Sigma>8_map eval8"
proof (rule trans)
  let ?K8 = "dtor_unfold_J (dd8 o \<Sigma>\<Sigma>8_map <\<Sigma>\<Sigma>8_map fst, dd8> o \<Sigma>\<Sigma>8_map (\<Sigma>\<Sigma>8_map <id, dtor_J>))"
  show "eval8 \<circ> flat8 = ?K8"
  apply(rule J.dtor_unfold_unique)
  unfolding F_map_comp o_assoc
  apply(subst o_assoc[symmetric], subst o_assoc[symmetric])
  unfolding dd8_flat8
  unfolding o_assoc[symmetric] \<Sigma>\<Sigma>8.map_comp0[symmetric] snd_convol
  unfolding flat8_natural
  unfolding o_assoc eval8 ..
  (*  *)
  have A: "<eval8, dtor_J o eval8> = <id,dtor_J> o eval8" by simp
  show "?K8 = eval8 \<circ> \<Sigma>\<Sigma>8_map eval8"
  apply(rule J.dtor_unfold_unique[symmetric])
  unfolding o_assoc[symmetric] \<Sigma>\<Sigma>8.map_comp0[symmetric] map_prod_o_convol id_o
  unfolding F_map_comp o_assoc
  apply(subst o_assoc[symmetric]) unfolding dd8_natural[symmetric]
  unfolding o_assoc[symmetric] \<Sigma>\<Sigma>8.map_comp0[symmetric]
  unfolding o_assoc unfolding map_prod_o_convol unfolding convol_o
  unfolding o_assoc[symmetric] \<Sigma>\<Sigma>8.map_comp0[symmetric] fst_convol \<Sigma>\<Sigma>8.map_id0 o_id
  unfolding o_assoc eval8 unfolding A unfolding convol_o id_o
  apply(rule sym) apply(subst eval8[symmetric])
  unfolding o_assoc[symmetric] \<Sigma>\<Sigma>8.map_comp0[symmetric] convol_o id_o ..
qed


subsection{* The correspondence between coalgebras up to and coalgebras *}

(* This correspondence, and add8 the lemmas of this subsection, make
sense not only for (J,dtor_J,eval8), but also for any dd8-bialgebra *)

(* Coalgebra-up-to to coalgebra and vice versa: *)
definition cut\<Sigma>\<Sigma>8Oc :: "('a \<Rightarrow> 'a \<Sigma>\<Sigma>8 F) \<Rightarrow> ('a \<Sigma>\<Sigma>8 \<Rightarrow> 'a \<Sigma>\<Sigma>8 F)"
where "cut\<Sigma>\<Sigma>8Oc s \<equiv> F_map flat8 o dd8 o \<Sigma>\<Sigma>8_map <leaf8, s>"
definition c\<Sigma>\<Sigma>8Ocut :: "('a \<Sigma>\<Sigma>8 \<Rightarrow> 'a \<Sigma>\<Sigma>8 F) \<Rightarrow> ('a \<Rightarrow> 'a \<Sigma>\<Sigma>8 F)"
where "c\<Sigma>\<Sigma>8Ocut s' \<equiv> s' o leaf8"

lemma c\<Sigma>\<Sigma>8Ocut_cut\<Sigma>\<Sigma>8Oc: "c\<Sigma>\<Sigma>8Ocut (cut\<Sigma>\<Sigma>8Oc s) = s"
unfolding c\<Sigma>\<Sigma>8Ocut_def cut\<Sigma>\<Sigma>8Oc_def
unfolding o_assoc[symmetric] unfolding leaf8_natural
unfolding o_assoc apply(subst o_assoc[symmetric])
unfolding dd8_leaf8 unfolding o_assoc F_map_comp[symmetric] flat8_leaf8
unfolding F_map_id id_o by simp

lemma cut\<Sigma>\<Sigma>8Oc_inj: "cut\<Sigma>\<Sigma>8Oc s8 = cut\<Sigma>\<Sigma>8Oc s2 \<longleftrightarrow> s8 = s2"
by (metis c\<Sigma>\<Sigma>8Ocut_cut\<Sigma>\<Sigma>8Oc)

lemma c\<Sigma>\<Sigma>8Ocut_surj: "\<exists> s'. c\<Sigma>\<Sigma>8Ocut s' = s"
using c\<Sigma>\<Sigma>8Ocut_cut\<Sigma>\<Sigma>8Oc by(rule exI[of _ "cut\<Sigma>\<Sigma>8Oc s"])

(* Morphism-up-to to morphism and vice versa: *)
(* The dd8-extension of a function *)
definition extdd8 :: "('a \<Rightarrow> J) \<Rightarrow> ('a \<Sigma>\<Sigma>8 \<Rightarrow> J)"
where "extdd8 f \<equiv> eval8 o \<Sigma>\<Sigma>8_map f"
(* The restriction of a function *)  term eval8
definition restr :: "('a \<Sigma>\<Sigma>8 \<Rightarrow> J) \<Rightarrow> ('a \<Rightarrow> J)"
where "restr f' \<equiv> f' o leaf8"

(* We think of extdd8 and restr as operating
extdd8 : Hom_dd8(s,dtor_J) \<rightarrow> Hom(cut\<Sigma>\<Sigma>8Oc s,dtor_J) and
restr : Hom(cut\<Sigma>\<Sigma>8Oc s,dtor_J) \<rightarrow> Hom_dd8(s,dtor_J), where
Hom(cut\<Sigma>\<Sigma>8Oc s,dtor_J) is the set of coalgebra morphisms betwee cut\<Sigma>\<Sigma>8Oc s and dtor_J and
Hom_dd8(s,dtor_J) is the set of coalgebra up-to-dd8-morphisms between s and dtor_J  *)

(* extdd8 is wedd8-defined: *)
lemma extdd8_mor:
assumes f:  "F_map (extdd8 f) o s = dtor_J o f"
shows "F_map (extdd8 f) o cut\<Sigma>\<Sigma>8Oc s = dtor_J o (extdd8 f)"
proof-
  have AA: "eval8 ** F_map eval8 \<circ> (\<Sigma>\<Sigma>8_map f ** F_map (\<Sigma>\<Sigma>8_map f) \<circ> <leaf8 , s>) =
            <f , F_map eval8 \<circ> (F_map (\<Sigma>\<Sigma>8_map f) \<circ> s)>"
  unfolding map_prod_o_convol unfolding leaf8_natural o_assoc eval8_leaf8 id_o  ..
  show ?thesis
  unfolding extdd8_def
  unfolding o_assoc eval8[symmetric]
  unfolding o_assoc[symmetric] \<Sigma>\<Sigma>8.map_comp0[symmetric]
  unfolding convol_comp[symmetric] id_o
  unfolding f[symmetric, unfolded extdd8_def]
  unfolding o_assoc
  apply(subst o_assoc[symmetric])
  unfolding F_map_comp o_assoc
  unfolding cut\<Sigma>\<Sigma>8Oc_def
  unfolding o_assoc
  unfolding F_map_comp[symmetric] unfolding o_assoc[symmetric]
  unfolding flat8_natural[symmetric]
  unfolding o_assoc F_map_comp
  apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
  unfolding dd8_natural[symmetric]
  unfolding o_assoc unfolding F_map_comp[symmetric] eval8_flat8
  unfolding F_map_comp apply(subst o_assoc[symmetric])
  unfolding dd8_natural[symmetric] unfolding o_assoc[symmetric] \<Sigma>\<Sigma>8.map_comp0[symmetric]
  unfolding o_assoc[symmetric] AA[unfolded o_assoc[symmetric]] ..
qed

lemma mor_cut\<Sigma>\<Sigma>8Oc_flat8:
assumes f': "F_map f' o cut\<Sigma>\<Sigma>8Oc s = dtor_J o f'"
shows "eval8 o \<Sigma>\<Sigma>8_map f' = f' o flat8"
proof(rule trans) (* this proof is clearly improvable: *)
  def h \<equiv> "dd8 o \<Sigma>\<Sigma>8_map <id,cut\<Sigma>\<Sigma>8Oc s>"
  have f'_id: "f' = f' o id" by simp
  show "eval8 \<circ> \<Sigma>\<Sigma>8_map f' = dtor_unfold_J h"
  apply(rule J.dtor_unfold_unique, rule sym)
  unfolding o_assoc eval8[symmetric]
  unfolding o_assoc[symmetric] \<Sigma>\<Sigma>8.map_comp0[symmetric]
  unfolding convol_comp_id1[symmetric] unfolding f'[symmetric]
  apply(subst f'_id)
  unfolding o_assoc \<Sigma>\<Sigma>8.map_comp0
  apply(subst o_assoc[symmetric])
  unfolding o_assoc[symmetric] F_map_comp
  unfolding h_def apply(rule sym)
  unfolding o_assoc apply(subst o_assoc[symmetric])
  unfolding dd8_natural[symmetric] unfolding o_assoc[symmetric]
  unfolding \<Sigma>\<Sigma>8.map_comp0[symmetric] map_prod_o_convol ..
  (*  *)
  have AA: "<id , cut\<Sigma>\<Sigma>8Oc s> = (flat8 ** F_map flat8) o (id ** dd8) o <leaf8, \<Sigma>\<Sigma>8_map <leaf8 , s>>"
  unfolding map_prod_o_convol o_assoc map_prod.comp cut\<Sigma>\<Sigma>8Oc_def o_id flat8_leaf8 ..
  have BB: "flat8 ** F_map flat8 \<circ> id ** dd8 \<circ> <leaf8 , \<Sigma>\<Sigma>8_map <leaf8 , s>> = flat8 ** F_map flat8 \<circ> id ** dd8 \<circ> <\<Sigma>\<Sigma>8_map leaf8 , \<Sigma>\<Sigma>8_map <leaf8 , s>>"
  unfolding map_prod.comp unfolding map_prod_o_convol unfolding o_id unfolding flat8_leaf8 leaf8_flat8 ..
  show "dtor_unfold_J h = f' \<circ> flat8"
  apply(rule J.dtor_unfold_unique[symmetric], rule sym)
  unfolding o_assoc f'[symmetric]
  unfolding F_map_comp o_assoc[symmetric]
  apply(rule arg_cong[of _ _ "op o (F_map f')"])
  unfolding h_def
  unfolding AA BB
  unfolding \<Sigma>\<Sigma>8.map_comp0 apply(rule sym)
  unfolding o_assoc apply(subst o_assoc[symmetric])
  unfolding dd8_natural
  unfolding o_assoc F_map_comp[symmetric]
  unfolding flat8_assoc unfolding F_map_comp
  unfolding cut\<Sigma>\<Sigma>8Oc_def o_assoc[symmetric] apply(rule arg_cong[of _ _ "op o (F_map flat8)"])
  unfolding o_assoc
  unfolding o_assoc[symmetric] unfolding \<Sigma>\<Sigma>8.map_comp0[symmetric] unfolding map_prod_o_convol id_o
  unfolding flat8_natural[symmetric] unfolding o_assoc
  unfolding dd8_flat8[symmetric] unfolding o_assoc[symmetric] unfolding \<Sigma>\<Sigma>8.map_comp0[symmetric]
  unfolding convol_o unfolding \<Sigma>\<Sigma>8.map_comp0[symmetric] unfolding fst_convol ..
qed

(* restr is wedd8-defined:  *)
lemma restr_mor:
assumes f': "F_map f' o cut\<Sigma>\<Sigma>8Oc s = dtor_J o f'"
shows "F_map (extdd8 (restr f')) o s = dtor_J o restr f'"
unfolding extdd8_def restr_def \<Sigma>\<Sigma>8.map_comp0
unfolding o_assoc mor_cut\<Sigma>\<Sigma>8Oc_flat8[OF f']
unfolding o_assoc[symmetric] leaf8_flat8 o_id
unfolding o_assoc f'[symmetric]
unfolding o_assoc[symmetric] c\<Sigma>\<Sigma>8Ocut_cut\<Sigma>\<Sigma>8Oc[unfolded c\<Sigma>\<Sigma>8Ocut_def] ..

lemma extdd8_restr:
assumes f': "F_map f' o cut\<Sigma>\<Sigma>8Oc s = dtor_J o f'"
shows "extdd8 (restr f') = f'"
proof-
  have "f' = eval8 o \<Sigma>\<Sigma>8_map f' o leaf8"
  unfolding o_assoc[symmetric] leaf8_natural
  unfolding o_assoc eval8_leaf8 by simp
  also have "... = eval8 o \<Sigma>\<Sigma>8_map (f' o leaf8)"
  unfolding \<Sigma>\<Sigma>8.map_comp0 o_assoc
  unfolding mor_cut\<Sigma>\<Sigma>8Oc_flat8[OF f'] unfolding o_assoc[symmetric] flat8_leaf8 leaf8_flat8 ..
  finally have A: "f' = eval8 o \<Sigma>\<Sigma>8_map (f' o leaf8)" .
  show ?thesis unfolding extdd8_def restr_def A[symmetric] ..
qed

lemma restr_inj:
assumes f8': "F_map f8' o cut\<Sigma>\<Sigma>8Oc s = dtor_J o f8'"
and f2': "F_map f2' o cut\<Sigma>\<Sigma>8Oc s = dtor_J o f2'"
shows "restr f8' = restr f2' \<longleftrightarrow> f8' = f2'"
using extdd8_restr[OF f8'] extdd8_restr[OF f2'] by metis

lemma extdd8_surj:
assumes f': "F_map f' o cut\<Sigma>\<Sigma>8Oc s = dtor_J o f'"
shows "\<exists> f. extdd8 f = f'"
using extdd8_restr[OF f'] by(rule exI[of _ "restr f'"])

lemma restr_extdd8:
assumes f: "F_map (extdd8 f) o s = dtor_J o f"
shows "restr (extdd8 f) = f"
proof-
  have "dtor_J o f = F_map (extdd8 f) o s" using assms unfolding extdd8_def by (rule sym)
  also have "... = dtor_J o restr (extdd8 f)"
  unfolding restr_def unfolding o_assoc extdd8_mor[OF f, symmetric]
  unfolding o_assoc[symmetric] c\<Sigma>\<Sigma>8Ocut_cut\<Sigma>\<Sigma>8Oc[unfolded c\<Sigma>\<Sigma>8Ocut_def] ..
  finally have "dtor_J o f = dtor_J \<circ> restr (extdd8 f)" .
  thus ?thesis unfolding dtor_J_o_inj by (rule sym)
qed

lemma extdd8_inj:
assumes f1: "F_map (extdd8 f1) o s = dtor_J o f1"
and f2: "F_map (extdd8 f2) o s = dtor_J o f2"
shows "extdd8 f1 = extdd8 f2 \<longleftrightarrow> f1 = f2"
using restr_extdd8[OF f1] restr_extdd8[OF f2] by metis

lemma restr_surj:
assumes f: "F_map (extdd8 f) o s = dtor_J o f"
shows "\<exists> f'. restr f' = f"
using restr_extdd8[OF f] by(rule exI[of _ "extdd8 f"])


subsection{* Coiteration up-to *}

definition "unfoldU8 s \<equiv> restr (dtor_unfold_J (cut\<Sigma>\<Sigma>8Oc s))"

theorem unfoldU8_pointfree:
"F_map (extdd8 (unfoldU8 s)) o s = dtor_J o unfoldU8 s"
unfolding unfoldU8_def apply(rule restr_mor)
unfolding dtor_unfold_J_pointfree ..

theorem unfoldU8: "F_map (extdd8 (unfoldU8 s)) (s a) = dtor_J (unfoldU8 s a)"
using unfoldU8_pointfree unfolding o_def fun_eq_iff by(rule allE)

theorem unfoldU8_ctor_J:
"ctor_J (F_map (extdd8 (unfoldU8 s)) (s a)) = unfoldU8 s a"
using unfoldU8 by (metis J.ctor_dtor)

theorem unfoldU8_unique:
assumes "F_map (extdd8 f) o s = dtor_J o f"
shows "f = unfoldU8 s"
proof-
  note f = extdd8_mor[OF assms]  note co = extdd8_mor[OF unfoldU8_pointfree]
  have A: "extdd8 f = extdd8 (unfoldU8 s)"
  proof(rule trans)
    show "extdd8 f = dtor_unfold_J (cut\<Sigma>\<Sigma>8Oc s)" apply(rule J.dtor_unfold_unique) using f .
    show "dtor_unfold_J (cut\<Sigma>\<Sigma>8Oc s) = extdd8 (unfoldU8 s)"
     apply(rule J.dtor_unfold_unique[symmetric]) using co .
  qed
  show ?thesis using A unfolding extdd8_inj[OF assms unfoldU8_pointfree] .
qed

lemma unfoldU8_ctor_J_pointfree:
"ctor_J o F_map (extdd8 (unfoldU8 s)) o s = unfoldU8 s"
unfolding o_def fun_eq_iff by (subst unfoldU8_ctor_J[symmetric]) (rule allI, rule refl)

(* Corecursion up to: *)
definition corecU8 :: "('a \<Rightarrow> (J + 'a) \<Sigma>\<Sigma>8 F) \<Rightarrow> 'a \<Rightarrow> J" where
"corecU8 s = unfoldU8 (case_sum (dd8 o leaf8 o <Inl, F_map Inl o dtor_J>) s) o Inr"

definition extddRec8 where
"extddRec8 f \<equiv> eval8 \<circ> \<Sigma>\<Sigma>8_map (case_sum id f)"

lemma unfoldU8_Inl:
"unfoldU8 (case_sum (dd8 \<circ> leaf8 \<circ> <Inl , F_map Inl \<circ> dtor_J>) s) o Inl = id"
(is "?L = ?R")
proof-
  have "?L = unfoldU8 (dd8 o leaf8 o <id, dtor_J>)"
  apply(rule unfoldU8_unique)
  unfolding o_assoc unfoldU8_pointfree[symmetric]
  unfolding o_assoc[symmetric] case_sum_o_inj extdd8_def F_map_comp \<Sigma>\<Sigma>8.map_comp0
  unfolding o_assoc apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric],
                          subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
  unfolding dd8_natural[symmetric]
  apply(subst o_assoc[symmetric]) unfolding leaf8_natural
  unfolding o_assoc[symmetric] map_prod_o_convol o_id ..
  also have "... = ?R"
  apply(rule sym, rule unfoldU8_unique)
  unfolding extdd8_def \<Sigma>\<Sigma>8.map_id0 o_id dd8_leaf8
  unfolding o_assoc[symmetric] snd_convol
  unfolding o_assoc F_map_comp[symmetric] eval8_leaf8 F_map_id id_o ..
  finally show ?thesis .
qed

theorem corecU8_pointfree:
"F_map (extddRec8 (corecU8 s)) o s = dtor_J o corecU8 s" (is "?L = ?R")
unfolding corecU8_def
unfolding o_assoc unfoldU8_pointfree[symmetric] extddRec8_def
unfolding o_assoc[symmetric] case_sum_o_inj
apply(subst unfoldU8_Inl[symmetric, of s])
unfolding o_assoc case_sum_Inl_Inr_L extdd8_def ..

theorem corecU8:
"F_map (extddRec8 (corecU8 s)) (s a) = dtor_J (corecU8 s a)"
using corecU8_pointfree unfolding o_def fun_eq_iff by(rule allE)


subsection{* Coinduction up-to *}

definition "cptdd8 R \<equiv> (\<Sigma>\<Sigma>8_rel R ===> R) eval8 eval8"

definition "cngdd8 R \<equiv> equivp R \<and> cptdd8 R"

lemma cngdd8_Retr: "cngdd8 R \<Longrightarrow> cngdd8 (R \<sqinter> Retr R)"
  unfolding cngdd8_def cptdd8_def
  apply (erule conjE)
  apply (rule conjI[OF equivp_inf[OF _ equivp_retr]])
  apply assumption
  apply assumption
  apply (rule rel_funI)
  apply (frule predicate2D[OF \<Sigma>\<Sigma>8_rel_inf])
  apply (erule inf2E)
  apply (rule inf2I)
  apply (erule rel_funE)
  apply assumption
  apply assumption
  apply (subst Retr_def)
  apply (subst eval8_def)+
  apply (subst J.dtor_unfold)+
  unfolding F_rel_F_map_F_map Grp_def relcompp.simps[abs_def] conversep.simps[abs_def]
  apply auto
  unfolding eval8_def[symmetric]
  apply (rule predicate2D[OF F_rel_mono])
  apply (rule predicate2I)
  apply (erule rel_funD)
  apply assumption
  apply (rule F_rel_\<Sigma>\<Sigma>8_rel)
  unfolding \<Sigma>\<Sigma>8_rel_\<Sigma>\<Sigma>8_map_\<Sigma>\<Sigma>8_map vimage2p_rel_prod vimage2p_id
  unfolding vimage2p_def Retr_def[symmetric]
  apply assumption
  done

(* The generated congruence: *)
definition "genCngdd8 R j1 j2 \<equiv> \<forall> R'. R \<le> R' \<and> cngdd8 R' \<longrightarrow> R' j1 j2"

lemma cngdd8_genCngdd8: "cngdd8 (genCngdd8 R)"
unfolding cngdd8_def proof safe
  show "cptdd8 (genCngdd8 R)"
  unfolding cptdd8_def rel_fun_def proof safe
    fix x y assume A: "\<Sigma>\<Sigma>8_rel (genCngdd8 R) x y"
    show "genCngdd8 R (eval8 x) (eval8 y)"
    unfolding genCngdd8_def[abs_def] proof safe
      fix R' assume "R \<le> R'" and 2: "cngdd8 R'"
      hence "\<Sigma>\<Sigma>8_rel R' x y" by (metis A \<Sigma>\<Sigma>8.rel_mono_strong genCngdd8_def)
      thus "R' (eval8 x) (eval8 y)" using 2 unfolding cngdd8_def cptdd8_def rel_fun_def by auto
    qed
  qed
qed(rule equivpI, unfold reflp_def symp_def transp_def genCngdd8_def cngdd8_def equivp_def, auto)

lemma
    genCngdd8_refl[intro,simp]: "genCngdd8 R j j"
and genCngdd8_sym[intro]: "genCngdd8 R j1 j2 \<Longrightarrow> genCngdd8 R j2 j1"
and genCngdd8_trans[intro]: "\<lbrakk>genCngdd8 R j1 j2; genCngdd8 R j2 j3\<rbrakk> \<Longrightarrow> genCngdd8 R j1 j3"
using cngdd8_genCngdd8 unfolding cngdd8_def equivp_def by auto

lemma genCngdd8_eval8_rel_fun: "(\<Sigma>\<Sigma>8_rel (genCngdd8 R) ===> genCngdd8 R) eval8 eval8"
using cngdd8_genCngdd8 unfolding cngdd8_def cptdd8_def by auto

lemma genCngdd8_eval8: "\<Sigma>\<Sigma>8_rel (genCngdd8 R) x y \<Longrightarrow> genCngdd8 R (eval8 x) (eval8 y)"
using genCngdd8_eval8_rel_fun unfolding rel_fun_def by auto

lemma leq_genCngdd8: "R \<le> genCngdd8 R"
and imp_genCngdd8[intro]: "R j1 j2 \<Longrightarrow> genCngdd8 R j1 j2"
unfolding genCngdd8_def[abs_def] by auto

lemma genCngdd8_minimal: "\<lbrakk>R \<le> R'; cngdd8 R'\<rbrakk> \<Longrightarrow> genCngdd8 R \<le> R'"
unfolding genCngdd8_def[abs_def] by (metis (lifting, no_types) predicate2I)

theorem coinductionU_genCngdd8:
assumes "\<forall> a b. R a b \<longrightarrow> F_rel (genCngdd8 R) (dtor_J a) (dtor_J b)"
shows "R a b \<longrightarrow> a = b"
proof-
  let ?R' = "genCngdd8 R"
  have "R \<le> Retr ?R'" using assms unfolding Retr_def[abs_def] by auto
  hence "R \<le> ?R' \<sqinter> Retr ?R'" using leq_genCngdd8 by auto
  moreover have "cngdd8 (?R' \<sqinter> Retr ?R')" using cngdd8_Retr[OF cngdd8_genCngdd8[of R]] .
  ultimately have "?R' \<le> ?R' \<sqinter> Retr ?R'" using genCngdd8_minimal by metis
  hence "?R' \<le> Retr ?R'" by auto
  hence "?R' a b \<longrightarrow> a = b"  unfolding Retr_def[abs_def] by (intro J.dtor_coinduct) auto
  thus ?thesis using leq_genCngdd8 by auto
qed


subsection{* Flattening from term algebra to "one-step" algebra *}

(* Since (J \<Sigma>\<Sigma>8, eval8) is an Eilenberg-Moore algebra (i.e., is compatible with
the monadic structure, it yields an algebra on the signature functor.
This is crucial for having suitable simplification rules. *)

(* The one-step algebra (naturally associated to \<Lambda>8, not to dd8): *)
definition alg\<Lambda>8 :: "J \<Sigma>8 \<Rightarrow> J" where "alg\<Lambda>8 = eval8 o \<oo>\<pp>8 o \<Sigma>8_map leaf8"

theorem eval8_comp_\<oo>\<pp>8: "eval8 o \<oo>\<pp>8 = alg\<Lambda>8 o \<Sigma>8_map eval8"
unfolding alg\<Lambda>8_def
unfolding o_assoc[symmetric] \<Sigma>8.map_comp0[symmetric]
unfolding leaf8_natural[symmetric] unfolding \<Sigma>8.map_comp0
apply(rule sym) unfolding o_assoc apply(subst o_assoc[symmetric])
unfolding \<oo>\<pp>8_natural
unfolding o_assoc eval8_flat8[symmetric]
apply(subst o_assoc[symmetric]) unfolding flat8_commute[symmetric]
unfolding o_assoc[symmetric] \<Sigma>8.map_comp0[symmetric] flat8_leaf8 \<Sigma>8.map_id0 o_id ..

theorem eval8_\<oo>\<pp>8: "eval8 (\<oo>\<pp>8 t) = alg\<Lambda>8 (\<Sigma>8_map eval8 t)"
using eval8_comp_\<oo>\<pp>8 unfolding o_def fun_eq_iff by (rule allE)

theorem eval8_leaf8': "eval8 (leaf8 j) = j"
using eval8_leaf8 unfolding o_def fun_eq_iff id_def by (rule allE)

theorem dtor_J_alg\<Lambda>8: "dtor_J o alg\<Lambda>8 = F_map eval8 o \<Lambda>8 o \<Sigma>8_map <id, dtor_J>"
  unfolding alg\<Lambda>8_def eval8_def o_assoc dtor_unfold_J_pointfree \<Lambda>8_dd8
  unfolding o_assoc[symmetric] \<oo>\<pp>8_natural[symmetric] \<Sigma>8.map_comp0[symmetric] leaf8_natural
  ..

theorem dtor_J_alg\<Lambda>8': "dtor_J (alg\<Lambda>8 t) = F_map eval8 (\<Lambda>8 (\<Sigma>8_map (<id, dtor_J>) t))"
  by (rule trans[OF o_eq_dest[OF dtor_J_alg\<Lambda>8] o_apply])

theorem ctor_J_alg\<Lambda>8: "alg\<Lambda>8 t = ctor_J (F_map eval8 (\<Lambda>8 (\<Sigma>8_map (<id, dtor_J>) t)))"
  by (rule iffD1[OF J.dtor_inject trans[OF dtor_J_alg\<Lambda>8' J.dtor_ctor[symmetric]]])

(* Note: The user wi\<Lambda>8 indicate an "equation" equ :: J \<Sigma>8 \<Rightarrow> (J \<Sigma>\<Sigma>8) F
in order to define the operation alg\<Lambda>8 :: J \<Sigma>8 \<Rightarrow> J on the final coalgebra
according to dtor_J_alg\<Lambda>8.
The package wi\<Lambda>8 identify the polymorphic function \<Lambda>8 :: ('a \<times> 'a F) \<Sigma>8 \<Rightarrow> 'a \<Sigma>\<Sigma>8 F
such that equ = \<Lambda>8 o \<Sigma>8 <id, dtor_J>. Then the package wi\<Lambda>8 attempt to prove
automatica\<Lambda>8y that \<Lambda>8 is natural.  If the proof fails, the user wi\<Lambda>8 be asked to prove it.
Upon success, the distributive law is being registered.
*)

(* Customizing coinduction up-to: *)
definition "cpt\<Lambda>8 R \<equiv> (\<Sigma>8_rel R ===> R) alg\<Lambda>8 alg\<Lambda>8"

definition "cng\<Lambda>8 R \<equiv> equivp R \<and> cpt\<Lambda>8 R"

lemma cptdd8_iff_cpt\<Lambda>8: "cptdd8 R \<longleftrightarrow> cpt\<Lambda>8 R"
apply (rule iffI)
apply (unfold cpt\<Lambda>8_def cptdd8_def alg\<Lambda>8_def o_assoc[symmetric]) [1]
apply (erule rel_funD[OF rel_funD[OF comp_transfer]])
apply transfer_prover

apply (unfold cpt\<Lambda>8_def cptdd8_def) [1]
unfolding rel_fun_def
apply (rule allI)+
apply (rule \<Sigma>\<Sigma>8_rel_induct)
apply (simp only: eval8_leaf8')
unfolding eval8_\<oo>\<pp>8
apply (drule spec2)
apply (erule mp)
apply (rule iffD2[OF \<Sigma>8_rel_\<Sigma>8_map_\<Sigma>8_map])
apply (subst vimage2p_def)
apply assumption
done

(* This is the definition of genCngdd8 we need to work with: *)
theorem genCngdd8_def2: "genCngdd8 R j1 j2 \<longleftrightarrow> (\<forall> R'. R \<le> R' \<and> cng\<Lambda>8 R' \<longrightarrow> R' j1 j2)"
unfolding genCngdd8_def cngdd8_def cng\<Lambda>8_def cptdd8_iff_cpt\<Lambda>8 ..


subsection {* Incremental coinduction *}

interpretation I8: Incremental where Retr = Retr and Cl = genCngdd8
proof
  show "mono Retr" by (rule mono_retr)
next
  show "mono genCngdd8" unfolding mono_def
  unfolding genCngdd8_def[abs_def] by (smt order.trans predicate2I)
next
  fix r show "genCngdd8 (genCngdd8 r) = genCngdd8 r"
  by (metis cngdd8_genCngdd8 genCngdd8_minimal leq_genCngdd8 order_class.order.antisym)
next
  fix r show "r \<le> genCngdd8 r" by (metis leq_genCngdd8)
next
  fix r assume "genCngdd8 r = r" thus "genCngdd8 (r \<sqinter> Retr r) = r \<sqinter> Retr r"
  by (metis antisym cngdd8_Retr cngdd8_genCngdd8 genCngdd8_minimal
            inf.orderI inf_idem leq_genCngdd8)
qed

definition ded8 where "ded8 r s \<equiv> I8.ded r s"

theorems Ax = I8.Ax'[unfolded ded8_def[symmetric]]
theorems Split = I8.Split[unfolded ded8_def[symmetric]]
theorems Coind = I8.Coind[unfolded ded8_def[symmetric]]

theorem soundness_ded:
assumes "ded8 (op =) s"  shows "s \<le> (op =)"
unfolding gfp_Retr_eq[symmetric] apply(rule I8.soundness_ded[unfolded ded8_def[symmetric]] )
using assms unfolding gfp_Retr_eq[symmetric] ded8_def .

unused_thms

end
