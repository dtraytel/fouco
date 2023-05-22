header {* Corecursion and coinduction up to *}

theory Stream_Corec_Upto4
imports Stream_Lift_to_Free4
begin


subsection{* The algebra associated to dd4 *}

definition "eval4 \<equiv> dtor_unfold_J (dd4 o \<Sigma>\<Sigma>4_map <id, dtor_J>)"

lemma eval4: "F_map eval4 o dd4 o \<Sigma>\<Sigma>4_map <id, dtor_J> = dtor_J o eval4"
  unfolding eval4_def dtor_unfold_J_pointfree unfolding o_assoc ..

lemma eval4_ctor_J: "ctor_J o F_map eval4 o dd4 o \<Sigma>\<Sigma>4_map <id, dtor_J> = eval4"
  unfolding o_def spec[OF eval4[unfolded o_def fun_eq_iff]] J.ctor_dtor ..

lemma eval4_leaf4: "eval4 \<circ> leaf4 = id"
proof (rule trans)
  show "eval4 \<circ> leaf4 = dtor_unfold_J dtor_J"
  apply(rule J.dtor_unfold_unique)
  unfolding o_assoc eval4[symmetric] unfolding o_assoc[symmetric] leaf4_natural
  apply(rule sym)
  unfolding F_map_comp o_assoc apply (subst o_assoc[symmetric])
  unfolding dd4_leaf4 unfolding o_assoc[symmetric] by simp
qed(metis F_map_id J.dtor_unfold_unique fun.map_id o_id)

lemma eval4_flat4: "eval4 \<circ> flat4 = eval4 \<circ> \<Sigma>\<Sigma>4_map eval4"
proof (rule trans)
  let ?K4 = "dtor_unfold_J (dd4 o \<Sigma>\<Sigma>4_map <\<Sigma>\<Sigma>4_map fst, dd4> o \<Sigma>\<Sigma>4_map (\<Sigma>\<Sigma>4_map <id, dtor_J>))"
  show "eval4 \<circ> flat4 = ?K4"
  apply(rule J.dtor_unfold_unique)
  unfolding F_map_comp o_assoc
  apply(subst o_assoc[symmetric], subst o_assoc[symmetric])
  unfolding dd4_flat4
  unfolding o_assoc[symmetric] \<Sigma>\<Sigma>4.map_comp0[symmetric] snd_convol
  unfolding flat4_natural
  unfolding o_assoc eval4 ..
  (*  *)
  have A: "<eval4, dtor_J o eval4> = <id,dtor_J> o eval4" by simp
  show "?K4 = eval4 \<circ> \<Sigma>\<Sigma>4_map eval4"
  apply(rule J.dtor_unfold_unique[symmetric])
  unfolding o_assoc[symmetric] \<Sigma>\<Sigma>4.map_comp0[symmetric] map_prod_o_convol id_o
  unfolding F_map_comp o_assoc
  apply(subst o_assoc[symmetric]) unfolding dd4_natural[symmetric]
  unfolding o_assoc[symmetric] \<Sigma>\<Sigma>4.map_comp0[symmetric]
  unfolding o_assoc unfolding map_prod_o_convol unfolding convol_o
  unfolding o_assoc[symmetric] \<Sigma>\<Sigma>4.map_comp0[symmetric] fst_convol \<Sigma>\<Sigma>4.map_id0 o_id
  unfolding o_assoc eval4 unfolding A unfolding convol_o id_o
  apply(rule sym) apply(subst eval4[symmetric])
  unfolding o_assoc[symmetric] \<Sigma>\<Sigma>4.map_comp0[symmetric] convol_o id_o ..
qed


subsection{* The correspondence between coalgebras up to and coalgebras *}

(* This correspondence, and add4 the lemmas of this subsection, make
sense not only for (J,dtor_J,eval4), but also for any dd4-bialgebra *)

(* Coalgebra-up-to to coalgebra and vice versa: *)
definition cut\<Sigma>\<Sigma>4Oc :: "('a \<Rightarrow> 'a \<Sigma>\<Sigma>4 F) \<Rightarrow> ('a \<Sigma>\<Sigma>4 \<Rightarrow> 'a \<Sigma>\<Sigma>4 F)"
where "cut\<Sigma>\<Sigma>4Oc s \<equiv> F_map flat4 o dd4 o \<Sigma>\<Sigma>4_map <leaf4, s>"
definition c\<Sigma>\<Sigma>4Ocut :: "('a \<Sigma>\<Sigma>4 \<Rightarrow> 'a \<Sigma>\<Sigma>4 F) \<Rightarrow> ('a \<Rightarrow> 'a \<Sigma>\<Sigma>4 F)"
where "c\<Sigma>\<Sigma>4Ocut s' \<equiv> s' o leaf4"

lemma c\<Sigma>\<Sigma>4Ocut_cut\<Sigma>\<Sigma>4Oc: "c\<Sigma>\<Sigma>4Ocut (cut\<Sigma>\<Sigma>4Oc s) = s"
unfolding c\<Sigma>\<Sigma>4Ocut_def cut\<Sigma>\<Sigma>4Oc_def
unfolding o_assoc[symmetric] unfolding leaf4_natural
unfolding o_assoc apply(subst o_assoc[symmetric])
unfolding dd4_leaf4 unfolding o_assoc F_map_comp[symmetric] flat4_leaf4
unfolding F_map_id id_o by simp

lemma cut\<Sigma>\<Sigma>4Oc_inj: "cut\<Sigma>\<Sigma>4Oc s4 = cut\<Sigma>\<Sigma>4Oc s2 \<longleftrightarrow> s4 = s2"
by (metis c\<Sigma>\<Sigma>4Ocut_cut\<Sigma>\<Sigma>4Oc)

lemma c\<Sigma>\<Sigma>4Ocut_surj: "\<exists> s'. c\<Sigma>\<Sigma>4Ocut s' = s"
using c\<Sigma>\<Sigma>4Ocut_cut\<Sigma>\<Sigma>4Oc by(rule exI[of _ "cut\<Sigma>\<Sigma>4Oc s"])

(* Morphism-up-to to morphism and vice versa: *)
(* The dd4-extension of a function *)
definition extdd4 :: "('a \<Rightarrow> J) \<Rightarrow> ('a \<Sigma>\<Sigma>4 \<Rightarrow> J)"
where "extdd4 f \<equiv> eval4 o \<Sigma>\<Sigma>4_map f"
(* The restriction of a function *)  term eval4
definition restr :: "('a \<Sigma>\<Sigma>4 \<Rightarrow> J) \<Rightarrow> ('a \<Rightarrow> J)"
where "restr f' \<equiv> f' o leaf4"

(* We think of extdd4 and restr as operating
extdd4 : Hom_dd4(s,dtor_J) \<rightarrow> Hom(cut\<Sigma>\<Sigma>4Oc s,dtor_J) and
restr : Hom(cut\<Sigma>\<Sigma>4Oc s,dtor_J) \<rightarrow> Hom_dd4(s,dtor_J), where
Hom(cut\<Sigma>\<Sigma>4Oc s,dtor_J) is the set of coalgebra morphisms betwee cut\<Sigma>\<Sigma>4Oc s and dtor_J and
Hom_dd4(s,dtor_J) is the set of coalgebra up-to-dd4-morphisms between s and dtor_J  *)

(* extdd4 is wedd4-defined: *)
lemma extdd4_mor:
assumes f:  "F_map (extdd4 f) o s = dtor_J o f"
shows "F_map (extdd4 f) o cut\<Sigma>\<Sigma>4Oc s = dtor_J o (extdd4 f)"
proof-
  have AA: "eval4 ** F_map eval4 \<circ> (\<Sigma>\<Sigma>4_map f ** F_map (\<Sigma>\<Sigma>4_map f) \<circ> <leaf4 , s>) =
            <f , F_map eval4 \<circ> (F_map (\<Sigma>\<Sigma>4_map f) \<circ> s)>"
  unfolding map_prod_o_convol unfolding leaf4_natural o_assoc eval4_leaf4 id_o  ..
  show ?thesis
  unfolding extdd4_def
  unfolding o_assoc eval4[symmetric]
  unfolding o_assoc[symmetric] \<Sigma>\<Sigma>4.map_comp0[symmetric]
  unfolding convol_comp[symmetric] id_o
  unfolding f[symmetric, unfolded extdd4_def]
  unfolding o_assoc
  apply(subst o_assoc[symmetric])
  unfolding F_map_comp o_assoc
  unfolding cut\<Sigma>\<Sigma>4Oc_def
  unfolding o_assoc
  unfolding F_map_comp[symmetric] unfolding o_assoc[symmetric]
  unfolding flat4_natural[symmetric]
  unfolding o_assoc F_map_comp
  apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
  unfolding dd4_natural[symmetric]
  unfolding o_assoc unfolding F_map_comp[symmetric] eval4_flat4
  unfolding F_map_comp apply(subst o_assoc[symmetric])
  unfolding dd4_natural[symmetric] unfolding o_assoc[symmetric] \<Sigma>\<Sigma>4.map_comp0[symmetric]
  unfolding o_assoc[symmetric] AA[unfolded o_assoc[symmetric]] ..
qed

lemma mor_cut\<Sigma>\<Sigma>4Oc_flat4:
assumes f': "F_map f' o cut\<Sigma>\<Sigma>4Oc s = dtor_J o f'"
shows "eval4 o \<Sigma>\<Sigma>4_map f' = f' o flat4"
proof(rule trans) (* this proof is clearly improvable: *)
  def h \<equiv> "dd4 o \<Sigma>\<Sigma>4_map <id,cut\<Sigma>\<Sigma>4Oc s>"
  have f'_id: "f' = f' o id" by simp
  show "eval4 \<circ> \<Sigma>\<Sigma>4_map f' = dtor_unfold_J h"
  apply(rule J.dtor_unfold_unique, rule sym)
  unfolding o_assoc eval4[symmetric]
  unfolding o_assoc[symmetric] \<Sigma>\<Sigma>4.map_comp0[symmetric]
  unfolding convol_comp_id1[symmetric] unfolding f'[symmetric]
  apply(subst f'_id)
  unfolding o_assoc \<Sigma>\<Sigma>4.map_comp0
  apply(subst o_assoc[symmetric])
  unfolding o_assoc[symmetric] F_map_comp
  unfolding h_def apply(rule sym)
  unfolding o_assoc apply(subst o_assoc[symmetric])
  unfolding dd4_natural[symmetric] unfolding o_assoc[symmetric]
  unfolding \<Sigma>\<Sigma>4.map_comp0[symmetric] map_prod_o_convol ..
  (*  *)
  have AA: "<id , cut\<Sigma>\<Sigma>4Oc s> = (flat4 ** F_map flat4) o (id ** dd4) o <leaf4, \<Sigma>\<Sigma>4_map <leaf4 , s>>"
  unfolding map_prod_o_convol o_assoc map_prod.comp cut\<Sigma>\<Sigma>4Oc_def o_id flat4_leaf4 ..
  have BB: "flat4 ** F_map flat4 \<circ> id ** dd4 \<circ> <leaf4 , \<Sigma>\<Sigma>4_map <leaf4 , s>> = flat4 ** F_map flat4 \<circ> id ** dd4 \<circ> <\<Sigma>\<Sigma>4_map leaf4 , \<Sigma>\<Sigma>4_map <leaf4 , s>>"
  unfolding map_prod.comp unfolding map_prod_o_convol unfolding o_id unfolding flat4_leaf4 leaf4_flat4 ..
  show "dtor_unfold_J h = f' \<circ> flat4"
  apply(rule J.dtor_unfold_unique[symmetric], rule sym)
  unfolding o_assoc f'[symmetric]
  unfolding F_map_comp o_assoc[symmetric]
  apply(rule arg_cong[of _ _ "op o (F_map f')"])
  unfolding h_def
  unfolding AA BB
  unfolding \<Sigma>\<Sigma>4.map_comp0 apply(rule sym)
  unfolding o_assoc apply(subst o_assoc[symmetric])
  unfolding dd4_natural
  unfolding o_assoc F_map_comp[symmetric]
  unfolding flat4_assoc unfolding F_map_comp
  unfolding cut\<Sigma>\<Sigma>4Oc_def o_assoc[symmetric] apply(rule arg_cong[of _ _ "op o (F_map flat4)"])
  unfolding o_assoc
  unfolding o_assoc[symmetric] unfolding \<Sigma>\<Sigma>4.map_comp0[symmetric] unfolding map_prod_o_convol id_o
  unfolding flat4_natural[symmetric] unfolding o_assoc
  unfolding dd4_flat4[symmetric] unfolding o_assoc[symmetric] unfolding \<Sigma>\<Sigma>4.map_comp0[symmetric]
  unfolding convol_o unfolding \<Sigma>\<Sigma>4.map_comp0[symmetric] unfolding fst_convol ..
qed

(* restr is wedd4-defined:  *)
lemma restr_mor:
assumes f': "F_map f' o cut\<Sigma>\<Sigma>4Oc s = dtor_J o f'"
shows "F_map (extdd4 (restr f')) o s = dtor_J o restr f'"
unfolding extdd4_def restr_def \<Sigma>\<Sigma>4.map_comp0
unfolding o_assoc mor_cut\<Sigma>\<Sigma>4Oc_flat4[OF f']
unfolding o_assoc[symmetric] leaf4_flat4 o_id
unfolding o_assoc f'[symmetric]
unfolding o_assoc[symmetric] c\<Sigma>\<Sigma>4Ocut_cut\<Sigma>\<Sigma>4Oc[unfolded c\<Sigma>\<Sigma>4Ocut_def] ..

lemma extdd4_restr:
assumes f': "F_map f' o cut\<Sigma>\<Sigma>4Oc s = dtor_J o f'"
shows "extdd4 (restr f') = f'"
proof-
  have "f' = eval4 o \<Sigma>\<Sigma>4_map f' o leaf4"
  unfolding o_assoc[symmetric] leaf4_natural
  unfolding o_assoc eval4_leaf4 by simp
  also have "... = eval4 o \<Sigma>\<Sigma>4_map (f' o leaf4)"
  unfolding \<Sigma>\<Sigma>4.map_comp0 o_assoc
  unfolding mor_cut\<Sigma>\<Sigma>4Oc_flat4[OF f'] unfolding o_assoc[symmetric] flat4_leaf4 leaf4_flat4 ..
  finally have A: "f' = eval4 o \<Sigma>\<Sigma>4_map (f' o leaf4)" .
  show ?thesis unfolding extdd4_def restr_def A[symmetric] ..
qed

lemma restr_inj:
assumes f4': "F_map f4' o cut\<Sigma>\<Sigma>4Oc s = dtor_J o f4'"
and f2': "F_map f2' o cut\<Sigma>\<Sigma>4Oc s = dtor_J o f2'"
shows "restr f4' = restr f2' \<longleftrightarrow> f4' = f2'"
using extdd4_restr[OF f4'] extdd4_restr[OF f2'] by metis

lemma extdd4_surj:
assumes f': "F_map f' o cut\<Sigma>\<Sigma>4Oc s = dtor_J o f'"
shows "\<exists> f. extdd4 f = f'"
using extdd4_restr[OF f'] by(rule exI[of _ "restr f'"])

lemma restr_extdd4:
assumes f: "F_map (extdd4 f) o s = dtor_J o f"
shows "restr (extdd4 f) = f"
proof-
  have "dtor_J o f = F_map (extdd4 f) o s" using assms unfolding extdd4_def by (rule sym)
  also have "... = dtor_J o restr (extdd4 f)"
  unfolding restr_def unfolding o_assoc extdd4_mor[OF f, symmetric]
  unfolding o_assoc[symmetric] c\<Sigma>\<Sigma>4Ocut_cut\<Sigma>\<Sigma>4Oc[unfolded c\<Sigma>\<Sigma>4Ocut_def] ..
  finally have "dtor_J o f = dtor_J \<circ> restr (extdd4 f)" .
  thus ?thesis unfolding dtor_J_o_inj by (rule sym)
qed

lemma extdd4_inj:
assumes f1: "F_map (extdd4 f1) o s = dtor_J o f1"
and f2: "F_map (extdd4 f2) o s = dtor_J o f2"
shows "extdd4 f1 = extdd4 f2 \<longleftrightarrow> f1 = f2"
using restr_extdd4[OF f1] restr_extdd4[OF f2] by metis

lemma restr_surj:
assumes f: "F_map (extdd4 f) o s = dtor_J o f"
shows "\<exists> f'. restr f' = f"
using restr_extdd4[OF f] by(rule exI[of _ "extdd4 f"])


subsection{* Coiteration up-to *}

definition "unfoldU4 s \<equiv> restr (dtor_unfold_J (cut\<Sigma>\<Sigma>4Oc s))"

theorem unfoldU4_pointfree:
"F_map (extdd4 (unfoldU4 s)) o s = dtor_J o unfoldU4 s"
unfolding unfoldU4_def apply(rule restr_mor)
unfolding dtor_unfold_J_pointfree ..

theorem unfoldU4: "F_map (extdd4 (unfoldU4 s)) (s a) = dtor_J (unfoldU4 s a)"
using unfoldU4_pointfree unfolding o_def fun_eq_iff by(rule allE)

theorem unfoldU4_ctor_J:
"ctor_J (F_map (extdd4 (unfoldU4 s)) (s a)) = unfoldU4 s a"
using unfoldU4 by (metis J.ctor_dtor)

theorem unfoldU4_unique:
assumes "F_map (extdd4 f) o s = dtor_J o f"
shows "f = unfoldU4 s"
proof-
  note f = extdd4_mor[OF assms]  note co = extdd4_mor[OF unfoldU4_pointfree]
  have A: "extdd4 f = extdd4 (unfoldU4 s)"
  proof(rule trans)
    show "extdd4 f = dtor_unfold_J (cut\<Sigma>\<Sigma>4Oc s)" apply(rule J.dtor_unfold_unique) using f .
    show "dtor_unfold_J (cut\<Sigma>\<Sigma>4Oc s) = extdd4 (unfoldU4 s)"
     apply(rule J.dtor_unfold_unique[symmetric]) using co .
  qed
  show ?thesis using A unfolding extdd4_inj[OF assms unfoldU4_pointfree] .
qed

lemma unfoldU4_ctor_J_pointfree:
"ctor_J o F_map (extdd4 (unfoldU4 s)) o s = unfoldU4 s"
unfolding o_def fun_eq_iff by (subst unfoldU4_ctor_J[symmetric]) (rule allI, rule refl)

(* Corecursion up to: *)
definition corecU4 :: "('a \<Rightarrow> (J + 'a) \<Sigma>\<Sigma>4 F) \<Rightarrow> 'a \<Rightarrow> J" where
"corecU4 s = unfoldU4 (case_sum (dd4 o leaf4 o <Inl, F_map Inl o dtor_J>) s) o Inr"

definition extddRec4 where
"extddRec4 f \<equiv> eval4 \<circ> \<Sigma>\<Sigma>4_map (case_sum id f)"

lemma unfoldU4_Inl:
"unfoldU4 (case_sum (dd4 \<circ> leaf4 \<circ> <Inl , F_map Inl \<circ> dtor_J>) s) o Inl = id"
(is "?L = ?R")
proof-
  have "?L = unfoldU4 (dd4 o leaf4 o <id, dtor_J>)"
  apply(rule unfoldU4_unique)
  unfolding o_assoc unfoldU4_pointfree[symmetric]
  unfolding o_assoc[symmetric] case_sum_o_inj extdd4_def F_map_comp \<Sigma>\<Sigma>4.map_comp0
  unfolding o_assoc apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric],
                          subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
  unfolding dd4_natural[symmetric]
  apply(subst o_assoc[symmetric]) unfolding leaf4_natural
  unfolding o_assoc[symmetric] map_prod_o_convol o_id ..
  also have "... = ?R"
  apply(rule sym, rule unfoldU4_unique)
  unfolding extdd4_def \<Sigma>\<Sigma>4.map_id0 o_id dd4_leaf4
  unfolding o_assoc[symmetric] snd_convol
  unfolding o_assoc F_map_comp[symmetric] eval4_leaf4 F_map_id id_o ..
  finally show ?thesis .
qed

theorem corecU4_pointfree:
"F_map (extddRec4 (corecU4 s)) o s = dtor_J o corecU4 s" (is "?L = ?R")
unfolding corecU4_def
unfolding o_assoc unfoldU4_pointfree[symmetric] extddRec4_def
unfolding o_assoc[symmetric] case_sum_o_inj
apply(subst unfoldU4_Inl[symmetric, of s])
unfolding o_assoc case_sum_Inl_Inr_L extdd4_def ..

theorem corecU4:
"F_map (extddRec4 (corecU4 s)) (s a) = dtor_J (corecU4 s a)"
using corecU4_pointfree unfolding o_def fun_eq_iff by(rule allE)


subsection{* Coinduction up-to *}

definition "cptdd4 R \<equiv> (\<Sigma>\<Sigma>4_rel R ===> R) eval4 eval4"

definition "cngdd4 R \<equiv> equivp R \<and> cptdd4 R"

lemma cngdd4_Retr: "cngdd4 R \<Longrightarrow> cngdd4 (R \<sqinter> Retr R)"
  unfolding cngdd4_def cptdd4_def
  apply (erule conjE)
  apply (rule conjI[OF equivp_inf[OF _ equivp_retr]])
  apply assumption
  apply assumption
  apply (rule rel_funI)
  apply (frule predicate2D[OF \<Sigma>\<Sigma>4_rel_inf])
  apply (erule inf2E)
  apply (rule inf2I)
  apply (erule rel_funE)
  apply assumption
  apply assumption
  apply (subst Retr_def)
  apply (subst eval4_def)+
  apply (subst J.dtor_unfold)+
  unfolding F_rel_F_map_F_map Grp_def relcompp.simps[abs_def] conversep.simps[abs_def]
  apply auto
  unfolding eval4_def[symmetric]
  apply (rule predicate2D[OF F_rel_mono])
  apply (rule predicate2I)
  apply (erule rel_funD)
  apply assumption
  apply (rule F_rel_\<Sigma>\<Sigma>4_rel)
  unfolding \<Sigma>\<Sigma>4_rel_\<Sigma>\<Sigma>4_map_\<Sigma>\<Sigma>4_map vimage2p_rel_prod vimage2p_id
  unfolding vimage2p_def Retr_def[symmetric]
  apply assumption
  done

(* The generated congruence: *)
definition "genCngdd4 R j1 j2 \<equiv> \<forall> R'. R \<le> R' \<and> cngdd4 R' \<longrightarrow> R' j1 j2"

lemma cngdd4_genCngdd4: "cngdd4 (genCngdd4 R)"
unfolding cngdd4_def proof safe
  show "cptdd4 (genCngdd4 R)"
  unfolding cptdd4_def rel_fun_def proof safe
    fix x y assume A: "\<Sigma>\<Sigma>4_rel (genCngdd4 R) x y"
    show "genCngdd4 R (eval4 x) (eval4 y)"
    unfolding genCngdd4_def[abs_def] proof safe
      fix R' assume "R \<le> R'" and 2: "cngdd4 R'"
      hence "\<Sigma>\<Sigma>4_rel R' x y" by (metis A \<Sigma>\<Sigma>4.rel_mono_strong genCngdd4_def)
      thus "R' (eval4 x) (eval4 y)" using 2 unfolding cngdd4_def cptdd4_def rel_fun_def by auto
    qed
  qed
qed(rule equivpI, unfold reflp_def symp_def transp_def genCngdd4_def cngdd4_def equivp_def, auto)

lemma
    genCngdd4_refl[intro,simp]: "genCngdd4 R j j"
and genCngdd4_sym[intro]: "genCngdd4 R j1 j2 \<Longrightarrow> genCngdd4 R j2 j1"
and genCngdd4_trans[intro]: "\<lbrakk>genCngdd4 R j1 j2; genCngdd4 R j2 j3\<rbrakk> \<Longrightarrow> genCngdd4 R j1 j3"
using cngdd4_genCngdd4 unfolding cngdd4_def equivp_def by auto

lemma genCngdd4_eval4_rel_fun: "(\<Sigma>\<Sigma>4_rel (genCngdd4 R) ===> genCngdd4 R) eval4 eval4"
using cngdd4_genCngdd4 unfolding cngdd4_def cptdd4_def by auto

lemma genCngdd4_eval4: "\<Sigma>\<Sigma>4_rel (genCngdd4 R) x y \<Longrightarrow> genCngdd4 R (eval4 x) (eval4 y)"
using genCngdd4_eval4_rel_fun unfolding rel_fun_def by auto

lemma leq_genCngdd4: "R \<le> genCngdd4 R"
and imp_genCngdd4[intro]: "R j1 j2 \<Longrightarrow> genCngdd4 R j1 j2"
unfolding genCngdd4_def[abs_def] by auto

lemma genCngdd4_minimal: "\<lbrakk>R \<le> R'; cngdd4 R'\<rbrakk> \<Longrightarrow> genCngdd4 R \<le> R'"
unfolding genCngdd4_def[abs_def] by (metis (lifting, no_types) predicate2I)

theorem coinductionU_genCngdd4:
assumes "\<forall> a b. R a b \<longrightarrow> F_rel (genCngdd4 R) (dtor_J a) (dtor_J b)"
shows "R a b \<longrightarrow> a = b"
proof-
  let ?R' = "genCngdd4 R"
  have "R \<le> Retr ?R'" using assms unfolding Retr_def[abs_def] by auto
  hence "R \<le> ?R' \<sqinter> Retr ?R'" using leq_genCngdd4 by auto
  moreover have "cngdd4 (?R' \<sqinter> Retr ?R')" using cngdd4_Retr[OF cngdd4_genCngdd4[of R]] .
  ultimately have "?R' \<le> ?R' \<sqinter> Retr ?R'" using genCngdd4_minimal by metis
  hence "?R' \<le> Retr ?R'" by auto
  hence "?R' a b \<longrightarrow> a = b"  unfolding Retr_def[abs_def] by (intro J.dtor_coinduct) auto
  thus ?thesis using leq_genCngdd4 by auto
qed


subsection{* Flattening from term algebra to "one-step" algebra *}

(* Since (J \<Sigma>\<Sigma>4, eval4) is an Eilenberg-Moore algebra (i.e., is compatible with
the monadic structure, it yields an algebra on the signature functor.
This is crucial for having suitable simplification rules. *)

(* The one-step algebra (naturally associated to \<Lambda>4, not to dd4): *)
definition alg\<Lambda>4 :: "J \<Sigma>4 \<Rightarrow> J" where "alg\<Lambda>4 = eval4 o \<oo>\<pp>4 o \<Sigma>4_map leaf4"

theorem eval4_comp_\<oo>\<pp>4: "eval4 o \<oo>\<pp>4 = alg\<Lambda>4 o \<Sigma>4_map eval4"
unfolding alg\<Lambda>4_def
unfolding o_assoc[symmetric] \<Sigma>4.map_comp0[symmetric]
unfolding leaf4_natural[symmetric] unfolding \<Sigma>4.map_comp0
apply(rule sym) unfolding o_assoc apply(subst o_assoc[symmetric])
unfolding \<oo>\<pp>4_natural
unfolding o_assoc eval4_flat4[symmetric]
apply(subst o_assoc[symmetric]) unfolding flat4_commute[symmetric]
unfolding o_assoc[symmetric] \<Sigma>4.map_comp0[symmetric] flat4_leaf4 \<Sigma>4.map_id0 o_id ..

theorem eval4_\<oo>\<pp>4: "eval4 (\<oo>\<pp>4 t) = alg\<Lambda>4 (\<Sigma>4_map eval4 t)"
using eval4_comp_\<oo>\<pp>4 unfolding o_def fun_eq_iff by (rule allE)

theorem eval4_leaf4': "eval4 (leaf4 j) = j"
using eval4_leaf4 unfolding o_def fun_eq_iff id_def by (rule allE)

theorem dtor_J_alg\<Lambda>4: "dtor_J o alg\<Lambda>4 = F_map eval4 o \<Lambda>4 o \<Sigma>4_map <id, dtor_J>"
  unfolding alg\<Lambda>4_def eval4_def o_assoc dtor_unfold_J_pointfree \<Lambda>4_dd4
  unfolding o_assoc[symmetric] \<oo>\<pp>4_natural[symmetric] \<Sigma>4.map_comp0[symmetric] leaf4_natural
  ..

theorem dtor_J_alg\<Lambda>4': "dtor_J (alg\<Lambda>4 t) = F_map eval4 (\<Lambda>4 (\<Sigma>4_map (<id, dtor_J>) t))"
  by (rule trans[OF o_eq_dest[OF dtor_J_alg\<Lambda>4] o_apply])

theorem ctor_J_alg\<Lambda>4: "alg\<Lambda>4 t = ctor_J (F_map eval4 (\<Lambda>4 (\<Sigma>4_map (<id, dtor_J>) t)))"
  by (rule iffD1[OF J.dtor_inject trans[OF dtor_J_alg\<Lambda>4' J.dtor_ctor[symmetric]]])

(* Note: The user wi\<Lambda>4 indicate an "equation" equ :: J \<Sigma>4 \<Rightarrow> (J \<Sigma>\<Sigma>4) F
in order to define the operation alg\<Lambda>4 :: J \<Sigma>4 \<Rightarrow> J on the final coalgebra
according to dtor_J_alg\<Lambda>4.
The package wi\<Lambda>4 identify the polymorphic function \<Lambda>4 :: ('a \<times> 'a F) \<Sigma>4 \<Rightarrow> 'a \<Sigma>\<Sigma>4 F
such that equ = \<Lambda>4 o \<Sigma>4 <id, dtor_J>. Then the package wi\<Lambda>4 attempt to prove
automatica\<Lambda>4y that \<Lambda>4 is natural.  If the proof fails, the user wi\<Lambda>4 be asked to prove it.
Upon success, the distributive law is being registered.
*)

(* Customizing coinduction up-to: *)
definition "cpt\<Lambda>4 R \<equiv> (\<Sigma>4_rel R ===> R) alg\<Lambda>4 alg\<Lambda>4"

definition "cng\<Lambda>4 R \<equiv> equivp R \<and> cpt\<Lambda>4 R"

lemma cptdd4_iff_cpt\<Lambda>4: "cptdd4 R \<longleftrightarrow> cpt\<Lambda>4 R"
apply (rule iffI)
apply (unfold cpt\<Lambda>4_def cptdd4_def alg\<Lambda>4_def o_assoc[symmetric]) [1]
apply (erule rel_funD[OF rel_funD[OF comp_transfer]])
apply transfer_prover

apply (unfold cpt\<Lambda>4_def cptdd4_def) [1]
unfolding rel_fun_def
apply (rule allI)+
apply (rule \<Sigma>\<Sigma>4_rel_induct)
apply (simp only: eval4_leaf4')
unfolding eval4_\<oo>\<pp>4
apply (drule spec2)
apply (erule mp)
apply (rule iffD2[OF \<Sigma>4_rel_\<Sigma>4_map_\<Sigma>4_map])
apply (subst vimage2p_def)
apply assumption
done

(* This is the definition of genCngdd4 we need to work with: *)
theorem genCngdd4_def2: "genCngdd4 R j1 j2 \<longleftrightarrow> (\<forall> R'. R \<le> R' \<and> cng\<Lambda>4 R' \<longrightarrow> R' j1 j2)"
unfolding genCngdd4_def cngdd4_def cng\<Lambda>4_def cptdd4_iff_cpt\<Lambda>4 ..


subsection {* Incremental coinduction *}

interpretation I4: Incremental where Retr = Retr and Cl = genCngdd4
proof
  show "mono Retr" by (rule mono_retr)
next
  show "mono genCngdd4" unfolding mono_def
  unfolding genCngdd4_def[abs_def] by (smt order.trans predicate2I)
next
  fix r show "genCngdd4 (genCngdd4 r) = genCngdd4 r"
  by (metis cngdd4_genCngdd4 genCngdd4_minimal leq_genCngdd4 order_class.order.antisym)
next
  fix r show "r \<le> genCngdd4 r" by (metis leq_genCngdd4)
next
  fix r assume "genCngdd4 r = r" thus "genCngdd4 (r \<sqinter> Retr r) = r \<sqinter> Retr r"
  by (metis antisym cngdd4_Retr cngdd4_genCngdd4 genCngdd4_minimal
            inf.orderI inf_idem leq_genCngdd4)
qed

definition ded4 where "ded4 r s \<equiv> I4.ded r s"

theorems Ax = I4.Ax'[unfolded ded4_def[symmetric]]
theorems Split = I4.Split[unfolded ded4_def[symmetric]]
theorems Coind = I4.Coind[unfolded ded4_def[symmetric]]

theorem soundness_ded:
assumes "ded4 (op =) s"  shows "s \<le> (op =)"
unfolding gfp_Retr_eq[symmetric] apply(rule I4.soundness_ded[unfolded ded4_def[symmetric]] )
using assms unfolding gfp_Retr_eq[symmetric] ded4_def .

unused_thms

end
