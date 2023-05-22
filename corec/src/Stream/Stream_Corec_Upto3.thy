header {* Corecursion and coinduction up to *}

theory Stream_Corec_Upto3
imports Stream_Lift_to_Free3
begin


subsection{* The algebra associated to dd3 *}

definition "eval3 \<equiv> dtor_unfold_J (dd3 o \<Sigma>\<Sigma>3_map <id, dtor_J>)"

lemma eval3: "F_map eval3 o dd3 o \<Sigma>\<Sigma>3_map <id, dtor_J> = dtor_J o eval3"
  unfolding eval3_def dtor_unfold_J_pointfree unfolding o_assoc ..

lemma eval3_ctor_J: "ctor_J o F_map eval3 o dd3 o \<Sigma>\<Sigma>3_map <id, dtor_J> = eval3"
  unfolding o_def spec[OF eval3[unfolded o_def fun_eq_iff]] J.ctor_dtor ..

lemma eval3_leaf3: "eval3 \<circ> leaf3 = id"
proof (rule trans)
  show "eval3 \<circ> leaf3 = dtor_unfold_J dtor_J"
  apply(rule J.dtor_unfold_unique)
  unfolding o_assoc eval3[symmetric] unfolding o_assoc[symmetric] leaf3_natural
  apply(rule sym)
  unfolding F_map_comp o_assoc apply (subst o_assoc[symmetric])
  unfolding dd3_leaf3 unfolding o_assoc[symmetric] by simp
qed(metis F_map_id J.dtor_unfold_unique fun.map_id o_id)

lemma eval3_flat3: "eval3 \<circ> flat3 = eval3 \<circ> \<Sigma>\<Sigma>3_map eval3"
proof (rule trans)
  let ?K3 = "dtor_unfold_J (dd3 o \<Sigma>\<Sigma>3_map <\<Sigma>\<Sigma>3_map fst, dd3> o \<Sigma>\<Sigma>3_map (\<Sigma>\<Sigma>3_map <id, dtor_J>))"
  show "eval3 \<circ> flat3 = ?K3"
  apply(rule J.dtor_unfold_unique)
  unfolding F_map_comp o_assoc
  apply(subst o_assoc[symmetric], subst o_assoc[symmetric])
  unfolding dd3_flat3
  unfolding o_assoc[symmetric] \<Sigma>\<Sigma>3.map_comp0[symmetric] snd_convol
  unfolding flat3_natural
  unfolding o_assoc eval3 ..
  (*  *)
  have A: "<eval3, dtor_J o eval3> = <id,dtor_J> o eval3" by simp
  show "?K3 = eval3 \<circ> \<Sigma>\<Sigma>3_map eval3"
  apply(rule J.dtor_unfold_unique[symmetric])
  unfolding o_assoc[symmetric] \<Sigma>\<Sigma>3.map_comp0[symmetric] map_prod_o_convol id_o
  unfolding F_map_comp o_assoc
  apply(subst o_assoc[symmetric]) unfolding dd3_natural[symmetric]
  unfolding o_assoc[symmetric] \<Sigma>\<Sigma>3.map_comp0[symmetric]
  unfolding o_assoc unfolding map_prod_o_convol unfolding convol_o
  unfolding o_assoc[symmetric] \<Sigma>\<Sigma>3.map_comp0[symmetric] fst_convol \<Sigma>\<Sigma>3.map_id0 o_id
  unfolding o_assoc eval3 unfolding A unfolding convol_o id_o
  apply(rule sym) apply(subst eval3[symmetric])
  unfolding o_assoc[symmetric] \<Sigma>\<Sigma>3.map_comp0[symmetric] convol_o id_o ..
qed


subsection{* The correspondence between coalgebras up to and coalgebras *}

(* This correspondence, and add3 the lemmas of this subsection, make
sense not only for (J,dtor_J,eval3), but also for any dd3-bialgebra *)

(* Coalgebra-up-to to coalgebra and vice versa: *)
definition cut\<Sigma>\<Sigma>3Oc :: "('a \<Rightarrow> 'a \<Sigma>\<Sigma>3 F) \<Rightarrow> ('a \<Sigma>\<Sigma>3 \<Rightarrow> 'a \<Sigma>\<Sigma>3 F)"
where "cut\<Sigma>\<Sigma>3Oc s \<equiv> F_map flat3 o dd3 o \<Sigma>\<Sigma>3_map <leaf3, s>"
definition c\<Sigma>\<Sigma>3Ocut :: "('a \<Sigma>\<Sigma>3 \<Rightarrow> 'a \<Sigma>\<Sigma>3 F) \<Rightarrow> ('a \<Rightarrow> 'a \<Sigma>\<Sigma>3 F)"
where "c\<Sigma>\<Sigma>3Ocut s' \<equiv> s' o leaf3"

lemma c\<Sigma>\<Sigma>3Ocut_cut\<Sigma>\<Sigma>3Oc: "c\<Sigma>\<Sigma>3Ocut (cut\<Sigma>\<Sigma>3Oc s) = s"
unfolding c\<Sigma>\<Sigma>3Ocut_def cut\<Sigma>\<Sigma>3Oc_def
unfolding o_assoc[symmetric] unfolding leaf3_natural
unfolding o_assoc apply(subst o_assoc[symmetric])
unfolding dd3_leaf3 unfolding o_assoc F_map_comp[symmetric] flat3_leaf3
unfolding F_map_id id_o by simp

lemma cut\<Sigma>\<Sigma>3Oc_inj: "cut\<Sigma>\<Sigma>3Oc s3 = cut\<Sigma>\<Sigma>3Oc s2 \<longleftrightarrow> s3 = s2"
by (metis c\<Sigma>\<Sigma>3Ocut_cut\<Sigma>\<Sigma>3Oc)

lemma c\<Sigma>\<Sigma>3Ocut_surj: "\<exists> s'. c\<Sigma>\<Sigma>3Ocut s' = s"
using c\<Sigma>\<Sigma>3Ocut_cut\<Sigma>\<Sigma>3Oc by(rule exI[of _ "cut\<Sigma>\<Sigma>3Oc s"])

(* Morphism-up-to to morphism and vice versa: *)
(* The dd3-extension of a function *)
definition extdd3 :: "('a \<Rightarrow> J) \<Rightarrow> ('a \<Sigma>\<Sigma>3 \<Rightarrow> J)"
where "extdd3 f \<equiv> eval3 o \<Sigma>\<Sigma>3_map f"
(* The restriction of a function *)  term eval3
definition restr :: "('a \<Sigma>\<Sigma>3 \<Rightarrow> J) \<Rightarrow> ('a \<Rightarrow> J)"
where "restr f' \<equiv> f' o leaf3"

(* We think of extdd3 and restr as operating
extdd3 : Hom_dd3(s,dtor_J) \<rightarrow> Hom(cut\<Sigma>\<Sigma>3Oc s,dtor_J) and
restr : Hom(cut\<Sigma>\<Sigma>3Oc s,dtor_J) \<rightarrow> Hom_dd3(s,dtor_J), where
Hom(cut\<Sigma>\<Sigma>3Oc s,dtor_J) is the set of coalgebra morphisms betwee cut\<Sigma>\<Sigma>3Oc s and dtor_J and
Hom_dd3(s,dtor_J) is the set of coalgebra up-to-dd3-morphisms between s and dtor_J  *)

(* extdd3 is wedd3-defined: *)
lemma extdd3_mor:
assumes f:  "F_map (extdd3 f) o s = dtor_J o f"
shows "F_map (extdd3 f) o cut\<Sigma>\<Sigma>3Oc s = dtor_J o (extdd3 f)"
proof-
  have AA: "eval3 ** F_map eval3 \<circ> (\<Sigma>\<Sigma>3_map f ** F_map (\<Sigma>\<Sigma>3_map f) \<circ> <leaf3 , s>) =
            <f , F_map eval3 \<circ> (F_map (\<Sigma>\<Sigma>3_map f) \<circ> s)>"
  unfolding map_prod_o_convol unfolding leaf3_natural o_assoc eval3_leaf3 id_o  ..
  show ?thesis
  unfolding extdd3_def
  unfolding o_assoc eval3[symmetric]
  unfolding o_assoc[symmetric] \<Sigma>\<Sigma>3.map_comp0[symmetric]
  unfolding convol_comp[symmetric] id_o
  unfolding f[symmetric, unfolded extdd3_def]
  unfolding o_assoc
  apply(subst o_assoc[symmetric])
  unfolding F_map_comp o_assoc
  unfolding cut\<Sigma>\<Sigma>3Oc_def
  unfolding o_assoc
  unfolding F_map_comp[symmetric] unfolding o_assoc[symmetric]
  unfolding flat3_natural[symmetric]
  unfolding o_assoc F_map_comp
  apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
  unfolding dd3_natural[symmetric]
  unfolding o_assoc unfolding F_map_comp[symmetric] eval3_flat3
  unfolding F_map_comp apply(subst o_assoc[symmetric])
  unfolding dd3_natural[symmetric] unfolding o_assoc[symmetric] \<Sigma>\<Sigma>3.map_comp0[symmetric]
  unfolding o_assoc[symmetric] AA[unfolded o_assoc[symmetric]] ..
qed

lemma mor_cut\<Sigma>\<Sigma>3Oc_flat3:
assumes f': "F_map f' o cut\<Sigma>\<Sigma>3Oc s = dtor_J o f'"
shows "eval3 o \<Sigma>\<Sigma>3_map f' = f' o flat3"
proof(rule trans) (* this proof is clearly improvable: *)
  def h \<equiv> "dd3 o \<Sigma>\<Sigma>3_map <id,cut\<Sigma>\<Sigma>3Oc s>"
  have f'_id: "f' = f' o id" by simp
  show "eval3 \<circ> \<Sigma>\<Sigma>3_map f' = dtor_unfold_J h"
  apply(rule J.dtor_unfold_unique, rule sym)
  unfolding o_assoc eval3[symmetric]
  unfolding o_assoc[symmetric] \<Sigma>\<Sigma>3.map_comp0[symmetric]
  unfolding convol_comp_id1[symmetric] unfolding f'[symmetric]
  apply(subst f'_id)
  unfolding o_assoc \<Sigma>\<Sigma>3.map_comp0
  apply(subst o_assoc[symmetric])
  unfolding o_assoc[symmetric] F_map_comp
  unfolding h_def apply(rule sym)
  unfolding o_assoc apply(subst o_assoc[symmetric])
  unfolding dd3_natural[symmetric] unfolding o_assoc[symmetric]
  unfolding \<Sigma>\<Sigma>3.map_comp0[symmetric] map_prod_o_convol ..
  (*  *)
  have AA: "<id , cut\<Sigma>\<Sigma>3Oc s> = (flat3 ** F_map flat3) o (id ** dd3) o <leaf3, \<Sigma>\<Sigma>3_map <leaf3 , s>>"
  unfolding map_prod_o_convol o_assoc map_prod.comp cut\<Sigma>\<Sigma>3Oc_def o_id flat3_leaf3 ..
  have BB: "flat3 ** F_map flat3 \<circ> id ** dd3 \<circ> <leaf3 , \<Sigma>\<Sigma>3_map <leaf3 , s>> = flat3 ** F_map flat3 \<circ> id ** dd3 \<circ> <\<Sigma>\<Sigma>3_map leaf3 , \<Sigma>\<Sigma>3_map <leaf3 , s>>"
  unfolding map_prod.comp unfolding map_prod_o_convol unfolding o_id unfolding flat3_leaf3 leaf3_flat3 ..
  show "dtor_unfold_J h = f' \<circ> flat3"
  apply(rule J.dtor_unfold_unique[symmetric], rule sym)
  unfolding o_assoc f'[symmetric]
  unfolding F_map_comp o_assoc[symmetric]
  apply(rule arg_cong[of _ _ "op o (F_map f')"])
  unfolding h_def
  unfolding AA BB
  unfolding \<Sigma>\<Sigma>3.map_comp0 apply(rule sym)
  unfolding o_assoc apply(subst o_assoc[symmetric])
  unfolding dd3_natural
  unfolding o_assoc F_map_comp[symmetric]
  unfolding flat3_assoc unfolding F_map_comp
  unfolding cut\<Sigma>\<Sigma>3Oc_def o_assoc[symmetric] apply(rule arg_cong[of _ _ "op o (F_map flat3)"])
  unfolding o_assoc
  unfolding o_assoc[symmetric] unfolding \<Sigma>\<Sigma>3.map_comp0[symmetric] unfolding map_prod_o_convol id_o
  unfolding flat3_natural[symmetric] unfolding o_assoc
  unfolding dd3_flat3[symmetric] unfolding o_assoc[symmetric] unfolding \<Sigma>\<Sigma>3.map_comp0[symmetric]
  unfolding convol_o unfolding \<Sigma>\<Sigma>3.map_comp0[symmetric] unfolding fst_convol ..
qed

(* restr is wedd3-defined:  *)
lemma restr_mor:
assumes f': "F_map f' o cut\<Sigma>\<Sigma>3Oc s = dtor_J o f'"
shows "F_map (extdd3 (restr f')) o s = dtor_J o restr f'"
unfolding extdd3_def restr_def \<Sigma>\<Sigma>3.map_comp0
unfolding o_assoc mor_cut\<Sigma>\<Sigma>3Oc_flat3[OF f']
unfolding o_assoc[symmetric] leaf3_flat3 o_id
unfolding o_assoc f'[symmetric]
unfolding o_assoc[symmetric] c\<Sigma>\<Sigma>3Ocut_cut\<Sigma>\<Sigma>3Oc[unfolded c\<Sigma>\<Sigma>3Ocut_def] ..

lemma extdd3_restr:
assumes f': "F_map f' o cut\<Sigma>\<Sigma>3Oc s = dtor_J o f'"
shows "extdd3 (restr f') = f'"
proof-
  have "f' = eval3 o \<Sigma>\<Sigma>3_map f' o leaf3"
  unfolding o_assoc[symmetric] leaf3_natural
  unfolding o_assoc eval3_leaf3 by simp
  also have "... = eval3 o \<Sigma>\<Sigma>3_map (f' o leaf3)"
  unfolding \<Sigma>\<Sigma>3.map_comp0 o_assoc
  unfolding mor_cut\<Sigma>\<Sigma>3Oc_flat3[OF f'] unfolding o_assoc[symmetric] flat3_leaf3 leaf3_flat3 ..
  finally have A: "f' = eval3 o \<Sigma>\<Sigma>3_map (f' o leaf3)" .
  show ?thesis unfolding extdd3_def restr_def A[symmetric] ..
qed

lemma restr_inj:
assumes f3': "F_map f3' o cut\<Sigma>\<Sigma>3Oc s = dtor_J o f3'"
and f2': "F_map f2' o cut\<Sigma>\<Sigma>3Oc s = dtor_J o f2'"
shows "restr f3' = restr f2' \<longleftrightarrow> f3' = f2'"
using extdd3_restr[OF f3'] extdd3_restr[OF f2'] by metis

lemma extdd3_surj:
assumes f': "F_map f' o cut\<Sigma>\<Sigma>3Oc s = dtor_J o f'"
shows "\<exists> f. extdd3 f = f'"
using extdd3_restr[OF f'] by(rule exI[of _ "restr f'"])

lemma restr_extdd3:
assumes f: "F_map (extdd3 f) o s = dtor_J o f"
shows "restr (extdd3 f) = f"
proof-
  have "dtor_J o f = F_map (extdd3 f) o s" using assms unfolding extdd3_def by (rule sym)
  also have "... = dtor_J o restr (extdd3 f)"
  unfolding restr_def unfolding o_assoc extdd3_mor[OF f, symmetric]
  unfolding o_assoc[symmetric] c\<Sigma>\<Sigma>3Ocut_cut\<Sigma>\<Sigma>3Oc[unfolded c\<Sigma>\<Sigma>3Ocut_def] ..
  finally have "dtor_J o f = dtor_J \<circ> restr (extdd3 f)" .
  thus ?thesis unfolding dtor_J_o_inj by (rule sym)
qed

lemma extdd3_inj:
assumes f1: "F_map (extdd3 f1) o s = dtor_J o f1"
and f2: "F_map (extdd3 f2) o s = dtor_J o f2"
shows "extdd3 f1 = extdd3 f2 \<longleftrightarrow> f1 = f2"
using restr_extdd3[OF f1] restr_extdd3[OF f2] by metis

lemma restr_surj:
assumes f: "F_map (extdd3 f) o s = dtor_J o f"
shows "\<exists> f'. restr f' = f"
using restr_extdd3[OF f] by(rule exI[of _ "extdd3 f"])


subsection{* Coiteration up-to *}

definition "unfoldU3 s \<equiv> restr (dtor_unfold_J (cut\<Sigma>\<Sigma>3Oc s))"

theorem unfoldU3_pointfree:
"F_map (extdd3 (unfoldU3 s)) o s = dtor_J o unfoldU3 s"
unfolding unfoldU3_def apply(rule restr_mor)
unfolding dtor_unfold_J_pointfree ..

theorem unfoldU3: "F_map (extdd3 (unfoldU3 s)) (s a) = dtor_J (unfoldU3 s a)"
using unfoldU3_pointfree unfolding o_def fun_eq_iff by(rule allE)

theorem unfoldU3_ctor_J:
"ctor_J (F_map (extdd3 (unfoldU3 s)) (s a)) = unfoldU3 s a"
using unfoldU3 by (metis J.ctor_dtor)

theorem unfoldU3_unique:
assumes "F_map (extdd3 f) o s = dtor_J o f"
shows "f = unfoldU3 s"
proof-
  note f = extdd3_mor[OF assms]  note co = extdd3_mor[OF unfoldU3_pointfree]
  have A: "extdd3 f = extdd3 (unfoldU3 s)"
  proof(rule trans)
    show "extdd3 f = dtor_unfold_J (cut\<Sigma>\<Sigma>3Oc s)" apply(rule J.dtor_unfold_unique) using f .
    show "dtor_unfold_J (cut\<Sigma>\<Sigma>3Oc s) = extdd3 (unfoldU3 s)"
     apply(rule J.dtor_unfold_unique[symmetric]) using co .
  qed
  show ?thesis using A unfolding extdd3_inj[OF assms unfoldU3_pointfree] .
qed

lemma unfoldU3_ctor_J_pointfree:
"ctor_J o F_map (extdd3 (unfoldU3 s)) o s = unfoldU3 s"
unfolding o_def fun_eq_iff by (subst unfoldU3_ctor_J[symmetric]) (rule allI, rule refl)

(* Corecursion up to: *)
definition corecU3 :: "('a \<Rightarrow> (J + 'a) \<Sigma>\<Sigma>3 F) \<Rightarrow> 'a \<Rightarrow> J" where
"corecU3 s = unfoldU3 (case_sum (dd3 o leaf3 o <Inl, F_map Inl o dtor_J>) s) o Inr"

definition extddRec3 where
"extddRec3 f \<equiv> eval3 \<circ> \<Sigma>\<Sigma>3_map (case_sum id f)"

lemma unfoldU3_Inl:
"unfoldU3 (case_sum (dd3 \<circ> leaf3 \<circ> <Inl , F_map Inl \<circ> dtor_J>) s) o Inl = id"
(is "?L = ?R")
proof-
  have "?L = unfoldU3 (dd3 o leaf3 o <id, dtor_J>)"
  apply(rule unfoldU3_unique)
  unfolding o_assoc unfoldU3_pointfree[symmetric]
  unfolding o_assoc[symmetric] case_sum_o_inj extdd3_def F_map_comp \<Sigma>\<Sigma>3.map_comp0
  unfolding o_assoc apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric],
                          subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
  unfolding dd3_natural[symmetric]
  apply(subst o_assoc[symmetric]) unfolding leaf3_natural
  unfolding o_assoc[symmetric] map_prod_o_convol o_id ..
  also have "... = ?R"
  apply(rule sym, rule unfoldU3_unique)
  unfolding extdd3_def \<Sigma>\<Sigma>3.map_id0 o_id dd3_leaf3
  unfolding o_assoc[symmetric] snd_convol
  unfolding o_assoc F_map_comp[symmetric] eval3_leaf3 F_map_id id_o ..
  finally show ?thesis .
qed

theorem corecU3_pointfree:
"F_map (extddRec3 (corecU3 s)) o s = dtor_J o corecU3 s" (is "?L = ?R")
unfolding corecU3_def
unfolding o_assoc unfoldU3_pointfree[symmetric] extddRec3_def
unfolding o_assoc[symmetric] case_sum_o_inj
apply(subst unfoldU3_Inl[symmetric, of s])
unfolding o_assoc case_sum_Inl_Inr_L extdd3_def ..

theorem corecU3:
"F_map (extddRec3 (corecU3 s)) (s a) = dtor_J (corecU3 s a)"
using corecU3_pointfree unfolding o_def fun_eq_iff by(rule allE)


subsection{* Coinduction up-to *}

definition "cptdd3 R \<equiv> (\<Sigma>\<Sigma>3_rel R ===> R) eval3 eval3"

definition "cngdd3 R \<equiv> equivp R \<and> cptdd3 R"

lemma cngdd3_Retr: "cngdd3 R \<Longrightarrow> cngdd3 (R \<sqinter> Retr R)"
  unfolding cngdd3_def cptdd3_def
  apply (erule conjE)
  apply (rule conjI[OF equivp_inf[OF _ equivp_retr]])
  apply assumption
  apply assumption
  apply (rule rel_funI)
  apply (frule predicate2D[OF \<Sigma>\<Sigma>3_rel_inf])
  apply (erule inf2E)
  apply (rule inf2I)
  apply (erule rel_funE)
  apply assumption
  apply assumption
  apply (subst Retr_def)
  apply (subst eval3_def)+
  apply (subst J.dtor_unfold)+
  unfolding F_rel_F_map_F_map Grp_def relcompp.simps[abs_def] conversep.simps[abs_def]
  apply auto
  unfolding eval3_def[symmetric]
  apply (rule predicate2D[OF F_rel_mono])
  apply (rule predicate2I)
  apply (erule rel_funD)
  apply assumption
  apply (rule F_rel_\<Sigma>\<Sigma>3_rel)
  unfolding \<Sigma>\<Sigma>3_rel_\<Sigma>\<Sigma>3_map_\<Sigma>\<Sigma>3_map vimage2p_rel_prod vimage2p_id
  unfolding vimage2p_def Retr_def[symmetric]
  apply assumption
  done

(* The generated congruence: *)
definition "genCngdd3 R j1 j2 \<equiv> \<forall> R'. R \<le> R' \<and> cngdd3 R' \<longrightarrow> R' j1 j2"

lemma cngdd3_genCngdd3: "cngdd3 (genCngdd3 R)"
unfolding cngdd3_def proof safe
  show "cptdd3 (genCngdd3 R)"
  unfolding cptdd3_def rel_fun_def proof safe
    fix x y assume A: "\<Sigma>\<Sigma>3_rel (genCngdd3 R) x y"
    show "genCngdd3 R (eval3 x) (eval3 y)"
    unfolding genCngdd3_def[abs_def] proof safe
      fix R' assume "R \<le> R'" and 2: "cngdd3 R'"
      hence "\<Sigma>\<Sigma>3_rel R' x y" by (metis A \<Sigma>\<Sigma>3.rel_mono_strong genCngdd3_def)
      thus "R' (eval3 x) (eval3 y)" using 2 unfolding cngdd3_def cptdd3_def rel_fun_def by auto
    qed
  qed
qed(rule equivpI, unfold reflp_def symp_def transp_def genCngdd3_def cngdd3_def equivp_def, auto)

lemma
    genCngdd3_refl[intro,simp]: "genCngdd3 R j j"
and genCngdd3_sym[intro]: "genCngdd3 R j1 j2 \<Longrightarrow> genCngdd3 R j2 j1"
and genCngdd3_trans[intro]: "\<lbrakk>genCngdd3 R j1 j2; genCngdd3 R j2 j3\<rbrakk> \<Longrightarrow> genCngdd3 R j1 j3"
using cngdd3_genCngdd3 unfolding cngdd3_def equivp_def by auto

lemma genCngdd3_eval3_rel_fun: "(\<Sigma>\<Sigma>3_rel (genCngdd3 R) ===> genCngdd3 R) eval3 eval3"
using cngdd3_genCngdd3 unfolding cngdd3_def cptdd3_def by auto

lemma genCngdd3_eval3: "\<Sigma>\<Sigma>3_rel (genCngdd3 R) x y \<Longrightarrow> genCngdd3 R (eval3 x) (eval3 y)"
using genCngdd3_eval3_rel_fun unfolding rel_fun_def by auto

lemma leq_genCngdd3: "R \<le> genCngdd3 R"
and imp_genCngdd3[intro]: "R j1 j2 \<Longrightarrow> genCngdd3 R j1 j2"
unfolding genCngdd3_def[abs_def] by auto

lemma genCngdd3_minimal: "\<lbrakk>R \<le> R'; cngdd3 R'\<rbrakk> \<Longrightarrow> genCngdd3 R \<le> R'"
unfolding genCngdd3_def[abs_def] by (metis (lifting, no_types) predicate2I)

theorem coinductionU_genCngdd3:
assumes "\<forall> a b. R a b \<longrightarrow> F_rel (genCngdd3 R) (dtor_J a) (dtor_J b)"
shows "R a b \<longrightarrow> a = b"
proof-
  let ?R' = "genCngdd3 R"
  have "R \<le> Retr ?R'" using assms unfolding Retr_def[abs_def] by auto
  hence "R \<le> ?R' \<sqinter> Retr ?R'" using leq_genCngdd3 by auto
  moreover have "cngdd3 (?R' \<sqinter> Retr ?R')" using cngdd3_Retr[OF cngdd3_genCngdd3[of R]] .
  ultimately have "?R' \<le> ?R' \<sqinter> Retr ?R'" using genCngdd3_minimal by metis
  hence "?R' \<le> Retr ?R'" by auto
  hence "?R' a b \<longrightarrow> a = b"  unfolding Retr_def[abs_def] by (intro J.dtor_coinduct) auto
  thus ?thesis using leq_genCngdd3 by auto
qed


subsection{* Flattening from term algebra to "one-step" algebra *}

(* Since (J \<Sigma>\<Sigma>3, eval3) is an Eilenberg-Moore algebra (i.e., is compatible with
the monadic structure, it yields an algebra on the signature functor.
This is crucial for having suitable simplification rules. *)

(* The one-step algebra (naturally associated to \<Lambda>3, not to dd3): *)
definition alg\<Lambda>3 :: "J \<Sigma>3 \<Rightarrow> J" where "alg\<Lambda>3 = eval3 o \<oo>\<pp>3 o \<Sigma>3_map leaf3"

theorem eval3_comp_\<oo>\<pp>3: "eval3 o \<oo>\<pp>3 = alg\<Lambda>3 o \<Sigma>3_map eval3"
unfolding alg\<Lambda>3_def
unfolding o_assoc[symmetric] \<Sigma>3.map_comp0[symmetric]
unfolding leaf3_natural[symmetric] unfolding \<Sigma>3.map_comp0
apply(rule sym) unfolding o_assoc apply(subst o_assoc[symmetric])
unfolding \<oo>\<pp>3_natural
unfolding o_assoc eval3_flat3[symmetric]
apply(subst o_assoc[symmetric]) unfolding flat3_commute[symmetric]
unfolding o_assoc[symmetric] \<Sigma>3.map_comp0[symmetric] flat3_leaf3 \<Sigma>3.map_id0 o_id ..

theorem eval3_\<oo>\<pp>3: "eval3 (\<oo>\<pp>3 t) = alg\<Lambda>3 (\<Sigma>3_map eval3 t)"
using eval3_comp_\<oo>\<pp>3 unfolding o_def fun_eq_iff by (rule allE)

theorem eval3_leaf3': "eval3 (leaf3 j) = j"
using eval3_leaf3 unfolding o_def fun_eq_iff id_def by (rule allE)

theorem dtor_J_alg\<Lambda>3: "dtor_J o alg\<Lambda>3 = F_map eval3 o \<Lambda>3 o \<Sigma>3_map <id, dtor_J>"
  unfolding alg\<Lambda>3_def eval3_def o_assoc dtor_unfold_J_pointfree \<Lambda>3_dd3
  unfolding o_assoc[symmetric] \<oo>\<pp>3_natural[symmetric] \<Sigma>3.map_comp0[symmetric] leaf3_natural
  ..

theorem dtor_J_alg\<Lambda>3': "dtor_J (alg\<Lambda>3 t) = F_map eval3 (\<Lambda>3 (\<Sigma>3_map (<id, dtor_J>) t))"
  by (rule trans[OF o_eq_dest[OF dtor_J_alg\<Lambda>3] o_apply])

theorem ctor_J_alg\<Lambda>3: "alg\<Lambda>3 t = ctor_J (F_map eval3 (\<Lambda>3 (\<Sigma>3_map (<id, dtor_J>) t)))"
  by (rule iffD1[OF J.dtor_inject trans[OF dtor_J_alg\<Lambda>3' J.dtor_ctor[symmetric]]])

(* Note: The user wi\<Lambda>3 indicate an "equation" equ :: J \<Sigma>3 \<Rightarrow> (J \<Sigma>\<Sigma>3) F
in order to define the operation alg\<Lambda>3 :: J \<Sigma>3 \<Rightarrow> J on the final coalgebra
according to dtor_J_alg\<Lambda>3.
The package wi\<Lambda>3 identify the polymorphic function \<Lambda>3 :: ('a \<times> 'a F) \<Sigma>3 \<Rightarrow> 'a \<Sigma>\<Sigma>3 F
such that equ = \<Lambda>3 o \<Sigma>3 <id, dtor_J>. Then the package wi\<Lambda>3 attempt to prove
automatica\<Lambda>3y that \<Lambda>3 is natural.  If the proof fails, the user wi\<Lambda>3 be asked to prove it.
Upon success, the distributive law is being registered.
*)

(* Customizing coinduction up-to: *)
definition "cpt\<Lambda>3 R \<equiv> (\<Sigma>3_rel R ===> R) alg\<Lambda>3 alg\<Lambda>3"

definition "cng\<Lambda>3 R \<equiv> equivp R \<and> cpt\<Lambda>3 R"

lemma cptdd3_iff_cpt\<Lambda>3: "cptdd3 R \<longleftrightarrow> cpt\<Lambda>3 R"
apply (rule iffI)
apply (unfold cpt\<Lambda>3_def cptdd3_def alg\<Lambda>3_def o_assoc[symmetric]) [1]
apply (erule rel_funD[OF rel_funD[OF comp_transfer]])
apply transfer_prover

apply (unfold cpt\<Lambda>3_def cptdd3_def) [1]
unfolding rel_fun_def
apply (rule allI)+
apply (rule \<Sigma>\<Sigma>3_rel_induct)
apply (simp only: eval3_leaf3')
unfolding eval3_\<oo>\<pp>3
apply (drule spec2)
apply (erule mp)
apply (rule iffD2[OF \<Sigma>3_rel_\<Sigma>3_map_\<Sigma>3_map])
apply (subst vimage2p_def)
apply assumption
done

(* This is the definition of genCngdd3 we need to work with: *)
theorem genCngdd3_def2: "genCngdd3 R j1 j2 \<longleftrightarrow> (\<forall> R'. R \<le> R' \<and> cng\<Lambda>3 R' \<longrightarrow> R' j1 j2)"
unfolding genCngdd3_def cngdd3_def cng\<Lambda>3_def cptdd3_iff_cpt\<Lambda>3 ..


subsection {* Incremental coinduction *}

interpretation I3: Incremental where Retr = Retr and Cl = genCngdd3
proof
  show "mono Retr" by (rule mono_retr)
next
  show "mono genCngdd3" unfolding mono_def
  unfolding genCngdd3_def[abs_def] by (smt order.trans predicate2I)
next
  fix r show "genCngdd3 (genCngdd3 r) = genCngdd3 r"
  by (metis cngdd3_genCngdd3 genCngdd3_minimal leq_genCngdd3 order_class.order.antisym)
next
  fix r show "r \<le> genCngdd3 r" by (metis leq_genCngdd3)
next
  fix r assume "genCngdd3 r = r" thus "genCngdd3 (r \<sqinter> Retr r) = r \<sqinter> Retr r"
  by (metis antisym cngdd3_Retr cngdd3_genCngdd3 genCngdd3_minimal
            inf.orderI inf_idem leq_genCngdd3)
qed

definition ded3 where "ded3 r s \<equiv> I3.ded r s"

theorems Ax = I3.Ax'[unfolded ded3_def[symmetric]]
theorems Split = I3.Split[unfolded ded3_def[symmetric]]
theorems Coind = I3.Coind[unfolded ded3_def[symmetric]]

theorem soundness_ded:
assumes "ded3 (op =) s"  shows "s \<le> (op =)"
unfolding gfp_Retr_eq[symmetric] apply(rule I3.soundness_ded[unfolded ded3_def[symmetric]] )
using assms unfolding gfp_Retr_eq[symmetric] ded3_def .

unused_thms

end
