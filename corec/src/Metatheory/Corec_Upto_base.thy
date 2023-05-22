header {* Corecursion and coinduction up to for the initial law *}

theory Corec_Upto_base
imports Lift_to_Free_base
begin


(* This theory works more generally, for any BNFs \<Sigma>\<Sigma>_base and F such that
\<Sigma>\<Sigma>_base is a monad and dd is a (pointed) (\<Sigma>\<Sigma>_base,\<Sigma>\<Sigma>_base,F)-distributive law compatible with the monadic structure.  *)

subsection{* The algebra associated to dd_base *}

definition "eval_base \<equiv> dtor_unfold_J (dd_base o \<Sigma>\<Sigma>_base_map <id, dtor_J>)"

lemma eval_base: "F_map eval_base o dd_base o \<Sigma>\<Sigma>_base_map <id, dtor_J> = dtor_J o eval_base"
  unfolding eval_base_def dtor_unfold_J_pointfree unfolding o_assoc ..

lemma eval_base_ctor_J: "ctor_J o F_map eval_base o dd_base o \<Sigma>\<Sigma>_base_map <id, dtor_J> = eval_base"
  unfolding o_def spec[OF eval_base[unfolded o_def fun_eq_iff]] J.ctor_dtor ..

lemma eval_base_leaf_base: "eval_base \<circ> leaf_base = id"
proof (rule trans)
  show "eval_base \<circ> leaf_base = dtor_unfold_J dtor_J"
  apply(rule J.dtor_unfold_unique)
  unfolding o_assoc eval_base[symmetric] unfolding o_assoc[symmetric] leaf_base_natural
  apply(rule sym)
  unfolding F_map_comp o_assoc apply (subst o_assoc[symmetric])
  unfolding dd_base_leaf_base unfolding o_assoc[symmetric] by simp
qed(metis F_map_id J.dtor_unfold_unique fun.map_id o_id)

lemma eval_base_flat_base: "eval_base \<circ> flat_base = eval_base \<circ> \<Sigma>\<Sigma>_base_map eval_base" term "eval_base o flat_base"
proof (rule trans)
  let ?K = "dtor_unfold_J (dd_base o \<Sigma>\<Sigma>_base_map <\<Sigma>\<Sigma>_base_map fst, dd_base> o \<Sigma>\<Sigma>_base_map (\<Sigma>\<Sigma>_base_map <id, dtor_J>))"
  show "eval_base \<circ> flat_base = ?K"
  apply(rule J.dtor_unfold_unique)
  unfolding F_map_comp o_assoc
  apply(subst o_assoc[symmetric], subst o_assoc[symmetric])
  unfolding dd_base_flat_base
  unfolding o_assoc[symmetric] \<Sigma>\<Sigma>_base.map_comp[symmetric] snd_convol
  unfolding flat_base_natural
  unfolding o_assoc eval_base ..
  (*  *)
  have A: "<eval_base, dtor_J o eval_base> = <id,dtor_J> o eval_base" by simp
  show "?K = eval_base \<circ> \<Sigma>\<Sigma>_base_map eval_base"
  apply(rule J.dtor_unfold_unique[symmetric])
  unfolding o_assoc[symmetric] map_prod_o_convol id_o
  unfolding F_map_comp o_assoc
  apply(subst o_assoc[symmetric]) unfolding dd_base_natural[symmetric]
  unfolding o_assoc[symmetric] \<Sigma>\<Sigma>_base.map_comp0[symmetric]
  unfolding o_assoc unfolding map_prod_o_convol unfolding convol_o
  unfolding o_assoc[symmetric] \<Sigma>\<Sigma>_base.map_comp0[symmetric] fst_convol \<Sigma>\<Sigma>_base.map_id0 o_id
  unfolding o_assoc eval_base unfolding A unfolding convol_o id_o
  apply(rule sym) apply(subst eval_base[symmetric])
  unfolding o_assoc[symmetric] \<Sigma>\<Sigma>_base.map_comp0[symmetric] convol_o id_o ..
qed


subsection{* The correspondence between coalgebras up to and coalgebras *}

(* This correspondence, and add_base the lemmas of this subsection, make
sense not only for (J,dtor_J,eval_base), but also for any dd_base-bialgebra *)

(* Coalgebra-up-to to coalgebra and vice versa: *)
definition cut\<Sigma>\<Sigma>_baseOc :: "('a \<Rightarrow> 'a \<Sigma>\<Sigma>_base F) \<Rightarrow> ('a \<Sigma>\<Sigma>_base \<Rightarrow> 'a \<Sigma>\<Sigma>_base F)"
where "cut\<Sigma>\<Sigma>_baseOc s \<equiv> F_map flat_base o dd_base o \<Sigma>\<Sigma>_base_map <leaf_base, s>"
definition c\<Sigma>\<Sigma>_baseOcut :: "('a \<Sigma>\<Sigma>_base \<Rightarrow> 'a \<Sigma>\<Sigma>_base F) \<Rightarrow> ('a \<Rightarrow> 'a \<Sigma>\<Sigma>_base F)"
where "c\<Sigma>\<Sigma>_baseOcut s' \<equiv> s' o leaf_base"

lemma c\<Sigma>\<Sigma>_baseOcut_cut\<Sigma>\<Sigma>_baseOc: "c\<Sigma>\<Sigma>_baseOcut (cut\<Sigma>\<Sigma>_baseOc s) = s"
unfolding c\<Sigma>\<Sigma>_baseOcut_def cut\<Sigma>\<Sigma>_baseOc_def
unfolding o_assoc[symmetric] unfolding leaf_base_natural
unfolding o_assoc apply(subst o_assoc[symmetric])
unfolding dd_base_leaf_base unfolding o_assoc F_map_comp[symmetric] flat_base_leaf_base
unfolding F_map_id id_o by simp

lemma cut\<Sigma>\<Sigma>_baseOc_inj: "cut\<Sigma>\<Sigma>_baseOc s1 = cut\<Sigma>\<Sigma>_baseOc s2 \<longleftrightarrow> s1 = s2"
by (metis c\<Sigma>\<Sigma>_baseOcut_cut\<Sigma>\<Sigma>_baseOc)

lemma c\<Sigma>\<Sigma>_baseOcut_surj: "\<exists> s'. c\<Sigma>\<Sigma>_baseOcut s' = s"
using c\<Sigma>\<Sigma>_baseOcut_cut\<Sigma>\<Sigma>_baseOc by(rule exI[of _ "cut\<Sigma>\<Sigma>_baseOc s"])

(* Morphism-up-to to morphism and vice versa: *)
(* The dd_base-ext_baseension of a function *)
definition extdd_base :: "('a \<Rightarrow> J) \<Rightarrow> ('a \<Sigma>\<Sigma>_base \<Rightarrow> J)"
where "extdd_base f \<equiv> eval_base o \<Sigma>\<Sigma>_base_map f"
(* The restriction of a function *)  term eval_base
definition restr :: "('a \<Sigma>\<Sigma>_base \<Rightarrow> J) \<Rightarrow> ('a \<Rightarrow> J)"
where "restr f' \<equiv> f' o leaf_base"

(* We think of extdd_base and restr as operating
extdd_base : Hom_dd_base(s,dtor_J) \<rightarrow> Hom(cut\<Sigma>\<Sigma>_baseOc s,dtor_J) and
restr : Hom(cut\<Sigma>\<Sigma>_baseOc s,dtor_J) \<rightarrow> Hom_dd_base(s,dtor_J), where
Hom(cut\<Sigma>\<Sigma>_baseOc s,dtor_J) is the set of coalgebra morphisms betwee cut\<Sigma>\<Sigma>_baseOc s and dtor_J and
Hom_dd_base(s,dtor_J) is the set of coalgebra up-to-dd_base-morphisms between s and dtor_J  *)

(* extdd_base is wedd_base-defined: *)
lemma extdd_base_mor:
assumes f:  "F_map (extdd_base f) o s = dtor_J o f"
shows "F_map (extdd_base f) o cut\<Sigma>\<Sigma>_baseOc s = dtor_J o (extdd_base f)"
proof-
  have AA: "eval_base ** F_map eval_base \<circ> (\<Sigma>\<Sigma>_base_map f ** F_map (\<Sigma>\<Sigma>_base_map f) \<circ> <leaf_base , s>) =
            <f , F_map eval_base \<circ> (F_map (\<Sigma>\<Sigma>_base_map f) \<circ> s)>"
  unfolding map_prod_o_convol unfolding leaf_base_natural o_assoc eval_base_leaf_base id_o  ..
  show ?thesis
  unfolding extdd_base_def
  unfolding o_assoc eval_base[symmetric]
  unfolding o_assoc[symmetric] \<Sigma>\<Sigma>_base.map_comp0[symmetric]
  unfolding convol_comp[symmetric] id_o
  unfolding f[symmetric, unfolded extdd_base_def]
  unfolding o_assoc
  apply(subst o_assoc[symmetric])
  unfolding F_map_comp o_assoc
  unfolding cut\<Sigma>\<Sigma>_baseOc_def
  unfolding o_assoc
  unfolding F_map_comp[symmetric] unfolding o_assoc[symmetric]
  unfolding flat_base_natural[symmetric]
  unfolding o_assoc F_map_comp
  apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
  unfolding dd_base_natural[symmetric]
  unfolding o_assoc unfolding F_map_comp[symmetric] eval_base_flat_base
  unfolding F_map_comp apply(subst o_assoc[symmetric])
  unfolding dd_base_natural[symmetric] unfolding o_assoc[symmetric] \<Sigma>\<Sigma>_base.map_comp0[symmetric]
  unfolding o_assoc[symmetric] AA[unfolded o_assoc[symmetric]] ..
qed

lemma mor_cut\<Sigma>\<Sigma>_baseOc_flat_base:
assumes f': "F_map f' o cut\<Sigma>\<Sigma>_baseOc s = dtor_J o f'"
shows "eval_base o \<Sigma>\<Sigma>_base_map f' = f' o flat_base"
proof(rule trans) (* this proof is clearly improvable: *)
  def h \<equiv> "dd_base o \<Sigma>\<Sigma>_base_map <id,cut\<Sigma>\<Sigma>_baseOc s>"
  have f'_id: "f' = f' o id" by simp
  show "eval_base \<circ> \<Sigma>\<Sigma>_base_map f' = dtor_unfold_J h"
  apply(rule J.dtor_unfold_unique, rule sym)
  unfolding o_assoc eval_base[symmetric]
  unfolding o_assoc[symmetric] \<Sigma>\<Sigma>_base.map_comp0[symmetric]
  unfolding convol_comp_id1[symmetric] unfolding f'[symmetric]
  apply(subst f'_id)
  unfolding o_assoc \<Sigma>\<Sigma>_base.map_comp
  apply(subst o_assoc[symmetric])
  unfolding o_assoc[symmetric] F_map_comp
  unfolding h_def apply(rule sym)
  unfolding o_assoc apply(subst o_assoc[symmetric])
  unfolding dd_base_natural[symmetric] unfolding o_assoc[symmetric]
  unfolding \<Sigma>\<Sigma>_base.map_comp0[symmetric] map_prod_o_convol ..
  (*  *)
  have AA: "<id , cut\<Sigma>\<Sigma>_baseOc s> = (flat_base ** F_map flat_base) o (id ** dd_base) o <leaf_base, \<Sigma>\<Sigma>_base_map <leaf_base , s>>"
  unfolding map_prod_o_convol o_assoc map_prod.comp cut\<Sigma>\<Sigma>_baseOc_def o_id flat_base_leaf_base ..
  have BB: "flat_base ** F_map flat_base \<circ> id ** dd_base \<circ> <leaf_base , \<Sigma>\<Sigma>_base_map <leaf_base , s>> = flat_base ** F_map flat_base \<circ> id ** dd_base \<circ> <\<Sigma>\<Sigma>_base_map leaf_base , \<Sigma>\<Sigma>_base_map <leaf_base , s>>"
  unfolding map_prod.comp unfolding map_prod_o_convol unfolding o_id unfolding flat_base_leaf_base leaf_base_flat_base ..
  show "dtor_unfold_J h = f' \<circ> flat_base"
  apply(rule J.dtor_unfold_unique[symmetric], rule sym)
  unfolding o_assoc f'[symmetric]
  unfolding F_map_comp o_assoc[symmetric]
  apply(rule arg_cong[of _ _ "op o (F_map f')"])
  unfolding h_def
  unfolding AA BB
  unfolding \<Sigma>\<Sigma>_base.map_comp0 apply(rule sym)
  unfolding o_assoc apply(subst o_assoc[symmetric])
  unfolding dd_base_natural
  unfolding o_assoc F_map_comp[symmetric]
  unfolding flat_base_assoc unfolding F_map_comp
  unfolding cut\<Sigma>\<Sigma>_baseOc_def o_assoc[symmetric] apply(rule arg_cong[of _ _ "op o (F_map flat_base)"])
  unfolding o_assoc
  unfolding o_assoc[symmetric] unfolding \<Sigma>\<Sigma>_base.map_comp0[symmetric] unfolding map_prod_o_convol id_o
  unfolding flat_base_natural[symmetric] unfolding o_assoc
  unfolding dd_base_flat_base[symmetric] unfolding o_assoc[symmetric] unfolding \<Sigma>\<Sigma>_base.map_comp0[symmetric]
  unfolding convol_o unfolding \<Sigma>\<Sigma>_base.map_comp0[symmetric] unfolding fst_convol ..
qed

(* restr is wedd_base-defined:  *)
lemma restr_mor:
assumes f': "F_map f' o cut\<Sigma>\<Sigma>_baseOc s = dtor_J o f'"
shows "F_map (extdd_base (restr f')) o s = dtor_J o restr f'"
unfolding extdd_base_def restr_def \<Sigma>\<Sigma>_base.map_comp0
unfolding o_assoc mor_cut\<Sigma>\<Sigma>_baseOc_flat_base[OF f']
unfolding o_assoc[symmetric] leaf_base_flat_base o_id
unfolding o_assoc f'[symmetric]
unfolding o_assoc[symmetric] c\<Sigma>\<Sigma>_baseOcut_cut\<Sigma>\<Sigma>_baseOc[unfolded c\<Sigma>\<Sigma>_baseOcut_def] ..

lemma extdd_base_restr:
assumes f': "F_map f' o cut\<Sigma>\<Sigma>_baseOc s = dtor_J o f'"
shows "extdd_base (restr f') = f'"
proof-
  have "f' = eval_base o \<Sigma>\<Sigma>_base_map f' o leaf_base"
  unfolding o_assoc[symmetric] leaf_base_natural
  unfolding o_assoc eval_base_leaf_base by simp
  also have "... = eval_base o \<Sigma>\<Sigma>_base_map (f' o leaf_base)"
  unfolding \<Sigma>\<Sigma>_base.map_comp0 o_assoc
  unfolding mor_cut\<Sigma>\<Sigma>_baseOc_flat_base[OF f'] unfolding o_assoc[symmetric] flat_base_leaf_base leaf_base_flat_base ..
  finally have A: "f' = eval_base o \<Sigma>\<Sigma>_base_map (f' o leaf_base)" .
  show ?thesis unfolding extdd_base_def restr_def A[symmetric] ..
qed

lemma restr_inj:
assumes f1': "F_map f1' o cut\<Sigma>\<Sigma>_baseOc s = dtor_J o f1'"
and f2': "F_map f2' o cut\<Sigma>\<Sigma>_baseOc s = dtor_J o f2'"
shows "restr f1' = restr f2' \<longleftrightarrow> f1' = f2'"
using extdd_base_restr[OF f1'] extdd_base_restr[OF f2'] by metis

lemma extdd_base_surj:
assumes f': "F_map f' o cut\<Sigma>\<Sigma>_baseOc s = dtor_J o f'"
shows "\<exists> f. extdd_base f = f'"
using extdd_base_restr[OF f'] by(rule exI[of _ "restr f'"])

lemma restr_extdd_base:
assumes f: "F_map (extdd_base f) o s = dtor_J o f"
shows "restr (extdd_base f) = f"
proof-
  have "dtor_J o f = F_map (extdd_base f) o s" using assms unfolding extdd_base_def by (rule sym)
  also have "... = dtor_J o restr (extdd_base f)"
  unfolding restr_def unfolding o_assoc extdd_base_mor[OF f, symmetric]
  unfolding o_assoc[symmetric] c\<Sigma>\<Sigma>_baseOcut_cut\<Sigma>\<Sigma>_baseOc[unfolded c\<Sigma>\<Sigma>_baseOcut_def] ..
  finally have "dtor_J o f = dtor_J \<circ> restr (extdd_base f)" .
  thus ?thesis unfolding dtor_J_o_inj by (rule sym)
qed

lemma extdd_base_inj:
assumes f1: "F_map (extdd_base f1) o s = dtor_J o f1"
and f2: "F_map (extdd_base f2) o s = dtor_J o f2"
shows "extdd_base f1 = extdd_base f2 \<longleftrightarrow> f1 = f2"
using restr_extdd_base[OF f1] restr_extdd_base[OF f2] by metis

lemma restr_surj:
assumes f: "F_map (extdd_base f) o s = dtor_J o f"
shows "\<exists> f'. restr f' = f"
using restr_extdd_base[OF f] by(rule exI[of _ "extdd_base f"])


subsection{* Coiteration up-to *}

definition "unfoldU_base s \<equiv> restr (dtor_unfold_J (cut\<Sigma>\<Sigma>_baseOc s))"

theorem unfoldU_base_pointfree:
"F_map (extdd_base (unfoldU_base s)) o s = dtor_J o unfoldU_base s"
unfolding unfoldU_base_def apply(rule restr_mor)
unfolding dtor_unfold_J_pointfree ..

theorem unfoldU_base: "F_map (extdd_base (unfoldU_base s)) (s a) = dtor_J (unfoldU_base s a)"
using unfoldU_base_pointfree unfolding o_def fun_eq_iff by(rule allE)

theorem unfoldU_base_ctor_J:
"ctor_J (F_map (extdd_base (unfoldU_base s)) (s a)) = unfoldU_base s a"
using unfoldU_base by (metis J.ctor_dtor)

theorem unfoldU_base_unique:
assumes "F_map (extdd_base f) o s = dtor_J o f"
shows "f = unfoldU_base s"
proof-
  note f = extdd_base_mor[OF assms]  note co = extdd_base_mor[OF unfoldU_base_pointfree]
  have A: "extdd_base f = extdd_base (unfoldU_base s)"
  proof(rule trans)
    show "extdd_base f = dtor_unfold_J (cut\<Sigma>\<Sigma>_baseOc s)" apply(rule J.dtor_unfold_unique) using f .
    show "dtor_unfold_J (cut\<Sigma>\<Sigma>_baseOc s) = extdd_base (unfoldU_base s)"
     apply(rule J.dtor_unfold_unique[symmetric]) using co .
  qed
  show ?thesis using A unfolding extdd_base_inj[OF assms unfoldU_base_pointfree] .
qed

lemma unfoldU_base_ctor_J_pointfree:
"ctor_J o F_map (extdd_base (unfoldU_base s)) o s = unfoldU_base s"
unfolding o_def fun_eq_iff by (subst unfoldU_base_ctor_J[symmetric]) (rule allI, rule refl)

(* Corecursion up to: *)
definition corecU_base :: "('a \<Rightarrow> (J + 'a) \<Sigma>\<Sigma>_base F) \<Rightarrow> 'a \<Rightarrow> J" where
"corecU_base s = unfoldU_base (case_sum (dd_base o leaf_base o <Inl, F_map Inl o dtor_J>) s) o Inr"

definition extddRec_base where
"extddRec_base f \<equiv> eval_base \<circ> \<Sigma>\<Sigma>_base_map (case_sum id f)"

lemma unfoldU_base_Inl:
"unfoldU_base (case_sum (dd_base \<circ> leaf_base \<circ> <Inl , F_map Inl \<circ> dtor_J>) s) o Inl = id"
(is "?L = ?R")
proof-
  have "?L = unfoldU_base (dd_base o leaf_base o <id, dtor_J>)"
  apply(rule unfoldU_base_unique)
  unfolding o_assoc unfoldU_base_pointfree[symmetric]
  unfolding o_assoc[symmetric] case_sum_o_inj extdd_base_def F_map_comp \<Sigma>\<Sigma>_base.map_comp0
  unfolding o_assoc apply(subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric],
                          subst o_assoc[symmetric], subst o_assoc[symmetric], subst o_assoc[symmetric])
  unfolding dd_base_natural[symmetric]
  apply(subst o_assoc[symmetric]) unfolding leaf_base_natural
  unfolding o_assoc[symmetric] map_prod_o_convol o_id ..
  also have "... = ?R"
  apply(rule sym, rule unfoldU_base_unique)
  unfolding extdd_base_def \<Sigma>\<Sigma>_base.map_id0 o_id dd_base_leaf_base
  unfolding o_assoc[symmetric] snd_convol
  unfolding o_assoc F_map_comp[symmetric] eval_base_leaf_base F_map_id id_o ..
  finally show ?thesis .
qed

theorem corecU_base_pointfree:
"F_map (extddRec_base (corecU_base s)) o s = dtor_J o corecU_base s" (is "?L = ?R")
unfolding corecU_base_def
unfolding o_assoc unfoldU_base_pointfree[symmetric] extddRec_base_def
unfolding o_assoc[symmetric] case_sum_o_inj
apply(subst unfoldU_base_Inl[symmetric, of s])
unfolding o_assoc case_sum_Inl_Inr_L extdd_base_def ..

theorem corecU_base:
"F_map (extddRec_base (corecU_base s)) (s a) = dtor_J (corecU_base s a)"
using corecU_base_pointfree unfolding o_def fun_eq_iff by(rule allE)


subsection{* Coinduction up-to *}

definition "cptdd_base R \<equiv> (\<Sigma>\<Sigma>_base_rel R ===> R) eval_base eval_base"

definition "cngdd_base R \<equiv> equivp R \<and> cptdd_base R"

lemma cngdd_base_Retr: "cngdd_base R \<Longrightarrow> cngdd_base (R \<sqinter> Retr R)"
  unfolding cngdd_base_def cptdd_base_def
  apply (erule conjE)
  apply (rule conjI[OF equivp_inf[OF _ equivp_retr]])
  apply assumption
  apply assumption
  apply (rule rel_funI)
  apply (frule predicate2D[OF \<Sigma>\<Sigma>_base_rel_inf])
  apply (erule inf2E)
  apply (rule inf2I)
  apply (erule rel_funE)
  apply assumption
  apply assumption
  apply (subst Retr_def)
  apply (subst eval_base_def)+
  apply (subst J.dtor_unfold)+
  unfolding F_rel_F_map_F_map Grp_def relcompp.simps[abs_def] conversep.simps[abs_def]
  apply auto
  unfolding eval_base_def[symmetric]
  apply (rule predicate2D[OF F_rel_mono])
  apply (rule predicate2I)
  apply (erule rel_funD)
  apply assumption
  apply (rule F_rel_\<Sigma>\<Sigma>_base_rel)
  unfolding \<Sigma>\<Sigma>_base_rel_\<Sigma>\<Sigma>_base_map_\<Sigma>\<Sigma>_base_map vimage2p_rel_prod vimage2p_id
  unfolding vimage2p_def Retr_def[symmetric]
  apply assumption
  done

(* The generated congruence: *)
definition "genCngdd_base R j1 j2 \<equiv> \<forall> R'. R \<le> R' \<and> cngdd_base R' \<longrightarrow> R' j1 j2"

lemma cngdd_base_genCngdd_base: "cngdd_base (genCngdd_base R)"
unfolding cngdd_base_def proof safe
  show "cptdd_base (genCngdd_base R)"
  unfolding cptdd_base_def rel_fun_def proof safe
    fix x y assume 1: "\<Sigma>\<Sigma>_base_rel (genCngdd_base R) x y"
    show "genCngdd_base R (eval_base x) (eval_base y)"
    unfolding genCngdd_base_def[abs_def] proof safe
      fix R' assume "R \<le> R'" and 2: "cngdd_base R'"
      hence "\<Sigma>\<Sigma>_base_rel R' x y" by (metis 1 \<Sigma>\<Sigma>_base.rel_mono_strong genCngdd_base_def)
      thus "R' (eval_base x) (eval_base y)" using 2 unfolding cngdd_base_def cptdd_base_def rel_fun_def by auto
    qed
  qed
qed(rule equivpI, unfold reflp_def symp_def transp_def genCngdd_base_def cngdd_base_def equivp_def, auto)

lemma
    genCngdd_base_refl[intro,simp]: "genCngdd_base R j j"
and genCngdd_base_sym[intro]: "genCngdd_base R j1 j2 \<Longrightarrow> genCngdd_base R j2 j1"
and genCngdd_base_trans[intro]: "\<lbrakk>genCngdd_base R j1 j2; genCngdd_base R j2 j3\<rbrakk> \<Longrightarrow> genCngdd_base R j1 j3"
using cngdd_base_genCngdd_base unfolding cngdd_base_def equivp_def by auto

lemma genCngdd_base_eval_base_rel_fun: "(\<Sigma>\<Sigma>_base_rel (genCngdd_base R) ===> genCngdd_base R) eval_base eval_base"
using cngdd_base_genCngdd_base unfolding cngdd_base_def cptdd_base_def by auto

lemma genCngdd_base_eval_base: "\<Sigma>\<Sigma>_base_rel (genCngdd_base R) x y \<Longrightarrow> genCngdd_base R (eval_base x) (eval_base y)"
using genCngdd_base_eval_base_rel_fun unfolding rel_fun_def by auto

lemma leq_genCngdd_base: "R \<le> genCngdd_base R"
and imp_genCngdd_base[intro]: "R j1 j2 \<Longrightarrow> genCngdd_base R j1 j2"
unfolding genCngdd_base_def[abs_def] by auto

lemma genCngdd_base_minimal: "\<lbrakk>R \<le> R'; cngdd_base R'\<rbrakk> \<Longrightarrow> genCngdd_base R \<le> R'"
unfolding genCngdd_base_def[abs_def] by (metis (lifting, no_types) predicate2I)

theorem coinductionU_genCngdd_base:
assumes "\<forall> a b. R a b \<longrightarrow> F_rel (genCngdd_base R) (dtor_J a) (dtor_J b)"
shows "R a b \<longrightarrow> a = b"
proof-
  let ?R' = "genCngdd_base R"
  have "R \<le> Retr ?R'" using assms unfolding Retr_def[abs_def] by auto
  hence "R \<le> ?R' \<sqinter> Retr ?R'" using leq_genCngdd_base by auto
  moreover have "cngdd_base (?R' \<sqinter> Retr ?R')" using cngdd_base_Retr[OF cngdd_base_genCngdd_base[of R]] .
  ultimately have "?R' \<le> ?R' \<sqinter> Retr ?R'" using genCngdd_base_minimal by metis
  hence "?R' \<le> Retr ?R'" by auto
  hence "?R' a b \<longrightarrow> a = b" unfolding Retr_def[abs_def] by (intro J.dtor_coinduct) auto
  thus ?thesis using leq_genCngdd_base by auto
qed

(* Since (J \<Sigma>\<Sigma>_base, eval_base) is an Eilenberg-Moore algebra (i.e., is compatible with
the monadic structure, it yields an algebra on the signature functor.
This is crucial for having suitable simplification rules. *)
definition alg\<Lambda>_base :: "J \<Sigma>_base \<Rightarrow> J" where
"alg\<Lambda>_base = eval_base o \<oo>\<pp>_base o \<Sigma>_base_map leaf_base"

theorem eval_base_comp_\<oo>\<pp>_base: "eval_base o \<oo>\<pp>_base = alg\<Lambda>_base o \<Sigma>_base_map eval_base"
unfolding alg\<Lambda>_base_def
unfolding o_assoc[symmetric] \<Sigma>_base.map_comp0[symmetric]
unfolding leaf_base_natural[symmetric] unfolding \<Sigma>_base.map_comp0
apply(rule sym) unfolding o_assoc apply(subst o_assoc[symmetric])
unfolding \<oo>\<pp>_base_natural
unfolding o_assoc eval_base_flat_base[symmetric]
apply(subst o_assoc[symmetric]) unfolding flat_base_commute[symmetric]
unfolding o_assoc[symmetric] \<Sigma>_base.map_comp0[symmetric] flat_base_leaf_base \<Sigma>_base.map_id0 o_id ..

theorem eval_base_\<oo>\<pp>_base: "eval_base (\<oo>\<pp>_base t) = alg\<Lambda>_base (\<Sigma>_base_map eval_base t)"
using eval_base_comp_\<oo>\<pp>_base unfolding o_def fun_eq_iff by (rule allE)

theorem eval_base_leaf_base': "eval_base (leaf_base j) = j"
using eval_base_leaf_base unfolding o_def fun_eq_iff id_def by (rule allE)

theorem dtor_J_alg\<Lambda>_base: "dtor_J o alg\<Lambda>_base = F_map eval_base o \<Lambda>_base o \<Sigma>_base_map <id, dtor_J>"
  unfolding alg\<Lambda>_base_def eval_base_def o_assoc dtor_unfold_J_pointfree \<Lambda>_base_dd_base
  unfolding o_assoc[symmetric] \<oo>\<pp>_base_natural[symmetric] \<Sigma>_base.map_comp0[symmetric] leaf_base_natural
  ..

theorem dtor_J_alg\<Lambda>_base': "dtor_J (alg\<Lambda>_base t) = F_map eval_base (\<Lambda>_base (\<Sigma>_base_map (<id, dtor_J>) t))"
  by (rule trans[OF o_eq_dest[OF dtor_J_alg\<Lambda>_base] o_apply])

theorem ctor_J_alg\<Lambda>_base: "alg\<Lambda>_base t = ctor_J (F_map eval_base (\<Lambda>_base (\<Sigma>_base_map (<id, dtor_J>) t)))"
  by (rule iffD1[OF J.dtor_inject trans[OF dtor_J_alg\<Lambda>_base' J.dtor_ctor[symmetric]]])

(* Customizing coinduction up-to: *)
definition "cpt\<Lambda>_base R \<equiv> (\<Sigma>_base_rel R ===> R) alg\<Lambda>_base alg\<Lambda>_base"

definition "cng\<Lambda>_base R \<equiv> equivp R \<and> cpt\<Lambda>_base R"

lemma cptdd_base_iff_cpt\<Lambda>_base: "cptdd_base R \<longleftrightarrow> cpt\<Lambda>_base R"
apply (rule iffI)
apply (unfold cpt\<Lambda>_base_def cptdd_base_def alg\<Lambda>_base_def o_assoc[symmetric]) [1]
apply (erule rel_funD[OF rel_funD[OF comp_transfer]])
apply transfer_prover

apply (unfold cpt\<Lambda>_base_def cptdd_base_def) [1]
unfolding rel_fun_def
apply (rule allI)+
apply (rule \<Sigma>\<Sigma>_base_rel_induct)
apply (simp only: eval_base_leaf_base')
unfolding eval_base_\<oo>\<pp>_base
apply (drule spec2)
apply (erule mp)
apply (rule iffD2[OF \<Sigma>_base_rel_\<Sigma>_base_map_\<Sigma>_base_map])
apply (subst vimage2p_def)
apply assumption
done

(* This is the definition of genCngdd we need to work with: *)
theorem genCngdd_base_def2: "genCngdd_base R j1 j2 \<longleftrightarrow> (\<forall> R'. R \<le> R' \<and> cng\<Lambda>_base R' \<longrightarrow> R' j1 j2)"
unfolding genCngdd_base_def cngdd_base_def cng\<Lambda>_base_def cptdd_base_iff_cpt\<Lambda>_base ..


subsection {* Incremental coinduction *}

interpretation I_base: Incremental where Retr = Retr and Cl = genCngdd_base
proof
  show "mono Retr" by (rule mono_retr)
next
  show "mono genCngdd_base" unfolding mono_def
  unfolding genCngdd_base_def[abs_def] by (smt order.trans predicate2I)
next
  fix r show "genCngdd_base (genCngdd_base r) = genCngdd_base r"
  by (metis cngdd_base_genCngdd_base genCngdd_base_minimal leq_genCngdd_base order_class.order.antisym)
next
  fix r show "r \<le> genCngdd_base r" by (metis leq_genCngdd_base)
next
  fix r assume "genCngdd_base r = r" thus "genCngdd_base (r \<sqinter> Retr r) = r \<sqinter> Retr r"
  by (metis antisym cngdd_base_Retr cngdd_base_genCngdd_base genCngdd_base_minimal
            inf.orderI inf_idem leq_genCngdd_base)
qed

definition ded_base where "ded_base r s \<equiv> I_base.ded r s"

theorems Ax = I_base.Ax'[unfolded ded_base_def[symmetric]]
theorems Split = I_base.Split[unfolded ded_base_def[symmetric]]
theorems Coind = I_base.Coind[unfolded ded_base_def[symmetric]]

theorem soundness_ded:
assumes "ded_base (op =) s"  shows "s \<le> (op =)"
unfolding gfp_Retr_eq[symmetric] apply(rule I_base.soundness_ded[unfolded ded_base_def[symmetric]] )
using assms unfolding gfp_Retr_eq[symmetric] ded_base_def .

unused_thms

end
