header {* The fixed behavior BNF *}

theory Stream_Behavior_BNF
imports Stream_Input0
begin

codatatype J = ctor "J F"

abbreviation F_map where "F_map \<equiv> map_pre_J"
abbreviation F_rel where "F_rel \<equiv> rel_pre_J"
abbreviation F_set where "F_set \<equiv> set_pre_J"

lemmas F_map_comp = pre_J.map_comp0
lemmas F_map_id = pre_J.map_id0
lemmas F_map_transfer = pre_J.map_transfer
lemmas F_rel_Grp = pre_J.rel_Grp
lemmas F_rel_compp = pre_J.rel_compp
lemmas F_rel_conversep = pre_J.rel_conversep
lemmas F_rel_eq = pre_J.rel_eq
lemmas F_rel_flip = pre_J.rel_flip
lemmas F_rel_mono = pre_J.rel_mono

declare F_map_transfer[transfer_rule]
declare J.dtor_unfold_transfer[transfer_rule]

lemma dtor_J_o_inj:
"dtor_J o f = dtor_J o g \<longleftrightarrow> f = g"
unfolding o_def fun_eq_iff by (metis J.ctor_dtor)

lemma ctor_J_o_inj:
"ctor_J o f = ctor_J o g \<longleftrightarrow> f = g"
unfolding o_def fun_eq_iff by (metis J.dtor_ctor)

lemma dtor_unfold_J_pointfree: "dtor_J o (dtor_unfold_J s) = F_map (dtor_unfold_J s) o s"
by (rule ext) (unfold o_apply J.dtor_unfold, rule refl)

lemma dtor_J_ctor_pointfree: "dtor_J o ctor_J = id"
unfolding o_def J.dtor_ctor id_def ..

lemma ctor_dtor_J_pointfree: "ctor_J o dtor_J = id"
unfolding o_def J.ctor_dtor id_def ..

lemma convol_ctor_J_dtor_J: "<ctor_J , id> = <id, dtor_J> o ctor_J"
unfolding convol_o id_o o_id dtor_J_ctor_pointfree ..

definition "Retr R a b = F_rel R (dtor_J a) (dtor_J b)"

lemma reflp_Retr: "reflp R \<Longrightarrow> reflp (Retr R)"
  by (metis (full_types) Retr_def F_rel_eq F_rel_mono predicate2I reflpD reflpI rev_predicate2D)

lemma symp_Retr: "symp R \<Longrightarrow> symp (Retr R)"
  unfolding Retr_def[abs_def] symp_iff
  apply (subst fun_eq_iff)+
  apply (subst conversep_iff)
  apply (subst conversep_conversep[symmetric, of R])
  apply (subst F_rel_flip)
  apply simp
  done

lemma trans_Retr: "transp R \<Longrightarrow> transp (Retr R)"
   unfolding Retr_def[abs_def] transp_iff
   apply (rule predicate2I)
   apply (erule relcomppE)
   apply (erule rev_predicate2D[OF _ F_rel_mono, rotated])
   apply (subst F_rel_compp)
   apply auto
   done

lemma equivp_retr: "equivp R \<Longrightarrow> equivp (Retr R)"
  by (metis equivpE equivpI reflp_Retr symp_Retr trans_Retr)

lemma mono_retr: "mono Retr"
  unfolding mono_def by safe (simp only: Retr_def predicate2D[OF F_rel_mono])

lemma gfp_Retr_eq: "gfp Retr = (op =)"
apply(rule order_class.antisym)
  apply(rule J.dtor_rel_coinduct) unfolding Retr_def[symmetric] gfp_unfold[OF mono_retr, symmetric]
  apply simp
  apply(rule gfp_upperbound) unfolding Retr_def[abs_def] by (auto simp: F_rel_eq)


lemma F_rel_F_map_F_map: "F_rel R (F_map f x) (F_map g y) =
  F_rel (BNF_Def.Grp UNIV f OO R OO (BNF_Def.Grp UNIV g)^--1) x y"
  unfolding F_rel_compp F_rel_conversep relcompp.simps conversep.simps F_rel_Grp
  apply (intro iffI exI conjI GrpI)
  apply (rule refl)
  apply (rule refl)
  apply (rule refl)
  apply (rule CollectI)
  apply (rule subset_UNIV)
  apply (rule refl)
  apply (rule refl)
  apply assumption
  apply (rule refl)
  apply (rule refl)
  apply (rule refl)
  apply (rule CollectI)
  apply (rule subset_UNIV)
  apply (elim exE conjE GrpE)
  apply hypsubst
  apply assumption
  done

end