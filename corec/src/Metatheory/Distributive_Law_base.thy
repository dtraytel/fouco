header{* The initial distributive law *}

(*<*)
(* This is similar to Distributive_Law, but uses a particular law \<Lambda>_base: *)
(*>*)

theory Distributive_Law_base
imports FreeAlg_base
begin

definition \<Lambda>_base :: "('a * 'a F) \<Sigma>_base \<Rightarrow> 'a \<Sigma>\<Sigma>_base F"
where "\<Lambda>_base \<equiv> Rep_\<Sigma>_base o \<Sigma>_base_map (\<oo>\<pp>_base o Abs_\<Sigma>_base o F_map leaf_base o snd)"

lemma \<Lambda>_base_transfer[transfer_rule]:
  "(\<Sigma>_base_rel (rel_prod R (F_rel R)) ===> F_rel (\<Sigma>\<Sigma>_base_rel R)) \<Lambda>_base \<Lambda>_base"
  unfolding \<Lambda>_base_def by transfer_prover

theorem \<Lambda>_base_natural: "\<Lambda>_base o \<Sigma>_base_map (f ** F_map f) = F_map (\<Sigma>\<Sigma>_base_map f) o \<Lambda>_base"
  using \<Lambda>_base_transfer[of "BNF_Def.Grp UNIV f"]
  unfolding \<Sigma>_base.rel_Grp F_rel_Grp prod.rel_Grp \<Sigma>\<Sigma>_base.rel_Grp
  unfolding Grp_def rel_fun_def by auto

end