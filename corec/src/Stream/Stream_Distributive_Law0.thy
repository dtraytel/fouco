header{* The initial distributive law *}

(*<*)
(* This is similar to Distributive_Law, but uses a particular law \<Lambda>0: *)
(*>*)

theory Stream_Distributive_Law0
imports Stream_FreeAlg0
begin

definition \<Lambda>0 :: "('a * 'a F) \<Sigma>0 \<Rightarrow> 'a \<Sigma>\<Sigma>0 F"
where "\<Lambda>0 \<equiv> Rep_\<Sigma>0 o \<Sigma>0_map (\<oo>\<pp>0 o Abs_\<Sigma>0 o F_map leaf0 o snd)"

lemma \<Lambda>0_transfer[transfer_rule]:
  "(\<Sigma>0_rel (rel_prod R (F_rel R)) ===> F_rel (\<Sigma>\<Sigma>0_rel R)) \<Lambda>0 \<Lambda>0"
  unfolding \<Lambda>0_def by transfer_prover

theorem \<Lambda>0_natural: "\<Lambda>0 o \<Sigma>0_map (f ** F_map f) = F_map (\<Sigma>\<Sigma>0_map f) o \<Lambda>0"
  using \<Lambda>0_transfer[of "BNF_Def.Grp UNIV f"]
  unfolding \<Sigma>0.rel_Grp F_rel_Grp prod.rel_Grp \<Sigma>\<Sigma>0.rel_Grp
  unfolding Grp_def rel_fun_def by auto

end