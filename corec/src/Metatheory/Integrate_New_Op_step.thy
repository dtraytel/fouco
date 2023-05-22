header{* The integration of a new operation in the up-to setting *}

theory Integrate_New_Op_step
imports Op_Input_step
begin


subsection{* The assumptions *}

(*
(* The operation that creates the new distributive law, since its definition splits
trough a natural transformation ll, which will be defined in More_Corec_Upto_step as follows: *)
definition alg\<rho>_step :: "J K_step \<Rightarrow> J" where
"alg\<rho>_step = unfoldU_base (\<rho>_step o K_step_map <id, dtor_J>)"
*)

lemma \<rho>_step_natural: "\<rho>_step o K_step_map (f ** F_map f) = F_map (\<Sigma>\<Sigma>_step_map f) o \<rho>_step"
  using \<rho>_step_transfer[of "BNF_Def.Grp UNIV f"]
  unfolding F_rel_Grp \<Sigma>\<Sigma>_step.rel_Grp K_step.rel_Grp prod.rel_Grp
  unfolding Grp_def rel_fun_def by auto

subsection{* The integration *}

definition embL_step :: "'a \<Sigma>\<Sigma>_base \<Rightarrow> 'a \<Sigma>\<Sigma>_step" where
"embL_step \<equiv> ext_base (\<oo>\<pp>_step o Abs_\<Sigma>_step o Inl) leaf_step"

definition embR_step :: "('a K_step) \<Sigma>\<Sigma>_base \<Rightarrow> 'a \<Sigma>\<Sigma>_step" where
"embR_step \<equiv> ext_base (\<oo>\<pp>_step o Abs_\<Sigma>_step o Inl) (\<oo>\<pp>_step o \<Sigma>_step_map leaf_step o Abs_\<Sigma>_step o Inr)"

definition \<Lambda>_step :: "('a \<times> 'a F) \<Sigma>_step \<Rightarrow> 'a \<Sigma>\<Sigma>_step F" where
"\<Lambda>_step = case_sum (F_map embL_step o \<Lambda>_base) \<rho>_step o Rep_\<Sigma>_step"

lemma embL_step_transfer[transfer_rule]:
  "(\<Sigma>\<Sigma>_base_rel R ===> \<Sigma>\<Sigma>_step_rel R) embL_step embL_step"
  unfolding embL_step_def ext_base_alt by transfer_prover

lemma embR_step_transfer[transfer_rule]:
  "(\<Sigma>\<Sigma>_base_rel (K_step_rel R) ===> \<Sigma>\<Sigma>_step_rel R) embR_step embR_step"
  unfolding embR_step_def ext_base_alt by transfer_prover

lemma \<Lambda>_step_transfer[transfer_rule]:
  "(\<Sigma>_step_rel (rel_prod R (F_rel R)) ===> F_rel (\<Sigma>\<Sigma>_step_rel R)) \<Lambda>_step \<Lambda>_step"
  unfolding \<Lambda>_step_def by transfer_prover

lemma \<Lambda>_step_natural: "\<Lambda>_step o \<Sigma>_step_map (f ** F_map f) = F_map (\<Sigma>\<Sigma>_step_map f) o \<Lambda>_step"
  using \<Lambda>_step_transfer[of "BNF_Def.Grp UNIV f"]
  unfolding F_rel_Grp \<Sigma>\<Sigma>_step.rel_Grp \<Sigma>_step.rel_Grp prod.rel_Grp
  unfolding Grp_def rel_fun_def by auto

lemma embL_step_natural: "embL_step \<circ> \<Sigma>\<Sigma>_base_map f = \<Sigma>\<Sigma>_step_map f \<circ> embL_step"
  using embL_step_transfer[of "BNF_Def.Grp UNIV f"]
  unfolding \<Sigma>\<Sigma>_base.rel_Grp \<Sigma>\<Sigma>_step.rel_Grp
  unfolding Grp_def rel_fun_def by auto

lemma embR_step_natural: "embR_step \<circ> \<Sigma>\<Sigma>_base_map (K_step_map f) = \<Sigma>\<Sigma>_step_map f \<circ> embR_step"
  using embR_step_transfer[of "BNF_Def.Grp UNIV f"]
  unfolding \<Sigma>\<Sigma>_base.rel_Grp K_step.rel_Grp \<Sigma>\<Sigma>_step.rel_Grp
  unfolding Grp_def rel_fun_def by auto

lemma \<Lambda>_step_Inl: "\<Lambda>_step o Abs_\<Sigma>_step o Inl = F_map embL_step o \<Lambda>_base"
  and \<Lambda>_step_Inr: "\<Lambda>_step o Abs_\<Sigma>_step o Inr = \<rho>_step"
unfolding \<Lambda>_step_def o_assoc[symmetric] Rep_\<Sigma>_step_o_Abs_\<Sigma>_step o_id by auto

lemma embL_step_leaf_base: "embL_step \<circ> leaf_base = leaf_step"
unfolding embL_step_def ext_base_comp_leaf_base ..

lemma embL_step_\<oo>\<pp>_base: "embL_step \<circ> \<oo>\<pp>_base = \<oo>\<pp>_step \<circ> Abs_\<Sigma>_step \<circ> Inl \<circ> \<Sigma>_base_map embL_step"
unfolding embL_step_def ext_base_commute ..

lemma embR_step_leaf_base: "embR_step \<circ> leaf_base = \<oo>\<pp>_step \<circ> Abs_\<Sigma>_step \<circ> Inr \<circ> K_step_map leaf_step"
unfolding embR_step_def ext_base_comp_leaf_base
unfolding o_assoc[symmetric] Abs_\<Sigma>_step_natural map_sum_Inr ..

lemma embR_step_\<oo>\<pp>_base: "embR_step \<circ> \<oo>\<pp>_base = \<oo>\<pp>_step \<circ> Abs_\<Sigma>_step \<circ>  Inl \<circ> \<Sigma>_base_map embR_step"
unfolding embR_step_def ext_base_commute ..

end