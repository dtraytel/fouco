header{* The integration of a new operation in the up-to setting *}

theory Stream_Integrate_New_Op2
imports Stream_Op_Input2
begin


subsection{* The assumptions *}

(*
(* The operation that creates the new distributive law, since its definition splits
trough a natural transformation ll, which will be defined in More_Corec_Upto2 as follows: *)
definition alg\<rho>2 :: "J K2 \<Rightarrow> J" where
"alg\<rho>2 = unfoldU1 (\<rho>2 o K2_map <id, dtor_J>)"
*)

lemma \<rho>2_natural: "\<rho>2 o K2_map (f ** F_map f) = F_map (\<Sigma>\<Sigma>2_map f) o \<rho>2"
  using \<rho>2_transfer[of "BNF_Def.Grp UNIV f"]
  unfolding F_rel_Grp \<Sigma>\<Sigma>2.rel_Grp K2.rel_Grp prod.rel_Grp
  unfolding Grp_def rel_fun_def by auto

subsection{* The integration *}

definition embL2 :: "'a \<Sigma>\<Sigma>1 \<Rightarrow> 'a \<Sigma>\<Sigma>2" where
"embL2 \<equiv> ext1 (\<oo>\<pp>2 o Abs_\<Sigma>2 o Inl) leaf2"

definition embR2 :: "('a K2) \<Sigma>\<Sigma>1 \<Rightarrow> 'a \<Sigma>\<Sigma>2" where
"embR2 \<equiv> ext1 (\<oo>\<pp>2 o Abs_\<Sigma>2 o Inl) (\<oo>\<pp>2 o \<Sigma>2_map leaf2 o Abs_\<Sigma>2 o Inr)"

definition \<Lambda>2 :: "('a \<times> 'a F) \<Sigma>2 \<Rightarrow> 'a \<Sigma>\<Sigma>2 F" where
"\<Lambda>2 = case_sum (F_map embL2 o \<Lambda>1) \<rho>2 o Rep_\<Sigma>2"

lemma embL2_transfer[transfer_rule]:
  "(\<Sigma>\<Sigma>1_rel R ===> \<Sigma>\<Sigma>2_rel R) embL2 embL2"
  unfolding embL2_def ext1_alt by transfer_prover

lemma embR2_transfer[transfer_rule]:
  "(\<Sigma>\<Sigma>1_rel (K2_rel R) ===> \<Sigma>\<Sigma>2_rel R) embR2 embR2"
  unfolding embR2_def ext1_alt by transfer_prover

lemma \<Lambda>2_transfer[transfer_rule]:
  "(\<Sigma>2_rel (rel_prod R (F_rel R)) ===> F_rel (\<Sigma>\<Sigma>2_rel R)) \<Lambda>2 \<Lambda>2"
  unfolding \<Lambda>2_def by transfer_prover

lemma \<Lambda>2_natural: "\<Lambda>2 o \<Sigma>2_map (f ** F_map f) = F_map (\<Sigma>\<Sigma>2_map f) o \<Lambda>2"
  using \<Lambda>2_transfer[of "BNF_Def.Grp UNIV f"]
  unfolding F_rel_Grp \<Sigma>\<Sigma>2.rel_Grp \<Sigma>2.rel_Grp prod.rel_Grp
  unfolding Grp_def rel_fun_def by auto

lemma embL2_natural: "embL2 \<circ> \<Sigma>\<Sigma>1_map f = \<Sigma>\<Sigma>2_map f \<circ> embL2"
  using embL2_transfer[of "BNF_Def.Grp UNIV f"]
  unfolding \<Sigma>\<Sigma>1.rel_Grp \<Sigma>\<Sigma>2.rel_Grp
  unfolding Grp_def rel_fun_def by auto

lemma embR2_natural: "embR2 \<circ> \<Sigma>\<Sigma>1_map (K2_map f) = \<Sigma>\<Sigma>2_map f \<circ> embR2"
  using embR2_transfer[of "BNF_Def.Grp UNIV f"]
  unfolding \<Sigma>\<Sigma>1.rel_Grp K2.rel_Grp \<Sigma>\<Sigma>2.rel_Grp
  unfolding Grp_def rel_fun_def by auto

lemma \<Lambda>2_Inl: "\<Lambda>2 o Abs_\<Sigma>2 o Inl = F_map embL2 o \<Lambda>1"
  and \<Lambda>2_Inr: "\<Lambda>2 o Abs_\<Sigma>2 o Inr = \<rho>2"
unfolding \<Lambda>2_def o_assoc[symmetric] Rep_\<Sigma>2_o_Abs_\<Sigma>2 o_id by auto

lemma embL2_leaf1: "embL2 \<circ> leaf1 = leaf2"
unfolding embL2_def ext1_comp_leaf1 ..

lemma embL2_\<oo>\<pp>1: "embL2 \<circ> \<oo>\<pp>1 = \<oo>\<pp>2 \<circ> Abs_\<Sigma>2 \<circ> Inl \<circ> \<Sigma>1_map embL2"
unfolding embL2_def ext1_commute ..

lemma embR2_leaf1: "embR2 \<circ> leaf1 = \<oo>\<pp>2 \<circ> Abs_\<Sigma>2 \<circ> Inr \<circ> K2_map leaf2"
unfolding embR2_def ext1_comp_leaf1
unfolding o_assoc[symmetric] Abs_\<Sigma>2_natural map_sum_Inr ..

lemma embR2_\<oo>\<pp>1: "embR2 \<circ> \<oo>\<pp>1 = \<oo>\<pp>2 \<circ> Abs_\<Sigma>2 \<circ>  Inl \<circ> \<Sigma>1_map embR2"
unfolding embR2_def ext1_commute ..

end