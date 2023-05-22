header{* The integration of a new operation in the up-to setting *}

theory Binary_Tree_Integrate_New_Op1
imports Binary_Tree_Op_Input1
begin


subsection{* The assumptions *}

(*
(* The operation that creates the new distributive law, since its definition splits
trough a natural transformation ll, which will be defined in More_Corec_Upto1 as follows: *)
definition alg\<rho>1 :: "J K1 \<Rightarrow> J" where
"alg\<rho>1 = unfoldU0 (\<rho>1 o K1_map <id, dtor_J>)"
*)

lemma \<rho>1_natural: "\<rho>1 o K1_map (f ** F_map f) = F_map (\<Sigma>\<Sigma>1_map f) o \<rho>1"
  using \<rho>1_transfer[of "BNF_Def.Grp UNIV f"]
  unfolding F_rel_Grp \<Sigma>\<Sigma>1.rel_Grp K1.rel_Grp prod.rel_Grp
  unfolding Grp_def rel_fun_def by auto

subsection{* The integration *}

definition embL1 :: "'a \<Sigma>\<Sigma>0 \<Rightarrow> 'a \<Sigma>\<Sigma>1" where
"embL1 \<equiv> ext0 (\<oo>\<pp>1 o Abs_\<Sigma>1 o Inl) leaf1"

definition embR1 :: "('a K1) \<Sigma>\<Sigma>0 \<Rightarrow> 'a \<Sigma>\<Sigma>1" where
"embR1 \<equiv> ext0 (\<oo>\<pp>1 o Abs_\<Sigma>1 o Inl) (\<oo>\<pp>1 o \<Sigma>1_map leaf1 o Abs_\<Sigma>1 o Inr)"

definition \<Lambda>1 :: "('a \<times> 'a F) \<Sigma>1 \<Rightarrow> 'a \<Sigma>\<Sigma>1 F" where
"\<Lambda>1 = case_sum (F_map embL1 o \<Lambda>0) \<rho>1 o Rep_\<Sigma>1"

lemma embL1_transfer[transfer_rule]:
  "(\<Sigma>\<Sigma>0_rel R ===> \<Sigma>\<Sigma>1_rel R) embL1 embL1"
  unfolding embL1_def ext0_alt by transfer_prover

lemma embR1_transfer[transfer_rule]:
  "(\<Sigma>\<Sigma>0_rel (K1_rel R) ===> \<Sigma>\<Sigma>1_rel R) embR1 embR1"
  unfolding embR1_def ext0_alt by transfer_prover

lemma \<Lambda>1_transfer[transfer_rule]:
  "(\<Sigma>1_rel (rel_prod R (F_rel R)) ===> F_rel (\<Sigma>\<Sigma>1_rel R)) \<Lambda>1 \<Lambda>1"
  unfolding \<Lambda>1_def by transfer_prover

lemma \<Lambda>1_natural: "\<Lambda>1 o \<Sigma>1_map (f ** F_map f) = F_map (\<Sigma>\<Sigma>1_map f) o \<Lambda>1"
  using \<Lambda>1_transfer[of "BNF_Def.Grp UNIV f"]
  unfolding F_rel_Grp \<Sigma>\<Sigma>1.rel_Grp \<Sigma>1.rel_Grp prod.rel_Grp
  unfolding Grp_def rel_fun_def by auto

lemma embL1_natural: "embL1 \<circ> \<Sigma>\<Sigma>0_map f = \<Sigma>\<Sigma>1_map f \<circ> embL1"
  using embL1_transfer[of "BNF_Def.Grp UNIV f"]
  unfolding \<Sigma>\<Sigma>0.rel_Grp \<Sigma>\<Sigma>1.rel_Grp
  unfolding Grp_def rel_fun_def by auto

lemma embR1_natural: "embR1 \<circ> \<Sigma>\<Sigma>0_map (K1_map f) = \<Sigma>\<Sigma>1_map f \<circ> embR1"
  using embR1_transfer[of "BNF_Def.Grp UNIV f"]
  unfolding \<Sigma>\<Sigma>0.rel_Grp K1.rel_Grp \<Sigma>\<Sigma>1.rel_Grp
  unfolding Grp_def rel_fun_def by auto

lemma \<Lambda>1_Inl: "\<Lambda>1 o Abs_\<Sigma>1 o Inl = F_map embL1 o \<Lambda>0"
  and \<Lambda>1_Inr: "\<Lambda>1 o Abs_\<Sigma>1 o Inr = \<rho>1"
unfolding \<Lambda>1_def o_assoc[symmetric] Rep_\<Sigma>1_o_Abs_\<Sigma>1 o_id by auto

lemma embL1_leaf0: "embL1 \<circ> leaf0 = leaf1"
unfolding embL1_def ext0_comp_leaf0 ..

lemma embL1_\<oo>\<pp>0: "embL1 \<circ> \<oo>\<pp>0 = \<oo>\<pp>1 \<circ> Abs_\<Sigma>1 \<circ> Inl \<circ> \<Sigma>0_map embL1"
unfolding embL1_def ext0_commute ..

lemma embR1_leaf0: "embR1 \<circ> leaf0 = \<oo>\<pp>1 \<circ> Abs_\<Sigma>1 \<circ> Inr \<circ> K1_map leaf1"
unfolding embR1_def ext0_comp_leaf0
unfolding o_assoc[symmetric] Abs_\<Sigma>1_natural map_sum_Inr ..

lemma embR1_\<oo>\<pp>0: "embR1 \<circ> \<oo>\<pp>0 = \<oo>\<pp>1 \<circ> Abs_\<Sigma>1 \<circ>  Inl \<circ> \<Sigma>0_map embR1"
unfolding embR1_def ext0_commute ..

end