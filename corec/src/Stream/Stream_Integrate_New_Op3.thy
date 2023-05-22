header{* The integration of a new operation in the up-to setting *}

theory Stream_Integrate_New_Op3
imports Stream_Op_Input3
begin


subsection{* The assumptions *}

(*
(* The operation that creates the new distributive law, since its definition splits
trough a natural transformation ll, which will be defined in More_Corec_Upto3 as follows: *)
definition alg\<rho>3 :: "J K3 \<Rightarrow> J" where
"alg\<rho>3 = unfoldU2 (\<rho>3 o K3_map <id, dtor_J>)"
*)

lemma \<rho>3_natural: "\<rho>3 o K3_map (f ** F_map f) = F_map (\<Sigma>\<Sigma>3_map f) o \<rho>3"
  using \<rho>3_transfer[of "BNF_Def.Grp UNIV f"]
  unfolding F_rel_Grp \<Sigma>\<Sigma>3.rel_Grp K3.rel_Grp prod.rel_Grp
  unfolding Grp_def rel_fun_def by auto

subsection{* The integration *}

definition embL3 :: "'a \<Sigma>\<Sigma>2 \<Rightarrow> 'a \<Sigma>\<Sigma>3" where
"embL3 \<equiv> ext2 (\<oo>\<pp>3 o Abs_\<Sigma>3 o Inl) leaf3"

definition embR3 :: "('a K3) \<Sigma>\<Sigma>2 \<Rightarrow> 'a \<Sigma>\<Sigma>3" where
"embR3 \<equiv> ext2 (\<oo>\<pp>3 o Abs_\<Sigma>3 o Inl) (\<oo>\<pp>3 o \<Sigma>3_map leaf3 o Abs_\<Sigma>3 o Inr)"

definition \<Lambda>3 :: "('a \<times> 'a F) \<Sigma>3 \<Rightarrow> 'a \<Sigma>\<Sigma>3 F" where
"\<Lambda>3 = case_sum (F_map embL3 o \<Lambda>2) \<rho>3 o Rep_\<Sigma>3"

lemma embL3_transfer[transfer_rule]:
  "(\<Sigma>\<Sigma>2_rel R ===> \<Sigma>\<Sigma>3_rel R) embL3 embL3"
  unfolding embL3_def ext2_alt by transfer_prover

lemma embR3_transfer[transfer_rule]:
  "(\<Sigma>\<Sigma>2_rel (K3_rel R) ===> \<Sigma>\<Sigma>3_rel R) embR3 embR3"
  unfolding embR3_def ext2_alt by transfer_prover

lemma \<Lambda>3_transfer[transfer_rule]:
  "(\<Sigma>3_rel (rel_prod R (F_rel R)) ===> F_rel (\<Sigma>\<Sigma>3_rel R)) \<Lambda>3 \<Lambda>3"
  unfolding \<Lambda>3_def by transfer_prover

lemma \<Lambda>3_natural: "\<Lambda>3 o \<Sigma>3_map (f ** F_map f) = F_map (\<Sigma>\<Sigma>3_map f) o \<Lambda>3"
  using \<Lambda>3_transfer[of "BNF_Def.Grp UNIV f"]
  unfolding F_rel_Grp \<Sigma>\<Sigma>3.rel_Grp \<Sigma>3.rel_Grp prod.rel_Grp
  unfolding Grp_def rel_fun_def by auto

lemma embL3_natural: "embL3 \<circ> \<Sigma>\<Sigma>2_map f = \<Sigma>\<Sigma>3_map f \<circ> embL3"
  using embL3_transfer[of "BNF_Def.Grp UNIV f"]
  unfolding \<Sigma>\<Sigma>2.rel_Grp \<Sigma>\<Sigma>3.rel_Grp
  unfolding Grp_def rel_fun_def by auto

lemma embR3_natural: "embR3 \<circ> \<Sigma>\<Sigma>2_map (K3_map f) = \<Sigma>\<Sigma>3_map f \<circ> embR3"
  using embR3_transfer[of "BNF_Def.Grp UNIV f"]
  unfolding \<Sigma>\<Sigma>2.rel_Grp K3.rel_Grp \<Sigma>\<Sigma>3.rel_Grp
  unfolding Grp_def rel_fun_def by auto

lemma \<Lambda>3_Inl: "\<Lambda>3 o Abs_\<Sigma>3 o Inl = F_map embL3 o \<Lambda>2"
  and \<Lambda>3_Inr: "\<Lambda>3 o Abs_\<Sigma>3 o Inr = \<rho>3"
unfolding \<Lambda>3_def o_assoc[symmetric] Rep_\<Sigma>3_o_Abs_\<Sigma>3 o_id by auto

lemma embL3_leaf2: "embL3 \<circ> leaf2 = leaf3"
unfolding embL3_def ext2_comp_leaf2 ..

lemma embL3_\<oo>\<pp>2: "embL3 \<circ> \<oo>\<pp>2 = \<oo>\<pp>3 \<circ> Abs_\<Sigma>3 \<circ> Inl \<circ> \<Sigma>2_map embL3"
unfolding embL3_def ext2_commute ..

lemma embR3_leaf2: "embR3 \<circ> leaf2 = \<oo>\<pp>3 \<circ> Abs_\<Sigma>3 \<circ> Inr \<circ> K3_map leaf3"
unfolding embR3_def ext2_comp_leaf2
unfolding o_assoc[symmetric] Abs_\<Sigma>3_natural map_sum_Inr ..

lemma embR3_\<oo>\<pp>2: "embR3 \<circ> \<oo>\<pp>2 = \<oo>\<pp>3 \<circ> Abs_\<Sigma>3 \<circ>  Inl \<circ> \<Sigma>2_map embR3"
unfolding embR3_def ext2_commute ..

end