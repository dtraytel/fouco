header{* The integration of a new operation in the up-to setting *}

theory Stream_Integrate_New_Op8
imports Stream_Op_Input8
begin


subsection{* The assumptions *}

(*
(* The operation that creates the new distributive law, since its definition splits
trough a natural transformation ll, which will be defined in More_Corec_Upto8 as follows: *)
definition alg\<rho>8 :: "J K8 \<Rightarrow> J" where
"alg\<rho>8 = unfoldU7 (\<rho>8 o K8_map <id, dtor_J>)"
*)

lemma \<rho>8_natural: "\<rho>8 o K8_map (f ** F_map f) = F_map (\<Sigma>\<Sigma>8_map f) o \<rho>8"
  using \<rho>8_transfer[of "BNF_Def.Grp UNIV f"]
  unfolding F_rel_Grp \<Sigma>\<Sigma>8.rel_Grp K8.rel_Grp prod.rel_Grp
  unfolding Grp_def rel_fun_def by auto

subsection{* The integration *}

definition embL8 :: "'a \<Sigma>\<Sigma>7 \<Rightarrow> 'a \<Sigma>\<Sigma>8" where
"embL8 \<equiv> ext7 (\<oo>\<pp>8 o Abs_\<Sigma>8 o Inl) leaf8"

definition embR8 :: "('a K8) \<Sigma>\<Sigma>7 \<Rightarrow> 'a \<Sigma>\<Sigma>8" where
"embR8 \<equiv> ext7 (\<oo>\<pp>8 o Abs_\<Sigma>8 o Inl) (\<oo>\<pp>8 o \<Sigma>8_map leaf8 o Abs_\<Sigma>8 o Inr)"

definition \<Lambda>8 :: "('a \<times> 'a F) \<Sigma>8 \<Rightarrow> 'a \<Sigma>\<Sigma>8 F" where
"\<Lambda>8 = case_sum (F_map embL8 o \<Lambda>7) \<rho>8 o Rep_\<Sigma>8"

lemma embL8_transfer[transfer_rule]:
  "(\<Sigma>\<Sigma>7_rel R ===> \<Sigma>\<Sigma>8_rel R) embL8 embL8"
  unfolding embL8_def ext7_alt by transfer_prover

lemma embR8_transfer[transfer_rule]:
  "(\<Sigma>\<Sigma>7_rel (K8_rel R) ===> \<Sigma>\<Sigma>8_rel R) embR8 embR8"
  unfolding embR8_def ext7_alt by transfer_prover

lemma \<Lambda>8_transfer[transfer_rule]:
  "(\<Sigma>8_rel (rel_prod R (F_rel R)) ===> F_rel (\<Sigma>\<Sigma>8_rel R)) \<Lambda>8 \<Lambda>8"
  unfolding \<Lambda>8_def by transfer_prover

lemma \<Lambda>8_natural: "\<Lambda>8 o \<Sigma>8_map (f ** F_map f) = F_map (\<Sigma>\<Sigma>8_map f) o \<Lambda>8"
  using \<Lambda>8_transfer[of "BNF_Def.Grp UNIV f"]
  unfolding F_rel_Grp \<Sigma>\<Sigma>8.rel_Grp \<Sigma>8.rel_Grp prod.rel_Grp
  unfolding Grp_def rel_fun_def by auto

lemma embL8_natural: "embL8 \<circ> \<Sigma>\<Sigma>7_map f = \<Sigma>\<Sigma>8_map f \<circ> embL8"
  using embL8_transfer[of "BNF_Def.Grp UNIV f"]
  unfolding \<Sigma>\<Sigma>7.rel_Grp \<Sigma>\<Sigma>8.rel_Grp
  unfolding Grp_def rel_fun_def by auto

lemma embR8_natural: "embR8 \<circ> \<Sigma>\<Sigma>7_map (K8_map f) = \<Sigma>\<Sigma>8_map f \<circ> embR8"
  using embR8_transfer[of "BNF_Def.Grp UNIV f"]
  unfolding \<Sigma>\<Sigma>7.rel_Grp K8.rel_Grp \<Sigma>\<Sigma>8.rel_Grp
  unfolding Grp_def rel_fun_def by auto

lemma \<Lambda>8_Inl: "\<Lambda>8 o Abs_\<Sigma>8 o Inl = F_map embL8 o \<Lambda>7"
  and \<Lambda>8_Inr: "\<Lambda>8 o Abs_\<Sigma>8 o Inr = \<rho>8"
unfolding \<Lambda>8_def o_assoc[symmetric] Rep_\<Sigma>8_o_Abs_\<Sigma>8 o_id by auto

lemma embL8_leaf7: "embL8 \<circ> leaf7 = leaf8"
unfolding embL8_def ext7_comp_leaf7 ..

lemma embL8_\<oo>\<pp>7: "embL8 \<circ> \<oo>\<pp>7 = \<oo>\<pp>8 \<circ> Abs_\<Sigma>8 \<circ> Inl \<circ> \<Sigma>7_map embL8"
unfolding embL8_def ext7_commute ..

lemma embR8_leaf7: "embR8 \<circ> leaf7 = \<oo>\<pp>8 \<circ> Abs_\<Sigma>8 \<circ> Inr \<circ> K8_map leaf8"
unfolding embR8_def ext7_comp_leaf7
unfolding o_assoc[symmetric] Abs_\<Sigma>8_natural map_sum_Inr ..

lemma embR8_\<oo>\<pp>7: "embR8 \<circ> \<oo>\<pp>7 = \<oo>\<pp>8 \<circ> Abs_\<Sigma>8 \<circ>  Inl \<circ> \<Sigma>7_map embR8"
unfolding embR8_def ext7_commute ..

end