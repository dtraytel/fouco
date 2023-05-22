header{* The integration of a new operation in the up-to setting *}

theory Stream_Integrate_New_Op9
imports Stream_Op_Input9
begin


subsection{* The assumptions *}

(*
(* The operation that creates the new distributive law, since its definition splits
trough a natural transformation ll, which will be defined in More_Corec_Upto9 as follows: *)
definition alg\<rho>9 :: "J K9 \<Rightarrow> J" where
"alg\<rho>9 = unfoldU8 (\<rho>9 o K9_map <id, dtor_J>)"
*)

lemma \<rho>9_natural: "\<rho>9 o K9_map (f ** F_map f) = F_map (\<Sigma>\<Sigma>9_map f) o \<rho>9"
  using \<rho>9_transfer[of "BNF_Def.Grp UNIV f"]
  unfolding F_rel_Grp \<Sigma>\<Sigma>9.rel_Grp K9.rel_Grp prod.rel_Grp
  unfolding Grp_def rel_fun_def by auto

subsection{* The integration *}

definition embL9 :: "'a \<Sigma>\<Sigma>8 \<Rightarrow> 'a \<Sigma>\<Sigma>9" where
"embL9 \<equiv> ext8 (\<oo>\<pp>9 o Abs_\<Sigma>9 o Inl) leaf9"

definition embR9 :: "('a K9) \<Sigma>\<Sigma>8 \<Rightarrow> 'a \<Sigma>\<Sigma>9" where
"embR9 \<equiv> ext8 (\<oo>\<pp>9 o Abs_\<Sigma>9 o Inl) (\<oo>\<pp>9 o \<Sigma>9_map leaf9 o Abs_\<Sigma>9 o Inr)"

definition \<Lambda>9 :: "('a \<times> 'a F) \<Sigma>9 \<Rightarrow> 'a \<Sigma>\<Sigma>9 F" where
"\<Lambda>9 = case_sum (F_map embL9 o \<Lambda>8) \<rho>9 o Rep_\<Sigma>9"

lemma embL9_transfer[transfer_rule]:
  "(\<Sigma>\<Sigma>8_rel R ===> \<Sigma>\<Sigma>9_rel R) embL9 embL9"
  unfolding embL9_def ext8_alt by transfer_prover

lemma embR9_transfer[transfer_rule]:
  "(\<Sigma>\<Sigma>8_rel (K9_rel R) ===> \<Sigma>\<Sigma>9_rel R) embR9 embR9"
  unfolding embR9_def ext8_alt by transfer_prover

lemma \<Lambda>9_transfer[transfer_rule]:
  "(\<Sigma>9_rel (rel_prod R (F_rel R)) ===> F_rel (\<Sigma>\<Sigma>9_rel R)) \<Lambda>9 \<Lambda>9"
  unfolding \<Lambda>9_def by transfer_prover

lemma \<Lambda>9_natural: "\<Lambda>9 o \<Sigma>9_map (f ** F_map f) = F_map (\<Sigma>\<Sigma>9_map f) o \<Lambda>9"
  using \<Lambda>9_transfer[of "BNF_Def.Grp UNIV f"]
  unfolding F_rel_Grp \<Sigma>\<Sigma>9.rel_Grp \<Sigma>9.rel_Grp prod.rel_Grp
  unfolding Grp_def rel_fun_def by auto

lemma embL9_natural: "embL9 \<circ> \<Sigma>\<Sigma>8_map f = \<Sigma>\<Sigma>9_map f \<circ> embL9"
  using embL9_transfer[of "BNF_Def.Grp UNIV f"]
  unfolding \<Sigma>\<Sigma>8.rel_Grp \<Sigma>\<Sigma>9.rel_Grp
  unfolding Grp_def rel_fun_def by auto

lemma embR9_natural: "embR9 \<circ> \<Sigma>\<Sigma>8_map (K9_map f) = \<Sigma>\<Sigma>9_map f \<circ> embR9"
  using embR9_transfer[of "BNF_Def.Grp UNIV f"]
  unfolding \<Sigma>\<Sigma>8.rel_Grp K9.rel_Grp \<Sigma>\<Sigma>9.rel_Grp
  unfolding Grp_def rel_fun_def by auto

lemma \<Lambda>9_Inl: "\<Lambda>9 o Abs_\<Sigma>9 o Inl = F_map embL9 o \<Lambda>8"
  and \<Lambda>9_Inr: "\<Lambda>9 o Abs_\<Sigma>9 o Inr = \<rho>9"
unfolding \<Lambda>9_def o_assoc[symmetric] Rep_\<Sigma>9_o_Abs_\<Sigma>9 o_id by auto

lemma embL9_leaf8: "embL9 \<circ> leaf8 = leaf9"
unfolding embL9_def ext8_comp_leaf8 ..

lemma embL9_\<oo>\<pp>8: "embL9 \<circ> \<oo>\<pp>8 = \<oo>\<pp>9 \<circ> Abs_\<Sigma>9 \<circ> Inl \<circ> \<Sigma>8_map embL9"
unfolding embL9_def ext8_commute ..

lemma embR9_leaf8: "embR9 \<circ> leaf8 = \<oo>\<pp>9 \<circ> Abs_\<Sigma>9 \<circ> Inr \<circ> K9_map leaf9"
unfolding embR9_def ext8_comp_leaf8
unfolding o_assoc[symmetric] Abs_\<Sigma>9_natural map_sum_Inr ..

lemma embR9_\<oo>\<pp>8: "embR9 \<circ> \<oo>\<pp>8 = \<oo>\<pp>9 \<circ> Abs_\<Sigma>9 \<circ>  Inl \<circ> \<Sigma>8_map embR9"
unfolding embR9_def ext8_commute ..

end