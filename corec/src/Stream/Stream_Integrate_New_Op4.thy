header{* The integration of a new operation in the up-to setting *}

theory Stream_Integrate_New_Op4
imports Stream_Op_Input4
begin


subsection{* The assumptions *}

(*
(* The operation that creates the new distributive law, since its definition splits
trough a natural transformation ll, which will be defined in More_Corec_Upto4 as follows: *)
definition alg\<rho>4 :: "J K4 \<Rightarrow> J" where
"alg\<rho>4 = unfoldU3 (\<rho>4 o K4_map <id, dtor_J>)"
*)

lemma \<rho>4_natural: "\<rho>4 o K4_map (f ** F_map f) = F_map (\<Sigma>\<Sigma>4_map f) o \<rho>4"
  using \<rho>4_transfer[of "BNF_Def.Grp UNIV f"]
  unfolding F_rel_Grp \<Sigma>\<Sigma>4.rel_Grp K4.rel_Grp prod.rel_Grp
  unfolding Grp_def rel_fun_def by auto

subsection{* The integration *}

definition embL4 :: "'a \<Sigma>\<Sigma>3 \<Rightarrow> 'a \<Sigma>\<Sigma>4" where
"embL4 \<equiv> ext3 (\<oo>\<pp>4 o Abs_\<Sigma>4 o Inl) leaf4"

definition embR4 :: "('a K4) \<Sigma>\<Sigma>3 \<Rightarrow> 'a \<Sigma>\<Sigma>4" where
"embR4 \<equiv> ext3 (\<oo>\<pp>4 o Abs_\<Sigma>4 o Inl) (\<oo>\<pp>4 o \<Sigma>4_map leaf4 o Abs_\<Sigma>4 o Inr)"

definition \<Lambda>4 :: "('a \<times> 'a F) \<Sigma>4 \<Rightarrow> 'a \<Sigma>\<Sigma>4 F" where
"\<Lambda>4 = case_sum (F_map embL4 o \<Lambda>3) \<rho>4 o Rep_\<Sigma>4"

lemma embL4_transfer[transfer_rule]:
  "(\<Sigma>\<Sigma>3_rel R ===> \<Sigma>\<Sigma>4_rel R) embL4 embL4"
  unfolding embL4_def ext3_alt by transfer_prover

lemma embR4_transfer[transfer_rule]:
  "(\<Sigma>\<Sigma>3_rel (K4_rel R) ===> \<Sigma>\<Sigma>4_rel R) embR4 embR4"
  unfolding embR4_def ext3_alt by transfer_prover

lemma \<Lambda>4_transfer[transfer_rule]:
  "(\<Sigma>4_rel (rel_prod R (F_rel R)) ===> F_rel (\<Sigma>\<Sigma>4_rel R)) \<Lambda>4 \<Lambda>4"
  unfolding \<Lambda>4_def by transfer_prover

lemma \<Lambda>4_natural: "\<Lambda>4 o \<Sigma>4_map (f ** F_map f) = F_map (\<Sigma>\<Sigma>4_map f) o \<Lambda>4"
  using \<Lambda>4_transfer[of "BNF_Def.Grp UNIV f"]
  unfolding F_rel_Grp \<Sigma>\<Sigma>4.rel_Grp \<Sigma>4.rel_Grp prod.rel_Grp
  unfolding Grp_def rel_fun_def by auto

lemma embL4_natural: "embL4 \<circ> \<Sigma>\<Sigma>3_map f = \<Sigma>\<Sigma>4_map f \<circ> embL4"
  using embL4_transfer[of "BNF_Def.Grp UNIV f"]
  unfolding \<Sigma>\<Sigma>3.rel_Grp \<Sigma>\<Sigma>4.rel_Grp
  unfolding Grp_def rel_fun_def by auto

lemma embR4_natural: "embR4 \<circ> \<Sigma>\<Sigma>3_map (K4_map f) = \<Sigma>\<Sigma>4_map f \<circ> embR4"
  using embR4_transfer[of "BNF_Def.Grp UNIV f"]
  unfolding \<Sigma>\<Sigma>3.rel_Grp K4.rel_Grp \<Sigma>\<Sigma>4.rel_Grp
  unfolding Grp_def rel_fun_def by auto

lemma \<Lambda>4_Inl: "\<Lambda>4 o Abs_\<Sigma>4 o Inl = F_map embL4 o \<Lambda>3"
  and \<Lambda>4_Inr: "\<Lambda>4 o Abs_\<Sigma>4 o Inr = \<rho>4"
unfolding \<Lambda>4_def o_assoc[symmetric] Rep_\<Sigma>4_o_Abs_\<Sigma>4 o_id by auto

lemma embL4_leaf3: "embL4 \<circ> leaf3 = leaf4"
unfolding embL4_def ext3_comp_leaf3 ..

lemma embL4_\<oo>\<pp>3: "embL4 \<circ> \<oo>\<pp>3 = \<oo>\<pp>4 \<circ> Abs_\<Sigma>4 \<circ> Inl \<circ> \<Sigma>3_map embL4"
unfolding embL4_def ext3_commute ..

lemma embR4_leaf3: "embR4 \<circ> leaf3 = \<oo>\<pp>4 \<circ> Abs_\<Sigma>4 \<circ> Inr \<circ> K4_map leaf4"
unfolding embR4_def ext3_comp_leaf3
unfolding o_assoc[symmetric] Abs_\<Sigma>4_natural map_sum_Inr ..

lemma embR4_\<oo>\<pp>3: "embR4 \<circ> \<oo>\<pp>3 = \<oo>\<pp>4 \<circ> Abs_\<Sigma>4 \<circ>  Inl \<circ> \<Sigma>3_map embR4"
unfolding embR4_def ext3_commute ..

end