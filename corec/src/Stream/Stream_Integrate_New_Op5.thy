header{* The integration of a new operation in the up-to setting *}

theory Stream_Integrate_New_Op5
imports Stream_Op_Input5
begin


subsection{* The assumptions *}

(*
(* The operation that creates the new distributive law, since its definition splits
trough a natural transformation ll, which will be defined in More_Corec_Upto5 as follows: *)
definition alg\<rho>5 :: "J K5 \<Rightarrow> J" where
"alg\<rho>5 = unfoldU4 (\<rho>5 o K5_map <id, dtor_J>)"
*)

lemma \<rho>5_natural: "\<rho>5 o K5_map (f ** F_map f) = F_map (\<Sigma>\<Sigma>5_map f) o \<rho>5"
  using \<rho>5_transfer[of "BNF_Def.Grp UNIV f"]
  unfolding F_rel_Grp \<Sigma>\<Sigma>5.rel_Grp K5.rel_Grp prod.rel_Grp
  unfolding Grp_def rel_fun_def by auto

subsection{* The integration *}

definition embL5 :: "'a \<Sigma>\<Sigma>4 \<Rightarrow> 'a \<Sigma>\<Sigma>5" where
"embL5 \<equiv> ext4 (\<oo>\<pp>5 o Abs_\<Sigma>5 o Inl) leaf5"

definition embR5 :: "('a K5) \<Sigma>\<Sigma>4 \<Rightarrow> 'a \<Sigma>\<Sigma>5" where
"embR5 \<equiv> ext4 (\<oo>\<pp>5 o Abs_\<Sigma>5 o Inl) (\<oo>\<pp>5 o \<Sigma>5_map leaf5 o Abs_\<Sigma>5 o Inr)"

definition \<Lambda>5 :: "('a \<times> 'a F) \<Sigma>5 \<Rightarrow> 'a \<Sigma>\<Sigma>5 F" where
"\<Lambda>5 = case_sum (F_map embL5 o \<Lambda>4) \<rho>5 o Rep_\<Sigma>5"

lemma embL5_transfer[transfer_rule]:
  "(\<Sigma>\<Sigma>4_rel R ===> \<Sigma>\<Sigma>5_rel R) embL5 embL5"
  unfolding embL5_def ext4_alt by transfer_prover

lemma embR5_transfer[transfer_rule]:
  "(\<Sigma>\<Sigma>4_rel (K5_rel R) ===> \<Sigma>\<Sigma>5_rel R) embR5 embR5"
  unfolding embR5_def ext4_alt by transfer_prover

lemma \<Lambda>5_transfer[transfer_rule]:
  "(\<Sigma>5_rel (rel_prod R (F_rel R)) ===> F_rel (\<Sigma>\<Sigma>5_rel R)) \<Lambda>5 \<Lambda>5"
  unfolding \<Lambda>5_def by transfer_prover

lemma \<Lambda>5_natural: "\<Lambda>5 o \<Sigma>5_map (f ** F_map f) = F_map (\<Sigma>\<Sigma>5_map f) o \<Lambda>5"
  using \<Lambda>5_transfer[of "BNF_Def.Grp UNIV f"]
  unfolding F_rel_Grp \<Sigma>\<Sigma>5.rel_Grp \<Sigma>5.rel_Grp prod.rel_Grp
  unfolding Grp_def rel_fun_def by auto

lemma embL5_natural: "embL5 \<circ> \<Sigma>\<Sigma>4_map f = \<Sigma>\<Sigma>5_map f \<circ> embL5"
  using embL5_transfer[of "BNF_Def.Grp UNIV f"]
  unfolding \<Sigma>\<Sigma>4.rel_Grp \<Sigma>\<Sigma>5.rel_Grp
  unfolding Grp_def rel_fun_def by auto

lemma embR5_natural: "embR5 \<circ> \<Sigma>\<Sigma>4_map (K5_map f) = \<Sigma>\<Sigma>5_map f \<circ> embR5"
  using embR5_transfer[of "BNF_Def.Grp UNIV f"]
  unfolding \<Sigma>\<Sigma>4.rel_Grp K5.rel_Grp \<Sigma>\<Sigma>5.rel_Grp
  unfolding Grp_def rel_fun_def by auto

lemma \<Lambda>5_Inl: "\<Lambda>5 o Abs_\<Sigma>5 o Inl = F_map embL5 o \<Lambda>4"
  and \<Lambda>5_Inr: "\<Lambda>5 o Abs_\<Sigma>5 o Inr = \<rho>5"
unfolding \<Lambda>5_def o_assoc[symmetric] Rep_\<Sigma>5_o_Abs_\<Sigma>5 o_id by auto

lemma embL5_leaf4: "embL5 \<circ> leaf4 = leaf5"
unfolding embL5_def ext4_comp_leaf4 ..

lemma embL5_\<oo>\<pp>4: "embL5 \<circ> \<oo>\<pp>4 = \<oo>\<pp>5 \<circ> Abs_\<Sigma>5 \<circ> Inl \<circ> \<Sigma>4_map embL5"
unfolding embL5_def ext4_commute ..

lemma embR5_leaf4: "embR5 \<circ> leaf4 = \<oo>\<pp>5 \<circ> Abs_\<Sigma>5 \<circ> Inr \<circ> K5_map leaf5"
unfolding embR5_def ext4_comp_leaf4
unfolding o_assoc[symmetric] Abs_\<Sigma>5_natural map_sum_Inr ..

lemma embR5_\<oo>\<pp>4: "embR5 \<circ> \<oo>\<pp>4 = \<oo>\<pp>5 \<circ> Abs_\<Sigma>5 \<circ>  Inl \<circ> \<Sigma>4_map embR5"
unfolding embR5_def ext4_commute ..

end