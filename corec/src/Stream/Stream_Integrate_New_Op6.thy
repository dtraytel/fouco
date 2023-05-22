header{* The integration of a new operation in the up-to setting *}

theory Stream_Integrate_New_Op6
imports Stream_Op_Input6
begin


subsection{* The assumptions *}

(*
(* The operation that creates the new distributive law, since its definition splits
trough a natural transformation ll, which will be defined in More_Corec_Upto6 as follows: *)
definition alg\<rho>6 :: "J K6 \<Rightarrow> J" where
"alg\<rho>6 = unfoldU5 (\<rho>6 o K6_map <id, dtor_J>)"
*)

lemma \<rho>6_natural: "\<rho>6 o K6_map (f ** F_map f) = F_map (\<Sigma>\<Sigma>6_map f) o \<rho>6"
  using \<rho>6_transfer[of "BNF_Def.Grp UNIV f"]
  unfolding F_rel_Grp \<Sigma>\<Sigma>6.rel_Grp K6.rel_Grp prod.rel_Grp
  unfolding Grp_def rel_fun_def by auto

subsection{* The integration *}

definition embL6 :: "'a \<Sigma>\<Sigma>5 \<Rightarrow> 'a \<Sigma>\<Sigma>6" where
"embL6 \<equiv> ext5 (\<oo>\<pp>6 o Abs_\<Sigma>6 o Inl) leaf6"

definition embR6 :: "('a K6) \<Sigma>\<Sigma>5 \<Rightarrow> 'a \<Sigma>\<Sigma>6" where
"embR6 \<equiv> ext5 (\<oo>\<pp>6 o Abs_\<Sigma>6 o Inl) (\<oo>\<pp>6 o \<Sigma>6_map leaf6 o Abs_\<Sigma>6 o Inr)"

definition \<Lambda>6 :: "('a \<times> 'a F) \<Sigma>6 \<Rightarrow> 'a \<Sigma>\<Sigma>6 F" where
"\<Lambda>6 = case_sum (F_map embL6 o \<Lambda>5) \<rho>6 o Rep_\<Sigma>6"

lemma embL6_transfer[transfer_rule]:
  "(\<Sigma>\<Sigma>5_rel R ===> \<Sigma>\<Sigma>6_rel R) embL6 embL6"
  unfolding embL6_def ext5_alt by transfer_prover

lemma embR6_transfer[transfer_rule]:
  "(\<Sigma>\<Sigma>5_rel (K6_rel R) ===> \<Sigma>\<Sigma>6_rel R) embR6 embR6"
  unfolding embR6_def ext5_alt by transfer_prover

lemma \<Lambda>6_transfer[transfer_rule]:
  "(\<Sigma>6_rel (rel_prod R (F_rel R)) ===> F_rel (\<Sigma>\<Sigma>6_rel R)) \<Lambda>6 \<Lambda>6"
  unfolding \<Lambda>6_def by transfer_prover

lemma \<Lambda>6_natural: "\<Lambda>6 o \<Sigma>6_map (f ** F_map f) = F_map (\<Sigma>\<Sigma>6_map f) o \<Lambda>6"
  using \<Lambda>6_transfer[of "BNF_Def.Grp UNIV f"]
  unfolding F_rel_Grp \<Sigma>\<Sigma>6.rel_Grp \<Sigma>6.rel_Grp prod.rel_Grp
  unfolding Grp_def rel_fun_def by auto

lemma embL6_natural: "embL6 \<circ> \<Sigma>\<Sigma>5_map f = \<Sigma>\<Sigma>6_map f \<circ> embL6"
  using embL6_transfer[of "BNF_Def.Grp UNIV f"]
  unfolding \<Sigma>\<Sigma>5.rel_Grp \<Sigma>\<Sigma>6.rel_Grp
  unfolding Grp_def rel_fun_def by auto

lemma embR6_natural: "embR6 \<circ> \<Sigma>\<Sigma>5_map (K6_map f) = \<Sigma>\<Sigma>6_map f \<circ> embR6"
  using embR6_transfer[of "BNF_Def.Grp UNIV f"]
  unfolding \<Sigma>\<Sigma>5.rel_Grp K6.rel_Grp \<Sigma>\<Sigma>6.rel_Grp
  unfolding Grp_def rel_fun_def by auto

lemma \<Lambda>6_Inl: "\<Lambda>6 o Abs_\<Sigma>6 o Inl = F_map embL6 o \<Lambda>5"
  and \<Lambda>6_Inr: "\<Lambda>6 o Abs_\<Sigma>6 o Inr = \<rho>6"
unfolding \<Lambda>6_def o_assoc[symmetric] Rep_\<Sigma>6_o_Abs_\<Sigma>6 o_id by auto

lemma embL6_leaf5: "embL6 \<circ> leaf5 = leaf6"
unfolding embL6_def ext5_comp_leaf5 ..

lemma embL6_\<oo>\<pp>5: "embL6 \<circ> \<oo>\<pp>5 = \<oo>\<pp>6 \<circ> Abs_\<Sigma>6 \<circ> Inl \<circ> \<Sigma>5_map embL6"
unfolding embL6_def ext5_commute ..

lemma embR6_leaf5: "embR6 \<circ> leaf5 = \<oo>\<pp>6 \<circ> Abs_\<Sigma>6 \<circ> Inr \<circ> K6_map leaf6"
unfolding embR6_def ext5_comp_leaf5
unfolding o_assoc[symmetric] Abs_\<Sigma>6_natural map_sum_Inr ..

lemma embR6_\<oo>\<pp>5: "embR6 \<circ> \<oo>\<pp>5 = \<oo>\<pp>6 \<circ> Abs_\<Sigma>6 \<circ>  Inl \<circ> \<Sigma>5_map embR6"
unfolding embR6_def ext5_commute ..

end