header{* The integration of a new operation in the up-to setting *}

theory Stream_Integrate_New_Op7
imports Stream_Op_Input7
begin


subsection{* The assumptions *}

(*
(* The operation that creates the new distributive law, since its definition splits
trough a natural transformation ll, which will be defined in More_Corec_Upto7 as follows: *)
definition alg\<rho>7 :: "J K7 \<Rightarrow> J" where
"alg\<rho>7 = unfoldU6 (\<rho>7 o K7_map <id, dtor_J>)"
*)

lemma \<rho>7_natural: "\<rho>7 o K7_map (f ** F_map f) = F_map (\<Sigma>\<Sigma>7_map f) o \<rho>7"
  using \<rho>7_transfer[of "BNF_Def.Grp UNIV f"]
  unfolding F_rel_Grp \<Sigma>\<Sigma>7.rel_Grp K7.rel_Grp prod.rel_Grp
  unfolding Grp_def rel_fun_def by auto

subsection{* The integration *}

definition embL7 :: "'a \<Sigma>\<Sigma>6 \<Rightarrow> 'a \<Sigma>\<Sigma>7" where
"embL7 \<equiv> ext6 (\<oo>\<pp>7 o Abs_\<Sigma>7 o Inl) leaf7"

definition embR7 :: "('a K7) \<Sigma>\<Sigma>6 \<Rightarrow> 'a \<Sigma>\<Sigma>7" where
"embR7 \<equiv> ext6 (\<oo>\<pp>7 o Abs_\<Sigma>7 o Inl) (\<oo>\<pp>7 o \<Sigma>7_map leaf7 o Abs_\<Sigma>7 o Inr)"

definition \<Lambda>7 :: "('a \<times> 'a F) \<Sigma>7 \<Rightarrow> 'a \<Sigma>\<Sigma>7 F" where
"\<Lambda>7 = case_sum (F_map embL7 o \<Lambda>6) \<rho>7 o Rep_\<Sigma>7"

lemma embL7_transfer[transfer_rule]:
  "(\<Sigma>\<Sigma>6_rel R ===> \<Sigma>\<Sigma>7_rel R) embL7 embL7"
  unfolding embL7_def ext6_alt by transfer_prover

lemma embR7_transfer[transfer_rule]:
  "(\<Sigma>\<Sigma>6_rel (K7_rel R) ===> \<Sigma>\<Sigma>7_rel R) embR7 embR7"
  unfolding embR7_def ext6_alt by transfer_prover

lemma \<Lambda>7_transfer[transfer_rule]:
  "(\<Sigma>7_rel (rel_prod R (F_rel R)) ===> F_rel (\<Sigma>\<Sigma>7_rel R)) \<Lambda>7 \<Lambda>7"
  unfolding \<Lambda>7_def by transfer_prover

lemma \<Lambda>7_natural: "\<Lambda>7 o \<Sigma>7_map (f ** F_map f) = F_map (\<Sigma>\<Sigma>7_map f) o \<Lambda>7"
  using \<Lambda>7_transfer[of "BNF_Def.Grp UNIV f"]
  unfolding F_rel_Grp \<Sigma>\<Sigma>7.rel_Grp \<Sigma>7.rel_Grp prod.rel_Grp
  unfolding Grp_def rel_fun_def by auto

lemma embL7_natural: "embL7 \<circ> \<Sigma>\<Sigma>6_map f = \<Sigma>\<Sigma>7_map f \<circ> embL7"
  using embL7_transfer[of "BNF_Def.Grp UNIV f"]
  unfolding \<Sigma>\<Sigma>6.rel_Grp \<Sigma>\<Sigma>7.rel_Grp
  unfolding Grp_def rel_fun_def by auto

lemma embR7_natural: "embR7 \<circ> \<Sigma>\<Sigma>6_map (K7_map f) = \<Sigma>\<Sigma>7_map f \<circ> embR7"
  using embR7_transfer[of "BNF_Def.Grp UNIV f"]
  unfolding \<Sigma>\<Sigma>6.rel_Grp K7.rel_Grp \<Sigma>\<Sigma>7.rel_Grp
  unfolding Grp_def rel_fun_def by auto

lemma \<Lambda>7_Inl: "\<Lambda>7 o Abs_\<Sigma>7 o Inl = F_map embL7 o \<Lambda>6"
  and \<Lambda>7_Inr: "\<Lambda>7 o Abs_\<Sigma>7 o Inr = \<rho>7"
unfolding \<Lambda>7_def o_assoc[symmetric] Rep_\<Sigma>7_o_Abs_\<Sigma>7 o_id by auto

lemma embL7_leaf6: "embL7 \<circ> leaf6 = leaf7"
unfolding embL7_def ext6_comp_leaf6 ..

lemma embL7_\<oo>\<pp>6: "embL7 \<circ> \<oo>\<pp>6 = \<oo>\<pp>7 \<circ> Abs_\<Sigma>7 \<circ> Inl \<circ> \<Sigma>6_map embL7"
unfolding embL7_def ext6_commute ..

lemma embR7_leaf6: "embR7 \<circ> leaf6 = \<oo>\<pp>7 \<circ> Abs_\<Sigma>7 \<circ> Inr \<circ> K7_map leaf7"
unfolding embR7_def ext6_comp_leaf6
unfolding o_assoc[symmetric] Abs_\<Sigma>7_natural map_sum_Inr ..

lemma embR7_\<oo>\<pp>6: "embR7 \<circ> \<oo>\<pp>6 = \<oo>\<pp>7 \<circ> Abs_\<Sigma>7 \<circ>  Inl \<circ> \<Sigma>6_map embR7"
unfolding embR7_def ext6_commute ..

end