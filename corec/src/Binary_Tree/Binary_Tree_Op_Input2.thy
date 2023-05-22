theory Binary_Tree_Op_Input2
imports Binary_Tree_FreeAlg2
begin

abbreviation "PLS2 \<equiv> \<oo>\<pp>2 o Abs_\<Sigma>2 o Inl o Abs_\<Sigma>1 o Inr :: 'a \<Sigma>\<Sigma>2 K1 \<Rightarrow> 'a \<Sigma>\<Sigma>2"
abbreviation "DIV2 \<equiv> \<oo>\<pp>2 o Abs_\<Sigma>2 o Inr :: 'a \<Sigma>\<Sigma>2 K2 \<Rightarrow> 'a \<Sigma>\<Sigma>2"

lemma DIV2_transfer[transfer_rule]:
  "(K2_rel (\<Sigma>\<Sigma>2_rel R) ===> \<Sigma>\<Sigma>2_rel R) DIV2 DIV2"
  by transfer_prover

(* \<rho>2 :: "('a \<times> 'a F) K2 \<Rightarrow> ('a K2) T0 F" *)
definition \<rho>2 :: "('a \<times> 'a F) K2 \<Rightarrow> 'a \<Sigma>\<Sigma>2 F" where
"\<rho>2 a_m_l_r_b_n_l_r =
 (let a_m_l_r = fst a_m_l_r_b_n_l_r ; b_n_l_r = snd a_m_l_r_b_n_l_r ;
      a = fst a_m_l_r ; m = fst (snd a_m_l_r) ; al = fst (snd (snd a_m_l_r)) ; ar = snd (snd (snd a_m_l_r)) ;
      b = fst b_n_l_r ; n = fst (snd b_n_l_r) ; bl = fst (snd (snd b_n_l_r)) ; br = snd (snd (snd b_n_l_r))
  in (m / n, K2_as_\<Sigma>\<Sigma>2 (al,bl), K2_as_\<Sigma>\<Sigma>2 (ar,br)))"

lemma \<rho>2_transfer[transfer_rule]:
  "(K2_rel (rel_prod R (F_rel R)) ===> F_rel (\<Sigma>\<Sigma>2_rel R)) \<rho>2 \<rho>2"
  unfolding Let_def \<rho>2_def[abs_def] rel_pre_J_def id_apply vimage2p_def BNF_Comp.id_bnf_comp_def
  by transfer_prover



end