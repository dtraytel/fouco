theory Binary_Tree_Op_Input1
imports Binary_Tree_FreeAlg1
begin

abbreviation "PLS1 \<equiv> \<oo>\<pp>1 o Abs_\<Sigma>1 o Inr :: 'a \<Sigma>\<Sigma>1 K1 \<Rightarrow> 'a \<Sigma>\<Sigma>1"

lemma PLS1_transfer[transfer_rule]:
  "(K1_rel (\<Sigma>\<Sigma>1_rel R) ===> \<Sigma>\<Sigma>1_rel R) PLS1 PLS1"
  by transfer_prover

(* \<rho>1 :: "('a \<times> 'a F) K1 \<Rightarrow> ('a K1) T0 F" *)
definition \<rho>1 :: "('a \<times> 'a F) K1 \<Rightarrow> 'a \<Sigma>\<Sigma>1 F" where
"\<rho>1 a_m_l_r_b_n_l_r =
 (let a_m_l_r = fst a_m_l_r_b_n_l_r ; b_n_l_r = snd a_m_l_r_b_n_l_r ;
      a = fst a_m_l_r ; m = fst (snd a_m_l_r) ; al = fst (snd (snd a_m_l_r)) ; ar = snd (snd (snd a_m_l_r)) ;
      b = fst b_n_l_r ; n = fst (snd b_n_l_r) ; bl = fst (snd (snd b_n_l_r)) ; br = snd (snd (snd b_n_l_r))
  in (m + n, K1_as_\<Sigma>\<Sigma>1 (al,bl), K1_as_\<Sigma>\<Sigma>1 (ar,br)))"

lemma \<rho>1_transfer[transfer_rule]:
  "(K1_rel (rel_prod R (F_rel R)) ===> F_rel (\<Sigma>\<Sigma>1_rel R)) \<rho>1 \<rho>1"
  unfolding Let_def \<rho>1_def[abs_def] rel_pre_J_def id_apply vimage2p_def BNF_Comp.id_bnf_comp_def
  by transfer_prover



end