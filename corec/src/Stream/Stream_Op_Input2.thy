theory Stream_Op_Input2
imports Stream_FreeAlg2
begin

abbreviation "PLS2 \<equiv> \<oo>\<pp>2 o Abs_\<Sigma>2 o Inl o Abs_\<Sigma>1 o Inr :: 'a \<Sigma>\<Sigma>2 K1 \<Rightarrow> 'a \<Sigma>\<Sigma>2"
abbreviation "PRD2 \<equiv> \<oo>\<pp>2 o Abs_\<Sigma>2 o Inr :: 'a \<Sigma>\<Sigma>2 K2 \<Rightarrow> 'a \<Sigma>\<Sigma>2"

lemma PLS2_transfer[transfer_rule]:
  "(K1_rel (\<Sigma>\<Sigma>2_rel R) ===> \<Sigma>\<Sigma>2_rel R) PLS2 PLS2"
  by transfer_prover

lemma PRD2_transfer[transfer_rule]:
  "(K2_rel (\<Sigma>\<Sigma>2_rel R) ===> \<Sigma>\<Sigma>2_rel R) PRD2 PRD2"
  by transfer_prover

definition \<rho>2 :: "('a \<times> 'a F) K2 \<Rightarrow> 'a \<Sigma>\<Sigma>2 F" where
  "\<rho>2 a_m_a'_b_n_b' =
    (let a_m_a' = fst a_m_a'_b_n_b' ; b_n_b' = snd a_m_a'_b_n_b' ;
      a = fst a_m_a' ; m = fst (snd a_m_a') ; a' = snd (snd a_m_a') ;
      b = fst b_n_b' ; n = fst (snd b_n_b') ; b' = snd (snd b_n_b')
    in (m * n, PLS2 (K2_as_\<Sigma>\<Sigma>2 (a,b'), K2_as_\<Sigma>\<Sigma>2 (a',b))))"

lemma \<rho>2_transfer[transfer_rule]:
  "(K2_rel (rel_prod R (F_rel R)) ===> F_rel (\<Sigma>\<Sigma>2_rel R)) \<rho>2 \<rho>2"
  unfolding Let_def \<rho>2_def[abs_def] rel_pre_J_def id_apply vimage2p_def BNF_Comp.id_bnf_comp_def
  by transfer_prover

end