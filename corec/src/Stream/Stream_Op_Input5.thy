theory Stream_Op_Input5
imports Stream_FreeAlg5
begin

abbreviation "PLS5 \<equiv> \<oo>\<pp>5 o Abs_\<Sigma>5 o Inl o Abs_\<Sigma>4 o Inl o Abs_\<Sigma>3 o Inl o Abs_\<Sigma>2 o Inl o Abs_\<Sigma>1 o Inr :: 'a \<Sigma>\<Sigma>5 K1 \<Rightarrow> 'a \<Sigma>\<Sigma>5"
abbreviation "PRD5 \<equiv> \<oo>\<pp>5 o Abs_\<Sigma>5 o Inr :: 'a \<Sigma>\<Sigma>5 K5 \<Rightarrow> 'a \<Sigma>\<Sigma>5"

lemma PLS5_transfer[transfer_rule]:
  "(K1_rel (\<Sigma>\<Sigma>5_rel R) ===> \<Sigma>\<Sigma>5_rel R) PLS5 PLS5"
  by transfer_prover

lemma PRD5_transfer[transfer_rule]:
  "(K5_rel (\<Sigma>\<Sigma>5_rel R) ===> \<Sigma>\<Sigma>5_rel R) PRD5 PRD5"
  by transfer_prover

definition \<rho>5 :: "('a \<times> 'a F) K5 \<Rightarrow> 'a \<Sigma>\<Sigma>5 F" where
  "\<rho>5 a_m_a'_b_n_b' =
    (let a_m_a' = fst a_m_a'_b_n_b' ; b_n_b' = snd a_m_a'_b_n_b' ;
      a = fst a_m_a' ; m = fst (snd a_m_a') ; a' = snd (snd a_m_a') ;
      b = fst b_n_b' ; n = fst (snd b_n_b') ; b' = snd (snd b_n_b')
    in (m * n, PRD5 (K5_as_\<Sigma>\<Sigma>5 (a,b'), PLS5 (leaf5 a', leaf5 b))))"

lemma \<rho>5_transfer[transfer_rule]:
  "(K5_rel (rel_prod R (F_rel R)) ===> F_rel (\<Sigma>\<Sigma>5_rel R)) \<rho>5 \<rho>5"
  unfolding Let_def \<rho>5_def[abs_def] rel_pre_J_def id_apply vimage2p_def BNF_Comp.id_bnf_comp_def
  by transfer_prover



end