theory Stream_Op_Input6
imports Stream_FreeAlg6
begin

abbreviation "PLS6 \<equiv> \<oo>\<pp>6 o Abs_\<Sigma>6 o Inl o Abs_\<Sigma>5 o Inl o Abs_\<Sigma>4 o Inl o Abs_\<Sigma>3 o Inl o Abs_\<Sigma>2 o Inl o Abs_\<Sigma>1 o Inr :: 'a \<Sigma>\<Sigma>6 K1 \<Rightarrow> 'a \<Sigma>\<Sigma>6"
abbreviation "INTERLEAVE6 \<equiv> \<oo>\<pp>6 o Abs_\<Sigma>6 o Inr :: 'a \<Sigma>\<Sigma>6 K6 \<Rightarrow> 'a \<Sigma>\<Sigma>6"

lemma PLS6_transfer[transfer_rule]:
  "(K1_rel (\<Sigma>\<Sigma>6_rel R) ===> \<Sigma>\<Sigma>6_rel R) PLS6 PLS6"
  by transfer_prover

lemma PRD6_transfer[transfer_rule]:
  "(K6_rel (\<Sigma>\<Sigma>6_rel R) ===> \<Sigma>\<Sigma>6_rel R) INTERLEAVE6 INTERLEAVE6"
  by transfer_prover

definition \<rho>6 :: "('a \<times> 'a F) K6 \<Rightarrow> 'a \<Sigma>\<Sigma>6 F" where
  "\<rho>6 a_m_a'_b_n_b' =
    (let a_m_a' = fst a_m_a'_b_n_b' ; b_n_b' = snd a_m_a'_b_n_b' ;
      a = fst a_m_a' ; m = fst (snd a_m_a') ; a' = snd (snd a_m_a') ;
      b = fst b_n_b' ; n = fst (snd b_n_b') ; b' = snd (snd b_n_b')
    in (m, INTERLEAVE6 (leaf6 b, leaf6 a')))"

lemma \<rho>6_transfer[transfer_rule]:
  "(K6_rel (rel_prod R (F_rel R)) ===> F_rel (\<Sigma>\<Sigma>6_rel R)) \<rho>6 \<rho>6"
  unfolding Let_def \<rho>6_def[abs_def] rel_pre_J_def id_apply vimage2p_def BNF_Comp.id_bnf_comp_def
  by transfer_prover

end