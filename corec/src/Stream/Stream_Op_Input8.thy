theory Stream_Op_Input8
imports Stream_FreeAlg8
begin

abbreviation "MERGE8 \<equiv> \<oo>\<pp>8 o Abs_\<Sigma>8 o Inr :: 'a \<Sigma>\<Sigma>8 K8 \<Rightarrow> 'a \<Sigma>\<Sigma>8"

lemma PRD8_transfer[transfer_rule]:
  "(K8_rel (\<Sigma>\<Sigma>8_rel R) ===> \<Sigma>\<Sigma>8_rel R) MERGE8 MERGE8"
  by transfer_prover

definition \<rho>8 :: "('a \<times> 'a F) K8 \<Rightarrow> 'a \<Sigma>\<Sigma>8 F" where
  "\<rho>8 a_m_a'_b_n_b' =
    (let a_m_a' = fst a_m_a'_b_n_b' ; b_n_b' = snd a_m_a'_b_n_b' ;
      a = fst a_m_a' ; m = fst (snd a_m_a') ; a' = snd (snd a_m_a') ;
      b = fst b_n_b' ; n = fst (snd b_n_b') ; b' = snd (snd b_n_b')
    in if m \<le> n then (m, MERGE8 (leaf8 a', leaf8 b)) else (n, MERGE8 (leaf8 a, leaf8 b')))"

lemma \<rho>8_transfer[transfer_rule]:
  "(K8_rel (rel_prod R (F_rel R)) ===> F_rel (\<Sigma>\<Sigma>8_rel R)) \<rho>8 \<rho>8"
  unfolding Let_def \<rho>8_def[abs_def] rel_pre_J_def id_apply vimage2p_def BNF_Comp.id_bnf_comp_def
  by transfer_prover

end