theory Tree_Op_Input1
imports Tree_FreeAlg1
begin

abbreviation "PLS1 \<equiv> \<oo>\<pp>1 o Abs_\<Sigma>1 o Inr :: 'a \<Sigma>\<Sigma>1 K1 \<Rightarrow> 'a \<Sigma>\<Sigma>1"

lemma PLS1_transfer[transfer_rule]:
  "(K1_rel (\<Sigma>\<Sigma>1_rel R) ===> \<Sigma>\<Sigma>1_rel R) PLS1 PLS1"
  by transfer_prover

definition \<rho>1 :: "('a \<times> 'a F) K1 \<Rightarrow> 'a \<Sigma>\<Sigma>1 F" where
"\<rho>1 a_m_a'_b_n_b' =
 (let a_m_a' = fst a_m_a'_b_n_b' ; b_n_b' = snd a_m_a'_b_n_b' ;
      a = fst a_m_a' ; m = fst (snd a_m_a') ; a' = snd (snd a_m_a') ;
      b = fst b_n_b' ; n = fst (snd b_n_b') ; b' = snd (snd b_n_b')
  in (m + n, map K1_as_\<Sigma>\<Sigma>1 (zip a' b')))"

lemma \<rho>1_transfer[transfer_rule]:
  "(K1_rel (rel_prod R (F_rel R)) ===> F_rel (\<Sigma>\<Sigma>1_rel R)) \<rho>1 \<rho>1"
  unfolding Let_def \<rho>1_def[abs_def] rel_pre_J_def id_apply vimage2p_def BNF_Comp.id_bnf_comp_def
  apply (rule rel_funI)
  apply (rule rel_funD[OF rel_funD[OF Pair_transfer], rotated])
   apply (rule rel_funD[OF rel_funD[OF map_transfer], rotated -2])
    apply (rule K1_as_\<Sigma>\<Sigma>1_transfer)
   apply (rule rel_funD[OF rel_funD[OF zip_transfer]])
   apply auto
  done



end