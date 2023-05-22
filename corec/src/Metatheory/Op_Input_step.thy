theory Op_Input_step
imports FreeAlg_step
begin

(* The distributive law extracted from the newly defined operation on the final coalgebra: *)
(*DEFINE_rr*)
consts \<rho>_step :: "('a \<times> 'a F) K_step \<Rightarrow> 'a \<Sigma>\<Sigma>_step F"

axiomatization where
  \<rho>_step_transfer[transfer_rule]:
    "(K_step_rel (rel_prod R (F_rel R)) ===> F_rel (\<Sigma>\<Sigma>_step_rel R)) \<rho>_step \<rho>_step"
(*DEFINE_\<rho>_END*)



end