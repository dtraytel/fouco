theory Input_base
imports Prelim
  "~~/src/HOL/Library/BNF_Axiomatization"
begin

(*REPLACE_F*)
bnf_axiomatization (F_set: 'a) F for map: F_map rel: F_rel
abbreviation "F_bd \<equiv> bd_F"
(*REPLACE_F_END*)

end
