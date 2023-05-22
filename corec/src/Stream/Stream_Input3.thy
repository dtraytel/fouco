theory Stream_Input3
imports Stream_More_Corec_Upto2
begin

datatype_new (K3_set: 'a) K3 = I 'a for map: K3_map rel: K3_rel
abbreviation "bd_K3 \<equiv> natLeq"
type_synonym bd_type_K3 = nat

end
