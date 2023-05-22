theory Stream_Input7
imports Stream_More_Corec_Upto6
begin

datatype_new (K7_set: 'a) K7 = I 'a for map: K7_map rel: K7_rel
abbreviation "bd_K7 \<equiv> natLeq"
type_synonym bd_type_K7 = nat

end
