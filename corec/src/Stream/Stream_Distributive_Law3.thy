header {* Distributive law for the sum of 2 *}

(* This is similar to Distributive_Law, but assumes a distributive law \<Lambda>3 over (SpK,\<Sigma>\<Sigma>3,F)
instead of (S,\<Sigma>\<Sigma>3,F): *)

theory Stream_Distributive_Law3
imports Stream_Integrate_New_Op3
begin

(* We assume (S,\<Sigma>\<Sigma>,F)-distributive law, where:
 -- S is the syntactic signature and T is its term extension (free algebra extension)
 -- F is the behavior functor  *)

(*
(* Distributive law: *)
consts \<Lambda>3 :: "('a \<times> 'a F) SpK \<Rightarrow> 'a \<Sigma>\<Sigma>3 F"

axiomatization where
  \<Lambda>3_natural: "\<Lambda>3 o SpKmap (f ** Fmap f) = Fmap (T1_map f) o \<Lambda>3"

*)


end