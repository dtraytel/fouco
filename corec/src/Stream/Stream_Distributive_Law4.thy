header {* Distributive law for the sum of 2 *}

(* This is similar to Distributive_Law, but assumes a distributive law \<Lambda>4 over (SpK,\<Sigma>\<Sigma>4,F)
instead of (S,\<Sigma>\<Sigma>4,F): *)

theory Stream_Distributive_Law4
imports Stream_Integrate_New_Op4
begin

(* We assume (S,\<Sigma>\<Sigma>,F)-distributive law, where:
 -- S is the syntactic signature and T is its term extension (free algebra extension)
 -- F is the behavior functor  *)

(*
(* Distributive law: *)
consts \<Lambda>4 :: "('a \<times> 'a F) SpK \<Rightarrow> 'a \<Sigma>\<Sigma>4 F"

axiomatization where
  \<Lambda>4_natural: "\<Lambda>4 o SpKmap (f ** Fmap f) = Fmap (T1_map f) o \<Lambda>4"

*)


end