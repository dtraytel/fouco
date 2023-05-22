header {* Distributive law for the sum of 2 *}

(* This is similar to Distributive_Law, but assumes a distributive law \<Lambda>6 over (SpK,\<Sigma>\<Sigma>6,F)
instead of (S,\<Sigma>\<Sigma>6,F): *)

theory Stream_Distributive_Law6
imports Stream_Integrate_New_Op6
begin

(* We assume (S,\<Sigma>\<Sigma>,F)-distributive law, where:
 -- S is the syntactic signature and T is its term extension (free algebra extension)
 -- F is the behavior functor  *)

(*
(* Distributive law: *)
consts \<Lambda>6 :: "('a \<times> 'a F) SpK \<Rightarrow> 'a \<Sigma>\<Sigma>6 F"

axiomatization where
  \<Lambda>6_natural: "\<Lambda>6 o SpKmap (f ** Fmap f) = Fmap (T1_map f) o \<Lambda>6"

*)


end