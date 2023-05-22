header {* Distributive law for the sum of 2 *}

(* This is similar to Distributive_Law, but assumes a distributive law \<Lambda>7 over (SpK,\<Sigma>\<Sigma>7,F)
instead of (S,\<Sigma>\<Sigma>7,F): *)

theory Stream_Distributive_Law7
imports Stream_Integrate_New_Op7
begin

(* We assume (S,\<Sigma>\<Sigma>,F)-distributive law, where:
 -- S is the syntactic signature and T is its term extension (free algebra extension)
 -- F is the behavior functor  *)

(*
(* Distributive law: *)
consts \<Lambda>7 :: "('a \<times> 'a F) SpK \<Rightarrow> 'a \<Sigma>\<Sigma>7 F"

axiomatization where
  \<Lambda>7_natural: "\<Lambda>7 o SpKmap (f ** Fmap f) = Fmap (T1_map f) o \<Lambda>7"

*)


end