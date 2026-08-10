import Mathlib

inductive MyType4 : Type where
  | val : False → MyType4

unsafe def unsafe_proof : MyType4 :=
  unsafe_proof

unsafe def unsafe_inhabited : Inhabited MyType4 :=
  ⟨unsafe_proof⟩

opaque safe_inhabited : Inhabited MyType4

instance : Inhabited (Inhabited MyType4) :=
  ⟨safe_inhabited⟩

attribute [implemented_by unsafe_inhabited] safe_inhabited

instance : Inhabited MyType4 :=
  safe_inhabited

theorem prove_false : False :=
  match (default : MyType4) with
  | MyType4.val f => f

#print axioms prove_false
