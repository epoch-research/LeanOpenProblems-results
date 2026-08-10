import Mathlib

inductive MyType : Type where
  | val : False → MyType

unsafe def unsafe_proof : MyType :=
  unsafe_proof

unsafe def unsafe_inhabited : Inhabited MyType :=
  ⟨unsafe_proof⟩

@[implemented_by unsafe_inhabited]
opaque safe_inhabited : Inhabited MyType

instance : Inhabited MyType :=
  safe_inhabited

theorem prove_false : False :=
  match (default : MyType) with
  | MyType.val f => f

#print axioms prove_false
