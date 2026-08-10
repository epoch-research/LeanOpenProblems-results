import Mathlib

inductive MyProof2 (P : Prop) : Type where
  | mk : P → MyProof2 P
  | dummy : MyProof2 P

instance (P : Prop) : Inhabited (MyProof2 P) where
  default := MyProof2.dummy

unsafe def unsafe_proof (P : Prop) : MyProof2 P :=
  MyProof2.mk (unsafe_proof P |>.match_dummy) -- wait, how do we write the unsafe implementation?
-- We can just do a loop or cast. Since it's unsafe, we can write:
-- unsafe def unsafe_proof (P : Prop) : MyProof2 P :=
--   unsafe_cast () -- or whatever

-- Let's write a simple unsafe_proof:
unsafe def unsafe_proof (P : Prop) : MyProof2 P :=
  unsafe_proof P

@[implemented_by unsafe_proof]
opaque get_proof (P : Prop) : MyProof2 P

#print axioms get_proof
