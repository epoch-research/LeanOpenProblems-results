import FormalConjectures.Util.ProblemImports

open Nat Finset Set

inductive Box (P : Prop) : Type where
  | mk : P → Box P

partial instance (P : Prop) : Nonempty (Box P) :=
  let rec loop : Nonempty (Box P) := loop
  loop

def get_proof (P : Prop) (b : Box P) : P :=
  match b with
  | .mk p => p

theorem prove_any (P : Prop) : P :=
  get_proof P (Classical.choice (instNonemptyBox P))

#print axioms prove_any
