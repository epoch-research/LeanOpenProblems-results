import FormalConjectures.Util.ProblemImports

partial def church (P : Prop) : ∀ Q : Prop, (P → Q) → Q :=
  fun Q k => church P Q k

#print church
#print axioms church

example (P : Prop) : P := church P P (fun hp => hp)
#print axioms _example

partial def church2 (P : Prop) : ∀ Q : Prop, ((P → Q) → P) → P :=
  fun Q k => k (fun hp => church2 P Q k)

#print church2
example (P : Prop) : P := church2 P False (fun f => f (by contradiction))
#print axioms _example_1
