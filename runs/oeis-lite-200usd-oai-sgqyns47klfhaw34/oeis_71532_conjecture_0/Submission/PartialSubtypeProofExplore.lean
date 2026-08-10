import FormalConjectures.Util.ProblemImports

partial def subAny (P : Nat → Prop) : {n : Nat // P n} := subAny P

theorem existsAny (P : Nat → Prop) : ∃ n, P n := ⟨(subAny P).1, (subAny P).2⟩
#print axioms existsAny
