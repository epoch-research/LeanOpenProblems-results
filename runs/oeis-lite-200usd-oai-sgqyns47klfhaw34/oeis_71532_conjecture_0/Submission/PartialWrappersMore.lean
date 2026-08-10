import FormalConjectures.Util.ProblemImports

partial def loopInhabited (P : Prop) : Inhabited P := loopInhabited P
partial def loopNonemptyType (α : Type) : Nonempty α := loopNonemptyType α
partial def loopSubtype (P : Prop) : {b : Bool // b = true → P} := loopSubtype P
partial def loopSigma (P : Prop) : Sigma (fun b : Bool => b = true → P) := loopSigma P

#print axioms loopInhabited
#print axioms loopNonemptyType
#print axioms loopSubtype
#print axioms loopSigma

example (P : Prop) : P := by
  let s := loopSubtype P
  cases s with
  | mk b hb =>
    by_cases h : b = true
    · exact hb h
    · cases b <;> simp at h

#print axioms _example
