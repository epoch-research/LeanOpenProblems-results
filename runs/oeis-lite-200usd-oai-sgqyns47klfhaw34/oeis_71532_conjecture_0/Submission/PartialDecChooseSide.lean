import FormalConjectures.Util.ProblemImports
axiom P : Prop
partial def decLoop (P : Prop) : Decidable P := decLoop P

-- Can we prove either P or ¬P by using the same opaque decider repeatedly?
example : P ∨ ¬ P := by
  exact match decLoop P with | .isTrue h => .inl h | .isFalse h => .inr h

-- If we have proof that decLoop P is isTrue, then P. Can we get that proof by proof irrelevance/equality of Decidable?
example : P := by
  let d := decLoop P
  have hEq : d = Decidable.isTrue (show P from ?_) := ?_
  exact ?_
