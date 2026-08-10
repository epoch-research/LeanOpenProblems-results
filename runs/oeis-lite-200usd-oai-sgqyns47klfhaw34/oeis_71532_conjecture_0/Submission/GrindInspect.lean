import FormalConjectures.Util.ProblemImports
#check Lean.Grind.alreadyNorm
#print Lean.Grind.alreadyNorm
#check Lean.Grind.em
#print Lean.Grind.em
#check Lean.Grind.of_lookahead
#check Lean.Grind.not_not
#check Lean.Grind.eq_true_eq
example (P : Prop) : P := by
  have h := Lean.Grind.em P
  -- inspect goals with cases
  cases h with
  | inl hp =>
    fail_if_success exact hp
    simp [Lean.Grind.alreadyNorm] at hp
    fail_if_success exact hp
    sorry
  | inr hn =>
    simp [Lean.Grind.alreadyNorm] at hn
    sorry
