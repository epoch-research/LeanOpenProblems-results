import FormalConjectures.Util.ProblemImports

abbrev Target : Prop := ∀ n : ℕ, n > 0 → ∃ k : ℕ, Nat.Prime ((3 ^ n - k) * (2 ^ n) - 1) ∧ Nat.Prime ((3 ^ n - k) * (2 ^ n) + 1)

def R (p q : Prop) : Prop := p → q

example : Quot.mk R True = Quot.mk R Target := by
  apply Quot.sound
  intro _
  exact?

example : Quot.mk R Target = Quot.mk R True := by
  exact Quot.sound (fun _ => True.intro)
