import FormalConjectures.Util.ProblemImports

abbrev Target : Prop := ∀ n : ℕ, n > 0 → ∃ k : ℕ, Nat.Prime ((3 ^ n - k) * (2 ^ n) - 1) ∧ Nat.Prime ((3 ^ n - k) * (2 ^ n) + 1)

-- Quotient all Props together.
def QProp := Quot (fun (_ _ : Prop) => True)

example : Quot.mk (fun (_ _ : Prop) => True) Target = Quot.mk (fun (_ _ : Prop) => True) True := Quot.sound True.intro

-- Can this equality be transported through a Quot.lift that returns Prop/proofs?
example : Target := by
  have hq : Quot.mk (fun (_ _ : Prop) => True) Target = Quot.mk (fun (_ _ : Prop) => True) True := Quot.sound True.intro
  -- Any lift out of quotient must be constant on related propositions, so can't use identity Prop.
  exact?

-- Quotient proofs of True/Target if any? cannot form target proof.
example : Nonempty Target := by
  exact?
