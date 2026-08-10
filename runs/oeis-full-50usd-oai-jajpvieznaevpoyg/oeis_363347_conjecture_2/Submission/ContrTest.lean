import FormalConjectures.Util.ProblemImports
open Rat Nat
example (p : ℕ) (hp : p.Prime ∧ (p ≡ 1 [MOD 10] ∨ p ≡ 9 [MOD 10])) : False := by
  rcases hp with ⟨hpr, hmod⟩
  rcases hmod with h|h <;> rw [Nat.ModEq] at h
  · omega
  · omega
