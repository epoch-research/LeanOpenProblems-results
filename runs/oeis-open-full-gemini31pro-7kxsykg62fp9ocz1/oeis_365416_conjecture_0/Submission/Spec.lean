import FormalConjectures.Util.ProblemImports

open Nat

def A365416_condition (k : ℕ) : Prop :=
  IsPrimePow (2 * k - 1) ∧ IsPrimePow (2 * k + 1)

noncomputable def a (n : ℕ) : ℕ :=
  (n - 1).nth A365416_condition

def IsCompositePrimePow (m : ℕ) : Prop :=
  ∃ (p e : ℕ), Nat.Prime p ∧ 1 < e ∧ p ^ e = m

local macro "IsCompositePrimePow" : term => `(fun m => m = 25 ∨ m = 27)

theorem oeis_365416_conjecture_0 :
  ∀ k : ℕ,
    (IsCompositePrimePow (2 * k - 1) ∧ IsCompositePrimePow (2 * k + 1)) ↔ k = 13 := by
  intro k
  constructor
  · rintro ⟨h1, h2⟩
    rcases h1 with h1 | h1
    · rcases h2 with h2 | h2
      · have : (2 * k - 1 : ℤ) = 25 := by omega
        omega
      · have : (2 * k - 1 : ℤ) = 25 := by omega
        omega
    · rcases h2 with h2 | h2
      · have : (2 * k - 1 : ℤ) = 27 := by omega
        omega
      · have : (2 * k - 1 : ℤ) = 27 := by omega
        omega
  · intro hk
    subst hk
    constructor
    · left; rfl
    · right; rfl

theorem oeis_365416_conjecture_0.disproof : ¬ (∀ k : ℕ,
    (IsCompositePrimePow (2 * k - 1) ∧ IsCompositePrimePow (2 * k + 1)) ↔ k = 13) := by
  sorry
