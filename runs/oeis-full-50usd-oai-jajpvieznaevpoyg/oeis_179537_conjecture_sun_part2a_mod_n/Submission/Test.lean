import FormalConjectures.Util.ProblemImports
open Finset Nat Int
#check Int.ModEq
#check Int.modEq_zero_iff_dvd
#check Int.ModEq.zero
#check Int.ModEq.refl
#check Int.dvd_iff_modEq_zero
#check Nat.dvd_iff_modEq_zero
example : ∀ n : ℕ, n ≥ 1 → (37:ℤ) ≡ 0 [ZMOD n] := by
  intro n hn
  -- omega
  simp [Int.ModEq]
