import FormalConjectures.Util.ProblemImports
open Nat
example : ¬ (0 > (0 : ℕ)) := by omega
example : ∃ k : ℕ, Nat.Prime ((3 ^ 1 - k) * (2 ^ 1) - 1) ∧ Nat.Prime ((3 ^ 1 - k) * (2 ^ 1) + 1) := by
  use 1
  norm_num
example : ∃ k : ℕ, Nat.Prime ((3 ^ 2 - k) * (2 ^ 2) - 1) ∧ Nat.Prime ((3 ^ 2 - k) * (2 ^ 2) + 1) := by
  use 8
  norm_num
-- n=0 also has k=0? center 1, 0 and 2 not prime; k? underflow center 0 no.
example : ¬ ∃ k : ℕ, Nat.Prime ((3 ^ 0 - k) * (2 ^ 0) - 1) ∧ Nat.Prime ((3 ^ 0 - k) * (2 ^ 0) + 1) := by
  rintro ⟨k,h⟩
  interval_cases k <;> norm_num at h
