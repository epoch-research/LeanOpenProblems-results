import FormalConjectures.Util.ProblemImports

open Nat Finset

def a (n : ℕ) : ℕ :=
  (filter (fun k => Nat.Prime ((k + 1) ^ (Nat.totient (n - k)) + k)) (Ico 1 n)).card

example : ¬ ∃ k, 0 < k ∧ k < 10 ∧ Nat.Prime ((k + 1) ^ (Nat.totient (10 - k) / 2) - k) := by
  rintro ⟨k, hk0, hklt, hp⟩
  interval_cases k <;> norm_num [Nat.totient, Nat.coprime] at hp
