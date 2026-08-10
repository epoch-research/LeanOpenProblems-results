import FormalConjectures.Util.ProblemImports

open Nat Finset

example (hp : Nat.Prime ((1 + 1) ^ (Nat.totient (1408 - 1) / 2) - 1)) : False := by
  have ht : Nat.totient (1408 - 1) = 792 := by native_decide
  rw [ht] at hp
  norm_num at hp
  have hd : 3 ∣ (2 ^ 396 - 1 : ℕ) := by native_decide
  rcases hp.eq_one_or_self_of_dvd 3 hd with h | h
  · norm_num at h
  · have hlt : 3 < (2 ^ 396 - 1 : ℕ) := by native_decide
    omega

example (hp : Nat.Prime ((5 + 1) ^ (Nat.totient (1408 - 5) / 2) - 5)) : False := by
  have ht : Nat.totient (1408 - 5) = 1320 := by native_decide
  rw [ht] at hp
  norm_num at hp
  have hd : 8819 ∣ (6 ^ 660 - 5 : ℕ) := by native_decide
  rcases hp.eq_one_or_self_of_dvd 8819 hd with h | h
  · norm_num at h
  · have hlt : 8819 < (6 ^ 660 - 5 : ℕ) := by native_decide
    omega
