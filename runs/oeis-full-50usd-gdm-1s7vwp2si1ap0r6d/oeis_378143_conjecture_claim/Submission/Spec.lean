import FormalConjectures.Util.ProblemImports

open Nat Set

theorem oeis_378143_conjecture_claim :
  ∀ (n : ℕ),
    Nat.Prime (10 ^ (2 ^ n) + 1) →
      Nat.Prime (4 ^ (2 ^ n) + 1) ∨ Nat.Prime (6 ^ (2 ^ n) + 1) := by
  intro n hp
  rcases le_or_gt n 12 with hn | hn
  · interval_cases n
    · right; norm_num
    · left; norm_num
    · exfalso
      apply Nat.not_prime_of_dvd_of_lt (by norm_num : 73 ∣ 10 ^ 4 + 1) (by decide) (by decide) hp
    · exfalso
      apply Nat.not_prime_of_dvd_of_lt (by norm_num : 17 ∣ 10 ^ 8 + 1) (by decide) (by decide) hp
    · exfalso
      apply Nat.not_prime_of_dvd_of_lt (by norm_num : 353 ∣ 10 ^ 16 + 1) (by decide) (by decide) hp
    · exfalso
      apply Nat.not_prime_of_dvd_of_lt (by norm_num : 19841 ∣ 10 ^ 32 + 1) (by decide) (by decide) hp
    · exfalso
      apply Nat.not_prime_of_dvd_of_lt (by norm_num : 1265011073 ∣ 10 ^ 64 + 1) (by decide) (by decide) hp
    · exfalso
      apply Nat.not_prime_of_dvd_of_lt (by norm_num : 257 ∣ 10 ^ 128 + 1) (by decide) (by decide) hp
    · exfalso
      apply Nat.not_prime_of_dvd_of_lt (by norm_num : 10753 ∣ 10 ^ 256 + 1) (by decide) (by decide) hp
    · exfalso
      apply Nat.not_prime_of_dvd_of_lt (by norm_num : 1514497 ∣ 10 ^ 512 + 1) (by decide) (by decide) hp
    · exfalso
      apply Nat.not_prime_of_dvd_of_lt (by norm_num : 1856104284667693057 ∣ 10 ^ 1024 + 1) (by decide) (by decide) hp
    · exfalso
      apply Nat.not_prime_of_dvd_of_lt (by norm_num : 106907803649 ∣ 10 ^ 2048 + 1) (by decide) (by decide) hp
    · exfalso
      apply Nat.not_prime_of_dvd_of_lt (by norm_num : 458924033 ∣ 10 ^ 4096 + 1) (by decide) (by decide) hp
  · sorry
