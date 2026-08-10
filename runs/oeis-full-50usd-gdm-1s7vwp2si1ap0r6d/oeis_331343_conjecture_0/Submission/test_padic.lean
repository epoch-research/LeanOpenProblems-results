import FormalConjectures.Util.ProblemImports

open Nat Finset

-- OEIS 331343 definition
def A331343 (n : ℕ) : ℕ :=
  let L : ℕ := (Ico 1 (n + 1)).lcm id
  (Ico 1 (n + 1)).sum fun k : ℕ ↦ (L / k) * (2 ^ (k - 1) - 1)

def a (n : ℕ) : ℕ := A331343 n

lemma test_conjecture (n : ℕ) (hn : n > 3) (hp : ¬ Nat.Prime n) (h_div : n^3 ∣ a n) (odd_of_dvd_a : ∀ {m : ℕ}, m ≥ 2 → m^3 ∣ a m → m % 2 = 1) : False := by
  have h_odd : n % 2 = 1 := odd_of_dvd_a (by omega) h_div
  by_cases hn9 : n = 9
  · subst hn9
    have h_not : ¬ (9^3 ∣ a 9) := by decide
    exact h_not h_div
  · sorry
