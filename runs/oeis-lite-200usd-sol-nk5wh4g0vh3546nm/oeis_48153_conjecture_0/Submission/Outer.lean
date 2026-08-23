import FormalConjectures.Util.ProblemImports

open Finset

def A048153 (n : ℕ) : ℕ :=
  Finset.sum (Finset.range n) (fun k => k ^ 2 % n)

private def negSquareSum (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range n, (n - (k ^ 2 % n)) % n

private lemma pair_le (n k : ℕ) (hn : 0 < n) :
    k ^ 2 % n + (n - (k ^ 2 % n)) % n ≤ n := by
  have hr : k ^ 2 % n < n := Nat.mod_lt _ hn
  by_cases hz : k ^ 2 % n = 0
  · simp [hz]
  have hs : n - k ^ 2 % n < n := Nat.sub_lt hn (Nat.zero_lt_of_ne_zero hz)
  rw [Nat.mod_eq_of_lt hs]
  omega

private lemma sums_le (n : ℕ) :
    A048153 n + negSquareSum n ≤ n * (n - 1) := by
  rcases n with _ | m
  · simp [A048153, negSquareSum]
  rw [A048153, negSquareSum, ← Finset.sum_add_distrib]
  rw [Finset.sum_range_succ']
  simp

  calc
    ∑ x ∈ Finset.range m, ((x + 1) ^ 2 % (m + 1) +
        (m + 1 - (x + 1) ^ 2 % (m + 1)) % (m + 1))
        ≤ ∑ _x ∈ Finset.range m, (m + 1) := by
          exact Finset.sum_le_sum (fun i _ ↦ pair_le (m + 1) (i + 1) (by omega))
    _ = (m + 1) * ((m + 1) - 1) := by simp [Nat.mul_comm]

private lemma result_of_excess
    (hexcess : ∀ n : ℕ, A048153 n ≤ negSquareSum n)
    (n : ℕ) (h : 1 ≤ n) :
    A048153 n ≤ (n ^ 2 - 1) / 2 := by
  have he := hexcess n
  have hs := sums_le n
  have h2 : 2 * A048153 n ≤ n * (n - 1) := by omega
  have hb : A048153 n ≤ n * (n - 1) / 2 := by
    exact (Nat.le_div_iff_mul_le (by omega)).2 (by simpa [mul_comm] using h2)
  apply hb.trans
  apply Nat.div_le_div_right
  rcases n with _ | m
  · omega
  simp [pow_two, Nat.mul_add, Nat.add_mul]
