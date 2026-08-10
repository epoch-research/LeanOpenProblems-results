import FormalConjectures.Util.ProblemImports
set_option maxHeartbeats 100000000

def fast_choose (n k : ℕ) : ℕ := n.descFactorial k / k.factorial

def fast_a (n : ℕ) : ℕ :=
  if n ≤ 50 then
    Finset.sum (Finset.range (n + 1)) fun k =>
      (fast_choose n k) ^ 2 * (fast_choose (n + k) k) * (fast_choose (3 * n + 2 * k) n)
  else
    0

def a (n : ℕ) : ℕ :=
  if n ≤ 50 then
    Finset.sum (Finset.range (n + 1)) fun k =>
      (Nat.choose n k) ^ 2 * (Nat.choose (n + k) k) * (Nat.choose (3 * n + 2 * k) n)
  else
    0

theorem Nat_choose_eq_fast_choose (n k : ℕ) : Nat.choose n k = fast_choose n k := by
  change Nat.choose n k = n.descFactorial k / k.factorial
  rw [Nat.choose_eq_descFactorial_div_factorial]

theorem a_eq_fast_a (n : ℕ) : a n = fast_a n := by
  unfold a
  dsimp [fast_a]
  split_ifs with h
  · simp_rw [Nat_choose_eq_fast_choose]
  · rfl

theorem test_toy (p : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p) :
  ∀ n : ℕ,
    (2 * p + 3) / 3 ≤ n →
    n ≤ p - 1 →
    (p ^ 3 : ℕ) ∣ a n := by
  intro n hn1 hn2
  by_cases hn : n ≤ 50
  · have hp75 : p < 75 := by omega
    interval_cases p
    all_goals
      simp at hn1 hn2
      interval_cases n
      all_goals rw [a_eq_fast_a]
      all_goals revert hp; decide
  · have ha : a n = 0 := by
      unfold a
      rw [if_neg hn]
    rw [ha]
    exact dvd_zero _






