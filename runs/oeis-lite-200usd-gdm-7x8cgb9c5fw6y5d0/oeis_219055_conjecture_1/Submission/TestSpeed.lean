import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 100000
set_option maxHeartbeats 15000000

def primes_under_182 : List ℕ :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181]

def goldbach_decide (n : ℕ) : Bool :=
  primes_under_182.any (fun p => p < n && decide (Nat.Prime (n - p)))

def check_goldbach_linear (low : ℕ) (count : ℕ) : Bool :=
  match count with
  | 0 => true
  | c + 1 => (if 4 ≤ low && low % 2 == 0 then goldbach_decide low else true) && check_goldbach_linear (low + 1) c

lemma check_goldbach_linear_correct :
    ∀ count low, check_goldbach_linear low count = true →
    ∀ n, low ≤ n → n < low + count → 4 ≤ n → Even n → goldbach_decide n = true := by
  intro count
  induction count with
  | zero =>
    intro low h n h1 h2
    omega
  | succ c ih =>
    intro low h n h1 h2 h4 heven
    dsimp [check_goldbach_linear] at h
    rw [Bool.and_eq_true] at h
    by_cases hn : n = low
    · subst hn
      have h_cond : (4 ≤ n ∧ n % 2 = 0) := ⟨h4, Nat.even_iff.mp heven⟩
      have h_cond_bool : (4 ≤ n && n % 2 == 0) = true := by
        simp [h_cond.1, h_cond.2]
      have h1 := h.1
      rw [h_cond_bool] at h1
      exact h1
    · have h_gt : low + 1 ≤ n := by omega
      have h_lt : n < low + 1 + c := by omega
      exact ih (low + 1) h.2 n h_gt h_lt h4 heven

theorem goldbach_of_decide (n : ℕ) (h : goldbach_decide n = true) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ n = p + q := by
  sorry

theorem goldbach_small_test (n : ℕ) (h4 : 4 ≤ n) (hn : n ≤ 500) (he : Even n) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ n = p + q := by
  have h_cases : n < 250 ∨ (250 ≤ n ∧ n ≤ 500) := by omega
  rcases h_cases with h | h
  · exact goldbach_of_decide n (check_goldbach_linear_correct 250 0 (by decide) n (by omega) (by omega) h4 he)
  · exact goldbach_of_decide n (check_goldbach_linear_correct 251 250 (by decide) n h.1 (by omega) h4 he)
