import FormalConjectures.Util.ProblemImports

open Finset Nat

def a (n : ℕ) : ℤ :=
  Finset.sum (range (n + 1)) fun k =>
    let m : ℕ := n - k;
    (n.choose k : ℤ) *
    ((n + k).choose k : ℤ) *
    ((2 * k).choose k : ℤ) *
    (centralBinom m : ℤ) *
    ((-8 : ℤ) ^ m)

def conjecture_sum (n : ℕ) : ℤ :=
  Finset.sum (range n) fun k =>
    let k_int : ℤ := k;
    let exp : ℕ := n - 1 - k;
    (-1 : ℤ) ^ k * (4 * k_int + 1) * (48 : ℤ) ^ exp * a k

-- Lemma A: positivity of (-1)^k a(k)
theorem barA_pos (k : ℕ) : 0 < (-1 : ℤ) ^ k * a k := by
  sorry

-- Lemma D: divisibility
theorem div_n (n : ℕ) (hn : n > 0) : (n : ℤ) ∣ conjecture_sum n := by
  sorry

-- Each term positive
theorem term_pos (n k : ℕ) (hk : k < n) :
    0 < (-1 : ℤ) ^ k * (4 * (k:ℤ) + 1) * (48 : ℤ) ^ (n - 1 - k) * a k := by
  have h1 : 0 < (-1 : ℤ) ^ k * a k := barA_pos k
  have h2 : (0:ℤ) < 4 * (k:ℤ) + 1 := by positivity
  have h3 : (0:ℤ) < (48 : ℤ) ^ (n - 1 - k) := by positivity
  have : (-1 : ℤ) ^ k * (4 * (k:ℤ) + 1) * (48 : ℤ) ^ (n - 1 - k) * a k
       = (4 * (k:ℤ) + 1) * (48 : ℤ) ^ (n - 1 - k) * ((-1 : ℤ) ^ k * a k) := by ring
  rw [this]
  positivity

theorem cs_pos (n : ℕ) (hn : n > 0) : 0 < conjecture_sum n := by
  unfold conjecture_sum
  apply Finset.sum_pos
  · intro k hk
    rw [Finset.mem_range] at hk
    exact term_pos n k hk
  · rw [Finset.nonempty_range_iff]
    omega

theorem main (n : ℕ) (hn : n > 0) :
    ∃ q : ℤ, (n : ℤ) * q = conjecture_sum n ∧ q > 0 := by
  obtain ⟨q, hq⟩ := div_n n hn
  refine ⟨q, hq.symm, ?_⟩
  have hpos := cs_pos n hn
  have hn' : (0:ℤ) < n := by exact_mod_cast hn
  have hmul : (0:ℤ) < (n:ℤ) * q := by rw [← hq]; exact hpos
  by_contra h
  push_neg at h
  nlinarith [mul_nonpos_of_nonneg_of_nonpos (le_of_lt hn') h]
