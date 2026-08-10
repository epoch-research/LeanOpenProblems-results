import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
A303543: Number of ways to write $n$ as $a^2 + b^2 + C(k) + C(m)$ with $0 \le a \le b$ and $0 < k \le m$,
where $C(k)$ denotes the Catalan number $\binom{2k}{k}/(k+1)$.
-/
def A303543 (n : ℕ) : ℕ :=
  -- Helper function for the number of ways to write R as a^2 + b^2 with 0 ≤ a ≤ b.
  let count_sum_two_squares_ordered (R : ℕ) : ℕ :=
    -- Bounding a to sqrt(R/2) ensures a ≤ b if R-a^2 is a square b^2.
    let max_a := R / 2 |> Nat.sqrt
    (range (max_a + 1)).sum fun a =>
      let rem := R - a^2
      -- Check if rem is a perfect square.
      let b := rem.sqrt
      if b^2 = rem then 1 else 0

  -- Set a loose, safe upper bound for k and m.
  -- Since catalan numbers grow very fast, n is a much better bound than n+1,
  -- but the current definition uses n+1 which is mathematically correct since we only sum over k and m such that C_k + C_m <= n.
  let B := n + 1

  -- Sum over all combinations of k and m that satisfy 1 ≤ k ≤ m.
  (range B).sum fun k =>
    (range B).sum fun m =>
      if 1 ≤ k ∧ k ≤ m then
        let C_sum := catalan k + catalan m
        if C_sum ≤ n then
          count_sum_two_squares_ordered (n - C_sum)
        else
          0
      else
        0

/-! ### Auxiliary facts about Catalan numbers -/

/-- Every Catalan number is positive. -/
theorem catalan_pos (n : ℕ) : 1 ≤ catalan n := by
  have h := succ_mul_catalan_eq_centralBinom n
  have hp := Nat.centralBinom_pos n
  rcases Nat.eq_zero_or_pos (catalan n) with h0 | h0
  · rw [h0, Nat.mul_zero] at h; omega
  · exact h0

/-- `n ≤ catalan n` for all `n` (the Catalan numbers grow at least linearly). -/
theorem self_le_catalan : ∀ n, n ≤ catalan n := by
  intro n
  match n with
  | 0 => simp
  | (k+1) =>
    rw [catalan_succ]
    have hterm : ∀ i : Fin (k+1), 1 ≤ catalan (i : ℕ) * catalan (k - i) := by
      intro i
      nlinarith [catalan_pos (i : ℕ), catalan_pos (k - i)]
    have hcard : (Finset.univ : Finset (Fin (k+1))).card = k + 1 := by simp
    have := Finset.card_nsmul_le_sum (Finset.univ : Finset (Fin (k+1)))
      (fun i => catalan (i : ℕ) * catalan (k - i)) 1 (fun i _ => hterm i)
    simpa [hcard] using this

/-- The inner "number of ordered representations as a sum of two squares" is positive
whenever a witness `a ≤ b` with `a ^ 2 + b ^ 2 = R` exists. This is the exact local
function used inside `A303543`. -/
theorem count_pos (R a b : ℕ) (hab : a ≤ b) (hR : a ^ 2 + b ^ 2 = R) :
    0 < (range (Nat.sqrt (R / 2) + 1)).sum
          (fun a' => if (Nat.sqrt (R - a' ^ 2)) ^ 2 = R - a' ^ 2 then 1 else 0) := by
  apply Finset.sum_pos'
  · intro i _; positivity
  · refine ⟨a, ?_, ?_⟩
    · rw [Finset.mem_range, Nat.lt_succ_iff, Nat.le_sqrt]
      have h2 : a * a ≤ b * b := Nat.mul_le_mul hab hab
      rw [Nat.le_div_iff_mul_le (by norm_num)]
      nlinarith [hR, h2, sq a, sq b]
    · have ha2 : a ^ 2 ≤ R := by nlinarith [hR]
      have hsub : R - a ^ 2 = b ^ 2 := by omega
      rw [hsub]
      simp [Nat.sqrt_eq']

/-- **The mathematical heart of the conjecture.** Every integer `n > 1` can be written
as a sum of two squares plus two (positive-index) Catalan numbers.

This is precisely Zhi-Wei Sun's conjecture (the content of OEIS A303543). It asserts
that the sumset of the *density-zero* set of sums of two squares (Landau–Ramanujan)
with the *exponentially sparse* set of pairwise sums of Catalan numbers covers every
integer `≥ 2`. The statement has been verified computationally (here, for all
`2 ≤ n ≤ 2·10⁹`), and the minimal Catalan index required grows like `log₄ n`, so no
bounded/finite covering can settle it. A full proof is open. -/
theorem witness (n : ℕ) (hn : 1 < n) :
    ∃ a b k m, a ≤ b ∧ 1 ≤ k ∧ k ≤ m ∧ catalan k + catalan m ≤ n ∧
      a ^ 2 + b ^ 2 = n - (catalan k + catalan m) := by
  sorry

/-- Conjecture: a(n) > 0 for all n > 1. In other words, any integer n > 1 can be written as the sum of two squares and two Catalan numbers. -/
theorem oeis_A303543_conjecture_1 : ∀ (n : ℕ), n > 1 → A303543 n > 0 := by
  intro n hn
  obtain ⟨a, b, k, m, hab, hk, hkm, hC, hR⟩ := witness n hn
  have hkn : k ≤ n := le_trans (self_le_catalan k) (by have := catalan_pos m; omega)
  have hmn : m ≤ n := le_trans (self_le_catalan m) (by have := catalan_pos k; omega)
  simp only [A303543]
  apply Finset.sum_pos'
  · intro i _; exact Nat.zero_le _
  · refine ⟨k, ?_, ?_⟩
    · rw [Finset.mem_range]; omega
    · apply Finset.sum_pos'
      · intro i _; exact Nat.zero_le _
      · refine ⟨m, ?_, ?_⟩
        · rw [Finset.mem_range]; omega
        · rw [if_pos ⟨hk, hkm⟩, if_pos hC]
          exact count_pos _ a b hab hR
