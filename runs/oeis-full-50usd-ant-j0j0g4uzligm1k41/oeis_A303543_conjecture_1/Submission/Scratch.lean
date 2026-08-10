import FormalConjectures.Util.ProblemImports

open Nat Finset

def A303543 (n : ℕ) : ℕ :=
  let count_sum_two_squares_ordered (R : ℕ) : ℕ :=
    let max_a := R / 2 |> Nat.sqrt
    (range (max_a + 1)).sum fun a =>
      let rem := R - a^2
      let b := rem.sqrt
      if b^2 = rem then 1 else 0
  let B := n + 1
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

-- helper: 1 ≤ catalan n
theorem catalan_pos (n : ℕ) : 1 ≤ catalan n := by
  have h := succ_mul_catalan_eq_centralBinom n
  have hp := Nat.centralBinom_pos n
  rcases Nat.eq_zero_or_pos (catalan n) with h0 | h0
  · rw [h0, Nat.mul_zero] at h; omega
  · exact h0

theorem self_le_catalan : ∀ n, n ≤ catalan n := by
  intro n
  match n with
  | 0 => simp
  | (k+1) =>
    rw [catalan_succ]
    -- sum over Fin (k+1) of terms each ≥ 1, so ≥ k+1
    have : ∀ i : Fin (k+1), 1 ≤ catalan (i : ℕ) * catalan (k - i) := by
      intro i
      have := catalan_pos (i : ℕ)
      have := catalan_pos (k - i)
      nlinarith [catalan_pos (i : ℕ), catalan_pos (k - i)]
    have hcard : (Finset.univ : Finset (Fin (k+1))).card = k + 1 := by simp
    have := Finset.card_nsmul_le_sum (Finset.univ : Finset (Fin (k+1)))
      (fun i => catalan (i : ℕ) * catalan (k - i)) 1 (fun i _ => this i)
    simpa [hcard] using this

theorem witness (n : ℕ) (hn : 1 < n) :
    ∃ a b k m, a ≤ b ∧ 1 ≤ k ∧ k ≤ m ∧ catalan k + catalan m ≤ n ∧
      a ^ 2 + b ^ 2 = n - (catalan k + catalan m) := by
  sorry

-- count helper: the inner sum-of-two-squares count is positive given a witness
theorem count_pos (R a b : ℕ) (hab : a ≤ b) (hR : a^2 + b^2 = R) :
    0 < (range (Nat.sqrt (R/2) + 1)).sum
          (fun a' => if (Nat.sqrt (R - a'^2))^2 = R - a'^2 then 1 else 0) := by
  apply Finset.sum_pos'
  · intro i _; positivity
  · refine ⟨a, ?_, ?_⟩
    · -- a ∈ range (sqrt (R/2) + 1)
      rw [Finset.mem_range, Nat.lt_succ_iff, Nat.le_sqrt]
      have h2 : a * a ≤ b * b := Nat.mul_le_mul hab hab
      rw [Nat.le_div_iff_mul_le (by norm_num)]
      nlinarith [hR, h2, sq a, sq b]
    · -- the if condition holds and value 1 > 0
      have ha2 : a^2 ≤ R := by nlinarith [hR]
      have hsub : R - a^2 = b^2 := by omega
      rw [hsub]
      simp [Nat.sqrt_eq']

theorem main (n : ℕ) (hn : n > 1) : A303543 n > 0 := by
  obtain ⟨a, b, k, m, hab, hk, hkm, hC, hR⟩ := witness n hn
  have hkn : k ≤ n := le_trans (self_le_catalan k) (by
    have := catalan_pos m; omega)
  have hmn : m ≤ n := le_trans (self_le_catalan m) (by
    have := catalan_pos k; omega)
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

