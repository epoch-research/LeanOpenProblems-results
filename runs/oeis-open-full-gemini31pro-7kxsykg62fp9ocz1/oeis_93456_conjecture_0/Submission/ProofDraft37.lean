import FormalConjectures.Util.ProblemImports
open Nat Finset

lemma algebra_ineq (p M x : ℕ) (hp5 : 5 ≤ p) (hx : M - p + 3 ≤ x) (hM : p ≤ M) :
  p * M - p * p + 2 * p + 2 ≤ p * x := by
  zify [show p * p ≤ p * M by nlinarith, show p ≤ M by nlinarith]
  have hz : (M : ℤ) - (p : ℤ) + 3 ≤ (x : ℤ) := by
    zify [show p ≤ M by nlinarith] at hx
    exact hx
  nlinarith

lemma image_subset_S (p n M : ℕ) (hp5 : 5 ≤ p)
  (h_R : n * (n - 1) / 2 = p * M)
  (h_L : n * (n - 1) / 2 - n + 2 = p * M - p * p + 2 * p + 2)
  (hM : p ≤ M) :
  (Icc (M - p + 3) M).image (fun x => p * x) ⊆
  (Icc (n * (n - 1) / 2 - n + 2) (n * (n - 1) / 2)).filter (fun k => 1 < k ∧ ¬ k.Prime) := by
  intro y
  simp only [mem_image, mem_filter, mem_Icc]
  rintro ⟨x, ⟨hx1, hx2⟩, rfl⟩
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [h_L]
    exact algebra_ineq p M x hp5 hx1 hM
  · rw [h_R]
    exact Nat.mul_le_mul_left p hx2
  · have : p * 1 < p * x := by
      apply Nat.mul_lt_mul_of_pos_left
      · have : 3 ≤ M - p + 3 := by omega
        omega
      · omega
    omega
  · intro h_prime
    have hdvd : p ∣ p * x := dvd_mul_right p x
    have hx_gt1 : 1 < x := by
      have : 3 ≤ M - p + 3 := by omega
      omega
    have hp_gt1 : 1 < p := by omega
    have := h_prime.eq_one_or_self_of_dvd p hdvd
    rcases this with h1 | h2
    · omega
    · have : x = 1 := by nlinarith
      omega
