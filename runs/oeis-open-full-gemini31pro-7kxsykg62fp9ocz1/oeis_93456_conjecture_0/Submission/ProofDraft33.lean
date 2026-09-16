import FormalConjectures.Util.ProblemImports
open Nat Finset

lemma image_subset_S (p n : ℕ) (hp5 : 5 ≤ p) (M : ℕ) (hp : p.Prime)
  (h_R : n * (n - 1) / 2 = p * M)
  (h_L : n * (n - 1) / 2 - n + 2 = p * M - p * p + 2 * p + 2)
  : (Icc (M - p + 3) M).image (fun x => p * x) ⊆ (Icc (n * (n - 1) / 2 - n + 2) (n * (n - 1) / 2)).filter (fun k => 1 < k ∧ ¬ k.Prime) := by
  intro y
  simp only [mem_image, mem_filter, mem_Icc]
  rintro ⟨x, ⟨hx1, hx2⟩, rfl⟩
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [h_L]
    nlinarith
  · rw [h_R]
    nlinarith
  · have : p * x ≥ 5 * 1 := by nlinarith
    linarith
  · intro h_prime
    have : p ∣ p * x := dvd_mul_right p x
    have hx_gt : x > 1 := by
      -- since p >= 5, x >= M - p + 3 ... wait, we need M
      sorry
    -- p * x is prime, but p divides it and p * x > p, contradiction
    sorry
