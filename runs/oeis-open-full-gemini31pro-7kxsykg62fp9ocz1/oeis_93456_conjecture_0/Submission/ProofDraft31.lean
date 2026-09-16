import FormalConjectures.Util.ProblemImports
open Nat Finset

lemma sum_subset_le (s t : Finset ℕ) (f : ℕ → ℕ) (h : s ⊆ t) :
  ∑ x ∈ s, f x ≤ ∑ x ∈ t, f x := by
  exact sum_le_sum_of_subset_of_nonneg h (fun _ _ => zero_le _)

lemma image_subset_S (p n : ℕ) (hp5 : 5 ≤ p) (M : ℕ)
  (h_R : n * (n - 1) / 2 = p * M)
  (h_L : n * (n - 1) / 2 - n + 2 = p * M - p * p + 2 * p + 2)
  : (Icc (M - p + 3) M).image (fun x => p * x) ⊆ (Icc (n * (n - 1) / 2 - n + 2) (n * (n - 1) / 2)).filter (fun k => 1 < k ∧ ¬ k.Prime) := by
  intro y
  simp only [mem_image, mem_filter, mem_Icc]
  rintro ⟨x, ⟨hx1, hx2⟩, rfl⟩
  -- here we just need to prove p * x is in the interval and composite
  sorry
