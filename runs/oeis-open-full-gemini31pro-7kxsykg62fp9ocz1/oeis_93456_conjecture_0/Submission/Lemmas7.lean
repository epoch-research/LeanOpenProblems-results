import FormalConjectures.Util.ProblemImports
open Nat Finset

lemma sum_Icc_shift (p M n : ℕ) (f : ℕ → ℕ) :
  ∑ y ∈ Icc (p * M + 1) (p * M + n), f y = ∑ k ∈ Icc 1 n, f (p * M + k) := by
  have : Icc (p * M + 1) (p * M + n) = (Icc 1 n).image (fun k => p * M + k) := by
    ext x
    simp only [mem_image, mem_Icc]
    constructor
    · rintro ⟨hx1, hx2⟩
      refine ⟨x - p * M, ⟨by omega, by omega⟩, by omega⟩
    · rintro ⟨k, ⟨hk1, hk2⟩, rfl⟩
      omega
  rw [this, sum_image]
  intro a _ b _ hab
  dsimp at hab
  omega
