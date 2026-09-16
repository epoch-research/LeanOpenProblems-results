import FormalConjectures.Util.ProblemImports
open Nat Int Finset

def f (k : ℕ) : ℤ := ((-1 : ℤ)^k) * ((factorial 1194648 : ℤ) / (k : ℤ))

lemma sum_multiples :
  ∑ k ∈ (Icc 1 1194648).filter (fun x => 1093 ∣ x), f k =
  ∑ m ∈ Icc 1 1092, f (m * 1093) := by
  have H : (Icc 1 1194648).filter (fun x => 1093 ∣ x) = (Icc 1 1092).image (fun m => m * 1093) := by
    ext x
    simp only [mem_filter, mem_Icc, mem_image]
    constructor
    · rintro ⟨⟨h1, h2⟩, ⟨m, hm⟩⟩
      use m
      subst hm
      constructor
      · omega
      · rfl
    · rintro ⟨m, ⟨h1, h2⟩, rfl⟩
      exact ⟨by omega, ⟨m, rfl⟩⟩
  rw [H]
  apply sum_image
  intro x hx y hy hxy
  omega
