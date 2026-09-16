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
      have : x = m * 1093 := by rw [hm, mul_comm]
      constructor
      · constructor
        · have : 0 < m := by
            by_contra h_not
            have : m = 0 := by omega
            subst this
            omega
          omega
        · have : m * 1093 ≤ 1092 * 1093 := by omega
          exact Nat.le_of_mul_le_mul_right this (by decide)
      · exact this
    · rintro ⟨m, ⟨h1, h2⟩, rfl⟩
      constructor
      · constructor
        · omega
        · have : m * 1093 ≤ 1092 * 1093 := Nat.mul_le_mul_right 1093 h2
          omega
      · use m
        ring
  rw [H]
  apply sum_image
  intro x hx y hy hxy
  have : x * 1093 = y * 1093 := hxy
  exact Nat.eq_of_mul_eq_mul_right (by decide) this
