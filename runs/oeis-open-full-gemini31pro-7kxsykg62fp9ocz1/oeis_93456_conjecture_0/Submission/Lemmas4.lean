import FormalConjectures.Util.ProblemImports
import Submission.Lemmas3
open Nat Finset

lemma sum_padicValNat_I2 (p M : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (hM : p ∣ M - 1) (hM_ge : 1 ≤ M) :
  ∑ k ∈ Icc 1 (p * (p - 2)), padicValNat p (p * M + k) = p - 2 := by
  have H : ∑ k ∈ Icc 1 (p * (p - 2)), padicValNat p (p * M + k) =
           ∑ k ∈ Icc 1 (p * (p - 2)), if p ∣ k then 1 else 0 := by
    apply sum_congr rfl
    intro k hk
    rw [mem_Icc] at hk
    exact padicValNat_pM_add_k p M k hp hk.1 hk.2 hM hM_ge
  rw [H]
  -- sum of (if p | k then 1 else 0) is the number of multiples of p
  have H2 : ∑ k ∈ Icc 1 (p * (p - 2)), if p ∣ k then 1 else 0 =
            ( (Icc 1 (p * (p - 2))).filter (fun k => p ∣ k) ).card := by
    rw [sum_ite]
    simp
  rw [H2]
  have H3 : ((Icc 1 (p * (p - 2))).filter (fun k => p ∣ k)).card = p - 2 := by
    -- we can use image
    have : ((Icc 1 (p - 2)).image (fun x => p * x)) = (Icc 1 (p * (p - 2))).filter (fun k => p ∣ k) := by
      ext x
      simp only [mem_image, mem_filter, mem_Icc]
      constructor
      · rintro ⟨y, ⟨hy1, hy2⟩, rfl⟩
        refine ⟨⟨?_, ?_⟩, dvd_mul_right p y⟩
        · have : 1 ≤ p := by omega
          nlinarith
        · exact Nat.mul_le_mul_left p hy2
      · rintro ⟨⟨hx1, hx2⟩, hdvd⟩
        obtain ⟨y, rfl⟩ := hdvd
        refine ⟨y, ⟨?_, ?_⟩, rfl⟩
        · rcases y with _ | y
          · omega
          · omega
        · exact Nat.le_of_mul_le_mul_left hx2 (by omega)
    rw [← this, card_image_of_injOn]
    · rw [Nat.card_Icc]; omega
    · intro a _ b _ hab
      exact Nat.eq_of_mul_eq_mul_left (by omega) hab
  rw [H3]
