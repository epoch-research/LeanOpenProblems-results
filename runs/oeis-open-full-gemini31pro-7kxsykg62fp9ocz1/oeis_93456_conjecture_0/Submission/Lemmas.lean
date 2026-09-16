import FormalConjectures.Util.ProblemImports
open Nat Finset

lemma sum_padicValNat_I2 (p M : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (hM : p ∣ M - 1) (hM_ge : 1 ≤ M) :
  ((Icc 1 (p * (p - 2))).filter (fun k => p ∣ k)).card = p - 2 := by
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
  rw [← this]
  have H : ((Icc 1 (p - 2)).image (fun x => p * x)).card = (Icc 1 (p - 2)).card := by
    apply Finset.card_image_of_injective
    intro a b hab
    exact Nat.eq_of_mul_eq_mul_left (by omega) hab
  rw [H, Nat.card_Icc]
  omega
