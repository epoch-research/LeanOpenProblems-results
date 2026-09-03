import FormalConjecturesUtil

/-! Homogeneous boundary clearing by pigeonhole. The produced weight vector
is nonzero, but its integer coefficient pair or its real value may be zero. -/
namespace BoundaryPigeonhole

open Finset

/-- A modular relation with bounded, not-all-zero integer weights. -/
theorem bounded_modular_relation (D C Q : ℕ) (hC : 0 < C)
    (hcard : C < (Q + 1) ^ D) (b : Fin D → ℤ) :
    ∃ w : Fin D → ℤ, w ≠ 0 ∧ (∀ i, |w i| ≤ Q) ∧ (C : ℤ) ∣ ∑ i, w i * b i := by
  classical
  letI : NeZero C := ⟨hC.ne'⟩
  let f : (Fin D → Fin (Q + 1)) → ZMod C := fun u =>
    ∑ i, (u i : ZMod C) * (b i : ZMod C)
  have hc : Fintype.card (ZMod C) < Fintype.card (Fin D → Fin (Q + 1)) := by
    simpa using hcard
  obtain ⟨u, v, huv, he⟩ := Fintype.exists_ne_map_eq_of_card_lt f hc
  let w : Fin D → ℤ := fun i => (u i : ℤ) - (v i : ℤ)
  refine ⟨w, ?_, ?_, ?_⟩
  · intro hw
    apply huv
    funext i
    apply Fin.ext
    have hi := congrFun hw i
    simp only [w, Pi.zero_apply, sub_eq_zero] at hi
    exact_mod_cast hi
  · intro i
    apply abs_le.mpr
    have hu := (u i).isLt
    have hv := (v i).isLt
    dsimp [w]
    constructor <;> omega
  · apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    push_cast
    simp only [w, Int.cast_sub, Int.cast_natCast, sub_mul, sum_sub_distrib]
    exact sub_eq_zero.mpr he

lemma weighted_error_bound (D Q : ℕ) (x η : ℝ)
    (A : ℤ) (B : Fin D → ℝ) (w : Fin D → ℤ)
    (hw : ∀ i, |w i| ≤ Q) (he : ∀ i, |(A : ℝ) * x - B i| ≤ η) :
    |(A * ∑ i, w i : ℤ) * x - ∑ i, (w i : ℝ) * B i| ≤ D * Q * η := by
  have hid : ((A * ∑ i, w i : ℤ) : ℝ) * x - ∑ i, (w i : ℝ) * B i =
      ∑ i, (w i : ℝ) * ((A : ℝ) * x - B i) := by
    simp only [Int.cast_mul, Int.cast_sum, mul_sub, sum_sub_distrib,
      ← sum_mul]
    ring
  rw [hid]
  calc
    _ ≤ ∑ i, |(w i : ℝ) * ((A : ℝ) * x - B i)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin D, (Q : ℝ) * η := by
      apply sum_le_sum
      intro i _
      rw [abs_mul]
      have hwi : |(w i : ℝ)| ≤ Q := by exact_mod_cast hw i
      exact mul_le_mul hwi (he i) (abs_nonneg _) (by positivity)
    _ = _ := by simp; ring

lemma integral_boundary_of_modular_relation (D C : ℕ) (hC : 0 < C)
    (B : Fin D → ℝ) (b w : Fin D → ℤ)
    (hb : ∀ i, (C : ℝ) * B i = b i)
    (hw : (C : ℤ) ∣ ∑ i, w i * b i) :
    ∃ z : ℤ, (∑ i, (w i : ℝ) * B i) = z := by
  obtain ⟨z, hz⟩ := hw
  refine ⟨z, ?_⟩
  apply (mul_left_cancel₀ (by positivity : (C : ℝ) ≠ 0))
  calc
    _ = ∑ i, (w i : ℝ) * ((C : ℝ) * B i) := by rw [mul_sum]; apply sum_congr rfl; intros; ring
    _ = ∑ i, (w i : ℝ) * (b i : ℝ) := by simp only [hb]
    _ = (C : ℝ) * (z : ℝ) := by exact_mod_cast hz

/-- The conclusion guarantees a nonzero weight vector, NOT a nonzero pair
or a nonzero value. No such assertion follows from pigeonhole alone. -/
theorem small_integral_form (D C Q : ℕ) (hC : 0 < C)
    (hcard : C < (Q + 1) ^ D) (x η : ℝ)
    (A : ℤ) (B : Fin D → ℝ)
    (hB : ∀ i, ∃ z : ℤ, (C : ℝ) * B i = z)
    (he : ∀ i, |(A : ℝ) * x - B i| ≤ η) :
    ∃ w : Fin D → ℤ, w ≠ 0 ∧ (∀ i, |w i| ≤ Q) ∧
      ∃ b : ℤ, (∑ i, (w i : ℝ) * B i) = b ∧
        |(A * ∑ i, w i : ℤ) * x - b| ≤ D * Q * η := by
  classical
  choose b hb using hB
  obtain ⟨w, hw, hsize, hmod⟩ := bounded_modular_relation D C Q hC hcard b
  obtain ⟨z, hz⟩ := integral_boundary_of_modular_relation D C hC B b w hb hmod
  refine ⟨w, hw, hsize, z, hz, ?_⟩
  rw [← hz]
  exact weighted_error_bound D Q x η A B w hsize he

end BoundaryPigeonhole

#print axioms BoundaryPigeonhole.bounded_modular_relation

#print axioms BoundaryPigeonhole.small_integral_form
