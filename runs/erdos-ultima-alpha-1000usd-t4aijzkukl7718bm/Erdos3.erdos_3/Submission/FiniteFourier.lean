import Submission.DissociatedRiesz

/-! Normalized Fourier identities on finite abelian groups, for spectral almost-periods. -/
namespace Erdos3FiniteFourier
open Finset Erdos3DissociatedRiesz
open scoped BigOperators Classical ComplexConjugate
set_option maxHeartbeats 2000000

variable {G : Type*} [AddCommGroup G] [Fintype G]

noncomputable def hat (f : G → ℂ) (χ : AddChar G ℂ) : ℂ := 𝔼 x : G, f x*conj (χ x)
noncomputable def meanChar (T : Finset G) (χ : AddChar G ℂ) : ℂ := 𝔼 t : T, χ t
noncomputable def cdiffSmooth (T : Finset G) (f : G → ℂ) (x : G) : ℂ :=
  𝔼 b : T, 𝔼 c : T, f (x+(c : G)-(b : G))
noncomputable def walkSmooth (T : Finset G) : ℕ → (G → ℂ) → G → ℂ
  | 0, f => f
  | n+1, f => cdiffSmooth T (walkSmooth T n f)

lemma expect_conj {V : Type*} [Fintype V] (f : V → ℂ) :
    conj (𝔼 x, f x) = 𝔼 x, conj (f x) := by
  exact map_expect ((Complex.conjCLE : ℂ ≃L[ℝ] ℂ).toLinearEquiv.toLinearMap.restrictScalars ℚ≥0) f univ

lemma char_sub (χ : AddChar G ℂ) (x y : G) : χ (x-y) = χ x*conj (χ y) := by
  rw [χ.map_sub_eq_div, div_eq_mul_inv, AddChar.inv_apply_eq_conj]

lemma sum_char_mul_conj (x y : G) :
    (∑ χ : AddChar G ℂ, χ x*conj (χ y)) = if x = y then (Fintype.card G : ℂ) else 0 := by
  simp_rw [← char_sub, AddChar.sum_apply_eq_ite, sub_eq_zero]

/-- Fourier inversion, with normalized coefficients and an unnormalized dual sum. -/
theorem inversion (f : G → ℂ) (x : G) : f x = ∑ χ : AddChar G ℂ, hat f χ*χ x := by
  symm
  unfold hat
  simp_rw [expect_mul]
  rw [← expect_sum_comm]
  have ht (y : G) : (∑ χ : AddChar G ℂ, f y*conj (χ y)*χ x) =
      f y*(if x = y then (Fintype.card G : ℂ) else 0) := by
    rw [← sum_char_mul_conj]
    rw [mul_sum]
    apply sum_congr rfl
    intro χ _
    ring
  simp_rw [ht]
  rw [Fintype.expect_eq_sum_div_card]
  simp [mul_ite, Fintype.card_ne_zero]

lemma parseval (f : G → ℂ) :
    (∑ χ : AddChar G ℂ, ‖hat f χ‖^2) = 𝔼 x : G, ‖f x‖^2 := by
  calc
    _ = 𝔼 x : G, ‖∑ χ : AddChar G ℂ, hat f χ*χ x‖^2 :=
      (expect_norm_sq_sum_chars univ id (hat f) (Function.injective_id.injOn)).symm
    _ = _ := by simp_rw [← inversion]

lemma hat_shift (f : G → ℂ) (t : G) (χ : AddChar G ℂ) :
    hat (fun x ↦ f (x+t)) χ = χ t*hat f χ := by
  calc
    _ = 𝔼 x : G, f x*conj (χ (x-t)) :=
      Fintype.expect_equiv (Equiv.addRight t) _ _ (fun x ↦ by simp)
    _ = _ := by
      unfold hat
      rw [mul_expect]
      apply expect_congr rfl
      intro x _
      rw [char_sub, map_mul, starRingEnd_self_apply]
      ring

lemma hat_cdiffSmooth (T : Finset G) (f : G → ℂ) (χ : AddChar G ℂ) :
    hat (cdiffSmooth T f) χ = (‖meanChar T χ‖^2 : ℝ)*hat f χ := by
  unfold hat cdiffSmooth
  simp_rw [expect_mul]
  calc
    _ = 𝔼 b : T, 𝔼 c : T, 𝔼 x : G,
        f (x+(c : G)-(b : G))*conj (χ x) := by
      rw [expect_comm]
      apply expect_congr rfl
      intro b _
      exact expect_comm _ _ _
    _ = 𝔼 b : T, 𝔼 c : T, χ ((c : G)-(b : G))*hat f χ := by
      apply expect_congr rfl
      intro b _
      apply expect_congr rfl
      intro c _
      simpa only [add_sub_assoc] using hat_shift f ((c : G)-(b : G)) χ
    _ = _ := by
      simp_rw [char_sub, ← expect_mul]
      rw [← mul_expect, ← expect_conj]
      simp only [meanChar, hat, Complex.mul_conj, Complex.normSq_eq_norm_sq]

lemma hat_walkSmooth (T : Finset G) (f : G → ℂ) (n : ℕ) (χ : AddChar G ℂ) :
    hat (walkSmooth T n f) χ = (‖meanChar T χ‖^(2*n) : ℝ)*hat f χ := by
  induction n with
  | zero => simp [walkSmooth]
  | succ n ih =>
    rw [walkSmooth, hat_cdiffSmooth, ih]
    push_cast
    rw [← mul_assoc, ← pow_add]
    congr 2
    omega

lemma norm_hat_le (f : G → ℂ) (χ : AddChar G ℂ) :
    ‖hat f χ‖ ≤ 𝔼 x : G, ‖f x‖ := by
  calc
    _ ≤ 𝔼 x : G, ‖f x*conj (χ x)‖ := RCLike.norm_expect_le (K := ℂ)
    _ = _ := by simp only [norm_mul, Complex.norm_conj, χ.norm_apply, mul_one]

lemma norm_meanChar_le_one (T : Finset G) (χ : AddChar G ℂ) : ‖meanChar T χ‖ ≤ 1 := by
  by_cases hT : T.Nonempty
  · letI : Nonempty T := hT.to_subtype
    calc
      _ ≤ 𝔼 t : T, ‖χ t‖ := RCLike.norm_expect_le (K := ℂ)
      _ = _ := by simp only [χ.norm_apply, Fintype.expect_const]
  · have hz : T = ∅ := not_nonempty_iff_eq_empty.mp hT
    subst T
    simp [meanChar, Fintype.expect_eq_sum_div_card]

lemma norm_char_sub_one_le_two (χ : AddChar G ℂ) (x : G) : ‖χ x-1‖ ≤ 2 := by
  calc
    _ ≤ ‖χ x‖+‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = _ := by rw [χ.norm_apply, norm_one]; norm_num

#print axioms inversion
#print axioms parseval
#print axioms hat_walkSmooth
end Erdos3FiniteFourier
