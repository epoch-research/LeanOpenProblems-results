import Submission.KloostermanCollisionEnergy

/-!
# Elementary fourth-moment bound for Kloosterman sums

The argument uses additive orthogonality, the collision energy of the inverse
graph, and multiplicative rescaling. It is not the Weil bound.
-/
open Finset
open scoped Classical BigOperators ComplexConjugate
namespace Erdos821.Kloosterman

variable {F : Type*} [Field F] [Fintype F]

noncomputable def kloosterman (ψ : AddChar F ℂ) (a b : F) : ℂ :=
  ∑ u : Fˣ, ψ (a*(u : F) + b*(u : F)⁻¹)

lemma kloosterman_sq (ψ : AddChar F ℂ) (a b : F) :
    kloosterman ψ a b ^ 2 =
      ∑ u : UnitPair F, ψ (a*pairSum u + b*pairInvSum u) := by
  rw [pow_two, kloosterman, Fintype.sum_prod_type]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  apply sum_congr rfl
  intro x _
  apply sum_congr rfl
  intro y _
  rw [← AddChar.map_add_eq_mul]
  congr 1
  dsimp [pairSum, pairInvSum]
  ring

lemma conj_char (ψ : AddChar F ℂ) (x : F) : conj (ψ x) = ψ (-x) := by
  rw [AddChar.map_neg_eq_inv]
  exact (Complex.inv_eq_conj (ψ.norm_apply x)).symm

lemma kloosterman_norm_fourth_expansion (ψ : AddChar F ℂ) (a b : F) :
    ((‖kloosterman ψ a b‖ ^ 4 : ℝ) : ℂ) =
      ∑ u : UnitPair F, ∑ v : UnitPair F,
        ψ (a*(pairSum u-pairSum v) + b*(pairInvSum u-pairInvSum v)) := by
  calc
    _ = kloosterman ψ a b ^ 2 * conj (kloosterman ψ a b ^ 2) := by
      rw [Complex.mul_conj', norm_pow]
      push_cast
      ring
    _ = _ := by
      rw [kloosterman_sq, map_sum]
      simp_rw [Finset.sum_mul, Finset.mul_sum]
      apply sum_congr rfl
      intro u _
      apply sum_congr rfl
      intro v _
      rw [conj_char, ← AddChar.map_add_eq_mul]
      congr 1
      ring

lemma sum_char_two_frequencies (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (s t : F) :
    (∑ a : F, ∑ b : F, ψ (a*s+b*t)) =
      if s=0 ∧ t=0 then (Fintype.card F : ℂ)^2 else 0 := by
  simp_rw [AddChar.map_add_eq_mul]
  rw [← Finset.sum_mul_sum]
  rw [AddChar.sum_mulShift s hψ, AddChar.sum_mulShift t hψ]
  split_ifs <;> simp_all [pow_two]

/-- The double-frequency fourth moment is exactly field-cardinality squared
 times the ordered collision energy. -/
theorem kloosterman_fourth_moment (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) :
    (∑ a : F, ∑ b : F, ‖kloosterman ψ a b‖ ^ 4) =
      (Fintype.card F : ℝ)^2 * collisionEnergy (F := F) := by
  apply Complex.ofReal_injective
  simp only [Complex.ofReal_sum]
  simp_rw [kloosterman_norm_fourth_expansion]
  calc
    _ = ∑ u : UnitPair F, ∑ v : UnitPair F,
        ∑ a : F, ∑ b : F,
          ψ (a*(pairSum u-pairSum v)+b*(pairInvSum u-pairInvSum v)) := by
      conv_lhs =>
        enter [2, a]
        rw [sum_comm]
      rw [sum_comm]
      apply sum_congr rfl
      intro u _
      conv_lhs =>
        enter [2, a]
        rw [sum_comm]
      rw [sum_comm]
    _ = ∑ u : UnitPair F, ∑ v : UnitPair F,
        if Collides u v then (Fintype.card F : ℂ)^2 else 0 := by
      simp_rw [sum_char_two_frequencies ψ hψ, sub_eq_zero, Collides]
      apply sum_congr rfl
      intro u _
      apply sum_congr rfl
      intro v _
      split_ifs <;> rfl
    _ = _ := by
      simp [collisionEnergy, collisionFiber, sum_ite, ← Finset.mul_sum,
        Nat.cast_sum, mul_comm]

lemma kloosterman_rescale (ψ : AddChar F ℂ) (a b : F) (c : Fˣ) :
    kloosterman ψ (a*(c : F)) (b/(c : F)) = kloosterman ψ a b := by
  unfold kloosterman
  apply Fintype.sum_equiv (Equiv.mulLeft c)
  intro u
  congr 1
  change a*(c : F)*(u : F) + b/(c : F)*(u : F)⁻¹ =
    a*((c*u : Fˣ) : F) + b*((c*u : Fˣ) : F)⁻¹
  simp only [Units.val_mul, mul_inv_rev, div_eq_mul_inv]
  ring

omit [Fintype F] in
lemma rescale_injective {a b : F} (ha : a ≠ 0) :
    Function.Injective (fun c : Fˣ => (a*(c : F), b/(c : F))) := by
  intro c d he
  apply Units.ext
  exact mul_left_cancel₀ ha (congrArg Prod.fst he)

lemma rescale_moment_le (ψ : AddChar F ℂ) (a b : F) (ha : a ≠ 0) :
    (Fintype.card Fˣ : ℝ) * ‖kloosterman ψ a b‖^4 ≤
      ∑ x : F, ∑ y : F, ‖kloosterman ψ x y‖^4 := by
  let orbit : Fˣ → F × F := fun c => (a*(c : F), b/(c : F))
  have hinj : Function.Injective orbit := rescale_injective ha
  calc
    _ = ∑ c : Fˣ, ‖kloosterman ψ (orbit c).1 (orbit c).2‖^4 := by
      simp [orbit, kloosterman_rescale]
    _ = ∑ v ∈ univ.image orbit, ‖kloosterman ψ v.1 v.2‖^4 :=
      (sum_image (s := univ) (f := fun v : F × F => ‖kloosterman ψ v.1 v.2‖^4)
        hinj.injOn).symm
    _ ≤ ∑ v : F × F, ‖kloosterman ψ v.1 v.2‖^4 :=
      sum_le_sum_of_subset_of_nonneg (subset_univ _) (by intros; positivity)
    _ = _ := Fintype.sum_prod_type _

/-- An elementary pointwise fourth-power bound, without a Weil estimate. -/
theorem kloosterman_norm_fourth_le_units (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive)
    (a b : F) (ha : a ≠ 0) :
    ‖kloosterman ψ a b‖^4 ≤
      3 * (Fintype.card F : ℝ)^2 * Fintype.card Fˣ := by
  have hU : 0 < (Fintype.card Fˣ : ℝ) := by exact_mod_cast Fintype.card_pos
  have hE : (collisionEnergy (F := F) : ℝ) ≤ 3*(Fintype.card Fˣ : ℝ)^2 := by
    exact_mod_cast (collisionEnergy_le (F := F))
  apply (mul_le_mul_iff_right₀ hU).mp
  calc
    _ ≤ ∑ x : F, ∑ y : F, ‖kloosterman ψ x y‖^4 := rescale_moment_le ψ a b ha
    _ = (Fintype.card F : ℝ)^2 * collisionEnergy (F := F) :=
      kloosterman_fourth_moment ψ hψ
    _ ≤ (Fintype.card F : ℝ)^2 * (3*(Fintype.card Fˣ : ℝ)^2) :=
      mul_le_mul_of_nonneg_left hE (sq_nonneg _)
    _ = _ := by ring

/-- The classical elementary three-quarter-power estimate, expressed without
fractional powers. The first frequency is assumed nonzero. -/
theorem kloosterman_norm_fourth_le (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive)
    (a b : F) (ha : a ≠ 0) :
    ‖kloosterman ψ a b‖^4 ≤ 3 * (Fintype.card F : ℝ)^3 := by
  have hU : (Fintype.card Fˣ : ℝ) ≤ Fintype.card F := by
    exact_mod_cast Fintype.card_le_of_injective (Units.val : Fˣ → F) Units.val_injective
  calc
    _ ≤ 3*(Fintype.card F : ℝ)^2 * Fintype.card Fˣ :=
      kloosterman_norm_fourth_le_units ψ hψ a b ha
    _ ≤ 3*(Fintype.card F : ℝ)^2 * Fintype.card F :=
      mul_le_mul_of_nonneg_left hU (by positivity)
    _ = _ := by ring

end Erdos821.Kloosterman
