import FormalConjecturesUtil

/-! A coefficient obstruction for a restricted quintic polynomial construction. -/

namespace Erdos322Research

/-- The three indicated coefficients cannot all be nonpositive. This applies to
`u * ((x + b*u)^5 + (y - b*u)^5) + ∑ i, (c i + d i*u)^5`
when `x,y` are positive and the constants `c i` are nonnegative. -/
theorem quintic_coefficient_obstruction {ι : Type*} [Fintype ι]
    (x y b : ℝ) (c d : ι → ℝ) (hx : 0 < x) (hy : 0 < y) (hb : b ≠ 0)
    (hc : ∀ i, 0 ≤ c i)
    (h2 : 5 * b * (x ^ 4 - y ^ 4) + 10 * (∑ i, c i ^ 3 * d i ^ 2) ≤ 0)
    (h3 : 10 * b ^ 2 * (x ^ 3 + y ^ 3) + 10 * (∑ i, c i ^ 2 * d i ^ 3) ≤ 0)
    (h4 : 10 * b ^ 3 * (x ^ 2 - y ^ 2) + 5 * (∑ i, c i * d i ^ 4) ≤ 0) : False := by
  classical
  let S₂ : ℝ := ∑ i, c i ^ 3 * d i ^ 2
  let S₃ : ℝ := ∑ i, c i ^ 2 * d i ^ 3
  let S₄ : ℝ := ∑ i, c i * d i ^ 4
  have hS₂ : 0 ≤ S₂ := Finset.sum_nonneg (fun i _ ↦ mul_nonneg (pow_nonneg (hc i) _) (sq_nonneg _))
  have hS₄ : 0 ≤ S₄ := Finset.sum_nonneg (fun i _ ↦ mul_nonneg (hc i) (by positivity))
  have hCS : S₃ ^ 2 ≤ S₂ * S₄ := by
    exact Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul Finset.univ
      (fun i _ ↦ mul_nonneg (pow_nonneg (hc i) _) (sq_nonneg _))
      (fun i _ ↦ mul_nonneg (hc i) (by positivity))
      (fun i _ ↦ by ring)
  let X := -b * (x ^ 4 - y ^ 4)
  let Y := -2 * b ^ 3 * (x ^ 2 - y ^ 2)
  have h₂ : 2 * S₂ ≤ X := by dsimp [S₂, X]; linarith only [h2]
  have h₄ : S₄ ≤ Y := by dsimp [S₄, Y]; linarith only [h4]
  have hX : 0 ≤ X := le_trans (by positivity) h₂
  have hp := mul_le_mul h₂ h₄ hS₄ hX
  have hB : 0 ≤ b ^ 2 * (x ^ 3 + y ^ 3) := by positivity
  have h₃ : b ^ 2 * (x ^ 3 + y ^ 3) ≤ -S₃ := by
    dsimp [S₃]
    linarith only [h3]
  have hnS₃ : 0 ≤ -S₃ := hB.trans h₃
  have hsq : (b ^ 2 * (x ^ 3 + y ^ 3)) ^ 2 ≤ S₃ ^ 2 := by
    simpa only [neg_sq] using (sq_le_sq₀ hB hnS₃).mpr h₃
  have hb4 : 0 < b ^ 4 := by
    simpa only [← pow_mul] using pow_pos (sq_pos_of_ne_zero hb) 2
  have hd : 0 < b ^ 4 * x ^ 2 * y ^ 2 * (x + y) ^ 2 := by positivity
  dsimp [X, Y] at hp
  nlinarith only [hCS, hp, hsq, hd]

open Polynomial

private theorem affine_fifth_coeff (c d : ℝ) (j : ℕ) :
    ((C c + C d * X) ^ 5 : ℝ[X]).coeff j =
      c ^ (5 - j) * (5 : ℕ).choose j * d ^ j := by
  have he : (C c + C d * X) ^ 5 = ((X + C c) ^ 5).comp (C d * X) := by
    simp [add_comm]
  rw [he, comp_C_mul_X_coeff, coeff_X_add_C_pow]

private noncomputable def quinticModel {ι : Type*} [Fintype ι] (x y b : ℝ) (c d : ι → ℝ) : ℝ[X] :=
  X * ((C x + C b * X) ^ 5 + (C y + C (-b) * X) ^ 5) +
    ∑ i, (C (c i) + C (d i) * X) ^ 5

private theorem quinticModel_coeff_two {ι : Type*} [Fintype ι]
    (x y b : ℝ) (c d : ι → ℝ) :
    (quinticModel x y b c d).coeff 2 =
      5 * b * (x ^ 4 - y ^ 4) + 10 * (∑ i, c i ^ 3 * d i ^ 2) := by
  simp only [quinticModel, coeff_add, show 2 = 1 + 1 by rfl, coeff_X_mul,
    finset_sum_coeff, affine_fifth_coeff]
  norm_num [Nat.choose]
  rw [Finset.mul_sum]
  congr 1
  · ring
  · apply Finset.sum_congr rfl
    intro i _
    ring

private theorem quinticModel_coeff_three {ι : Type*} [Fintype ι]
    (x y b : ℝ) (c d : ι → ℝ) :
    (quinticModel x y b c d).coeff 3 =
      10 * b ^ 2 * (x ^ 3 + y ^ 3) + 10 * (∑ i, c i ^ 2 * d i ^ 3) := by
  simp only [quinticModel, coeff_add, show 3 = 2 + 1 by rfl, coeff_X_mul,
    finset_sum_coeff, affine_fifth_coeff]
  norm_num [Nat.choose]
  rw [Finset.mul_sum]
  congr 1
  · ring
  · apply Finset.sum_congr rfl
    intro i _
    ring

private theorem quinticModel_coeff_four {ι : Type*} [Fintype ι]
    (x y b : ℝ) (c d : ι → ℝ) :
    (quinticModel x y b c d).coeff 4 =
      10 * b ^ 3 * (x ^ 2 - y ^ 2) + 5 * (∑ i, c i * d i ^ 4) := by
  simp only [quinticModel, coeff_add, show 4 = 3 + 1 by rfl, coeff_X_mul,
    finset_sum_coeff, affine_fifth_coeff]
  norm_num [Nat.choose]
  rw [Finset.mul_sum]
  congr 1
  · ring
  · apply Finset.sum_congr rfl
    intro i _
    ring

/-- A nonnegative-coefficient remainder cannot make this restricted quintic
polynomial construction constant. -/
theorem quintic_model_not_constant {ι : Type*} [Fintype ι]
    (x y b : ℝ) (c d : ι → ℝ) (R : ℝ[X]) (N : ℝ)
    (hx : 0 < x) (hy : 0 < y) (hb : b ≠ 0) (hc : ∀ i, 0 ≤ c i)
    (hR2 : 0 ≤ R.coeff 2) (hR3 : 0 ≤ R.coeff 3) (hR4 : 0 ≤ R.coeff 4) :
    X * ((C x + C b * X) ^ 5 + (C y + C (-b) * X) ^ 5) +
      (∑ i, (C (c i) + C (d i) * X) ^ 5) + R ≠ C N := by
  intro h
  change quinticModel x y b c d + R = C N at h
  have h2 := congrArg (fun p : ℝ[X] ↦ p.coeff 2) h
  have h3 := congrArg (fun p : ℝ[X] ↦ p.coeff 3) h
  have h4 := congrArg (fun p : ℝ[X] ↦ p.coeff 4) h
  simp only [coeff_add, quinticModel_coeff_two, coeff_C, OfNat.ofNat_ne_zero, ite_false] at h2
  simp only [coeff_add, quinticModel_coeff_three, coeff_C, OfNat.ofNat_ne_zero, ite_false] at h3
  simp only [coeff_add, quinticModel_coeff_four, coeff_C, OfNat.ofNat_ne_zero, ite_false] at h4
  exact quintic_coefficient_obstruction x y b c d hx hy hb hc
    (by linarith only [h2, hR2]) (by linarith only [h3, hR3]) (by linarith only [h4, hR4])

private theorem scale_affine_fifth (w x b : ℝ) :
    ((C (w * x) + C (w * b) * X) ^ 5 : ℝ[X]) =
      C (w ^ 5) * (C x + C b * X) ^ 5 := by
  simp only [map_mul, map_pow]
  ring

set_option maxHeartbeats 2000000 in
/-- The obstruction persists after translation to any positive parameter value.
The final monomial may have arbitrary nonnegative degree. -/
theorem quintic_model_no_positive_point
    (a A b c d e f g u N : ℝ) (r : ℕ)
    (hu : 0 < u) (hg : 0 ≤ g) (hb : b ≠ 0)
    (ha : 0 < a + b * u) (hA : 0 < A - b * u)
    (hc : 0 ≤ c + d * u) (he : 0 ≤ e + f * u) :
    (X * ((C a + C b * X) ^ 5 + (C A + C (-b) * X) ^ 5) +
      (C c + C d * X) ^ 5 + (C e + C f * X) ^ 5 + C g * X ^ r : ℝ[X]) ≠ C N := by
  intro h
  let w : ℝ := u ^ (1 / 5 : ℝ)
  have hw : 0 < w := by dsimp [w]; positivity
  have hw5 : w ^ 5 = u := by
    dsimp [w]
    rw [← Real.rpow_mul_natCast hu.le]
    norm_num
  let cs : Fin 4 → ℝ := ![c + d * u, e + f * u, w * (a + b * u), w * (A - b * u)]
  let ds : Fin 4 → ℝ := ![d, f, w * b, w * (-b)]
  let R : ℝ[X] := C g * (X + C u) ^ r
  have hcs : ∀ i, 0 ≤ cs i := by
    intro i
    fin_cases i <;> dsimp [cs]
    · exact hc
    · exact he
    · exact mul_nonneg hw.le ha.le
    · exact mul_nonneg hw.le hA.le
  have hR (j : ℕ) : 0 ≤ R.coeff j := by
    dsimp [R]
    rw [coeff_C_mul, coeff_X_add_C_pow]
    positivity
  apply quintic_model_not_constant (a + b * u) (A - b * u) b cs ds R N
    ha hA hb hcs (hR 2) (hR 3) (hR 4)
  have hh := congrArg (fun p : ℝ[X] ↦ p.comp (X + C u)) h
  simp only [add_comp, mul_comp, pow_comp, C_comp, X_comp] at hh
  calc
    _ = (X + C u) * ((C a + C b * (X + C u)) ^ 5 +
        (C A + C (-b) * (X + C u)) ^ 5) +
        (C c + C d * (X + C u)) ^ 5 +
        (C e + C f * (X + C u)) ^ 5 + C g * (X + C u) ^ r := by
      rw [Fin.sum_univ_four]
      dsimp only [cs, ds, R]
      change _ + ((C (c + d * u) + C d * X) ^ 5 +
        (C (e + f * u) + C f * X) ^ 5 +
        (C (w * (a + b * u)) + C (w * b) * X) ^ 5 +
        (C (w * (A - b * u)) + C (w * (-b)) * X) ^ 5) + _ = _
      rw [scale_affine_fifth, scale_affine_fifth, hw5]
      have haff (p q : ℝ) : (C (p + q * u) + C q * X : ℝ[X]) =
          C p + C q * (X + C u) := by
        simp only [map_add, map_mul]
        ring
      have hsub : A - b * u = A + (-b) * u := by ring
      rw [hsub, haff, haff, haff, haff]
      ring
    _ = C N := hh

end Erdos322Research

#print axioms Erdos322Research.quintic_coefficient_obstruction

#print axioms Erdos322Research.quintic_model_not_constant

#print axioms Erdos322Research.quintic_model_no_positive_point
