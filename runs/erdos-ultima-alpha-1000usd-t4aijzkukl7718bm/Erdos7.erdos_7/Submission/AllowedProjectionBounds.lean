import Submission.ArithmeticProjectionLower

/-! Two-sided bounds for arbitrary allowed cylinders, not only projections of
present classes. These are auxiliary geometric facts, not a settlement. -/
namespace Erdos7AllowedProjectionBounds
open scoped BigOperators
open Erdos7PureProjectionLower Erdos7ArithmeticProjectionLower
set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- Each allowed cylinder has conditional mass between its original mass and
 twice that mass after removal of a disjoint, complete odd pure-power family. -/
theorem allowed_cylinder_bounds (p E v : ℕ) [NeZero p] (hp : 3 ≤ p)
    (a : ℕ → ℤ) (r : ℤ) (hvE : v ≤ E)
    (hdis : ∀ i j, 1 ≤ i → i ≤ E → 1 ≤ j → j ≤ E → i ≠ j →
      Disjoint (cylinder p E i (a i)) (cylinder p E j (a j)))
    (hsep : ∀ j, 1 ≤ j → j ≤ v → ¬ ((p^j:ℕ):ℤ) ∣ r-a j) :
    let U := Finset.univ \ pureUnion (fun j => cylinder p E j (a j)) E
    1/2 ≤ mass (uniform p E) U ∧
      ((p:ℝ)⁻¹)^v ≤ mass (uniform p E) (cylinder p E v r ∩ U) /
        mass (uniform p E) U ∧
      mass (uniform p E) (cylinder p E v r ∩ U) / mass (uniform p E) U ≤
        2*((p:ℝ)⁻¹)^v := by
  dsimp only
  let B := fun j => cylinder p E j (a j)
  let U := Finset.univ \ pureUnion B E
  have hB : ∀ j, 1 ≤ j → j ≤ E → mass (uniform p E) (B j) = ((p:ℝ)⁻¹)^j := by
    intro j _ hj
    exact cylinder_mass p E j _ hj
  have hhalf : 1/2 ≤ mass (uniform p E) U := by
    rw [pure_complement_mass _ (uniform_mass p E) B E _ hB hdis]
    have hh := geom_le_half ((p:ℝ)⁻¹) (by positivity) (inv_le_third p hp) E
    linarith
  have hpos : 0 < mass (uniform p E) U := by linarith
  refine ⟨hhalf,?_,?_⟩
  · apply conditional_cylinder_lower_bound (uniform p E) (uniform_nonneg p E)
      (uniform_mass p E) B E v hvE ((p:ℝ)⁻¹) (by positivity) hB hdis
      (cylinder p E v r) (cylinder_mass p E v r hvE) _ hpos
    intro j hj hjv
    exact (cylinder_disjoint p E j v (a j) r hjv (hsep j hj hjv)).symm
  · apply (div_le_iff₀ hpos).mpr
    have hsub := mass_mono (uniform p E) (uniform_nonneg p E)
      (Finset.inter_subset_left (s₁ := cylinder p E v r) (s₂ := U))
    rw [cylinder_mass p E v r hvE] at hsub
    have hmul := mul_le_mul_of_nonneg_left hhalf (pow_nonneg (by positivity : 0 ≤ (p:ℝ)⁻¹) v)
    nlinarith

/-- Five surviving mod9 cells have the claimed bounds, as soon as the cell's
residue avoids the pure3 and pure9 classes. All higher exponents are allowed. -/
theorem ternary_cell_bounds (E : ℕ) (hE : 2 ≤ E) (a : ℕ → ℤ) (r : ℤ)
    (hdis : ∀ i j, 1 ≤ i → i ≤ E → 1 ≤ j → j ≤ E → i ≠ j →
      Disjoint (cylinder 3 E i (a i)) (cylinder 3 E j (a j)))
    (h₁ : ¬ (3:ℤ) ∣ r-a 1) (h₂ : ¬ (9:ℤ) ∣ r-a 2) :
    let U := Finset.univ \ pureUnion (fun j => cylinder 3 E j (a j)) E
    1/9 ≤ mass (uniform 3 E) (cylinder 3 E 2 r ∩ U) / mass (uniform 3 E) U ∧
      mass (uniform 3 E) (cylinder 3 E 2 r ∩ U) / mass (uniform 3 E) U ≤ 2/9 := by
  have hh := allowed_cylinder_bounds 3 E 2 (by decide) a r hE hdis (by
    intro j hj hj2
    have : j = 1 ∨ j = 2 := by omega
    rcases this with rfl | rfl
    · simpa only [pow_one,Nat.cast_ofNat] using h₁
    · norm_num only [Nat.reducePow,Nat.cast_ofNat]
      exact h₂)
  norm_num only [Nat.cast_ofNat,inv_pow,one_div,show ((3:ℝ)⁻¹)^2 = 1/9 by norm_num,
    show 2*(1/9:ℝ) = 2/9 by norm_num] at hh
  exact hh.2

#print axioms allowed_cylinder_bounds
#print axioms ternary_cell_bounds
end Erdos7AllowedProjectionBounds
