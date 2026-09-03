import Submission.QuarticOddPowerFailure
import Submission.LargeCountPolynomialDensity

/-! Finitely many rational formulas do not circumvent the odd-power transfer
obstruction by selecting a different formula at each source tuple. No bound
on the full exact representation count is claimed. -/
namespace Erdos322Research.QuarticFinitePowerFormulas
noncomputable section
open Finset MvPolynomial QuarticOddPowerFailure LargeCountPolynomialDensity
open scoped Classical
set_option Elab.async false

/-- A high-count tuple can simultaneously avoid finitely many prescribed
nonzero polynomial zero sets. -/
theorem exists_large_count_off_finite_family {ι : Type*} [Fintype ι]
    (k M : ℕ) (P : ι → MvPolynomial (Fin (k+2)) ℚ) (hP : ∀ j, P j ≠ 0) :
    ∃ a : Fin (k+2) → ℕ,
      M < Erdos322.representationCount (k+2) (∑ i, a i^(k+2)) ∧
      ∀ j, eval (fun i ↦ (a i : ℚ)) (P j) ≠ 0 := by
  have hp : (∏ j, P j) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun j _ ↦ hP j)
  obtain ⟨a,ha,hprod⟩ := exists_large_count_off_polynomial k M (∏ j, P j) hp
  refine ⟨a,ha,?_⟩
  intro j
  rw [map_prod] at hprod
  exact Finset.prod_ne_zero_iff.mp hprod j (mem_univ j)

/-- Given any finite menu of rational formulas with positive multipliers and
exponents congruent to three modulo four, a high-count input exists at which
ALL denominators are nonzero and EVERY formula gives the wrong norm.
The chosen multiplier and exponent may differ between menu entries. -/
theorem finite_rational_power_menu_fails {ι : Type*} [Fintype ι]
    (M : ℕ) (c : ι → ℚ) (hc : ∀ j, 0 < c j) (m : ι → ℕ)
    (P : ι → Fin 4 → MvPolynomial (Fin 4) ℚ)
    (D : ι → MvPolynomial (Fin 4) ℚ) (hD : ∀ j, D j ≠ 0) :
    ∃ a : Fin 4 → ℕ,
      M < Erdos322.representationCount 4 (∑ i, a i^4) ∧
      ∀ j,
        eval (fun i ↦ (a i : ℚ)) (D j) ≠ 0 ∧
        (∑ i, (eval (fun l ↦ (a l : ℚ)) (P j i) /
          eval (fun l ↦ (a l : ℚ)) (D j))^4) ≠
            c j * ((∑ i, a i^4 : ℕ) : ℚ)^(4*m j+3) := by
  let E (j : ι) : MvPolynomial (Fin 4) ℚ :=
    (∑ i, P j i^4) - D j^4 *
      (C (c j) * (∑ i : Fin 4, X i^4)^(4*m j+3))
  have hE (j : ι) : E j ≠ 0 := by
    intro hz
    exact no_rational_power_formula (c j) (hc j) (m j) (P j) (D j) (hD j)
      (sub_eq_zero.mp hz)
  obtain ⟨a,ha,havoid⟩ := exists_large_count_off_finite_family 2 M
    (fun j ↦ D j * E j) (fun j ↦ mul_ne_zero (hD j) (hE j))
  refine ⟨a,ha,?_⟩
  intro j
  have hboth := havoid j
  rw [map_mul] at hboth
  have hd := (mul_ne_zero_iff.mp hboth).1
  have he := (mul_ne_zero_iff.mp hboth).2
  refine ⟨hd,?_⟩
  intro hnorm
  simp only [div_pow,← Finset.sum_div] at hnorm
  have hnorm' := (div_eq_iff (pow_ne_zero 4 hd)).mp hnorm
  apply he
  simp only [E,map_sub,map_sum,map_pow,map_mul,eval_C,eval_X]
  rw [hnorm']
  simp only [Nat.cast_sum,Nat.cast_pow]
  ring

end
end Erdos322Research.QuarticFinitePowerFormulas
