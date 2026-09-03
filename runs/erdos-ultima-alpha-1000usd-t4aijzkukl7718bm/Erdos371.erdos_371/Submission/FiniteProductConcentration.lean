import Submission.FiniteInformation

/-! Finite Hoeffding bounds and information decoupling for independent coordinates.
No independence of arithmetic labels and residues is asserted. -/

namespace Erdos371.FiniteInformation
open Finset

variable {α : Type*} [Fintype α]

lemma mean_exp_mul_le_unit (q : Law α) (F : α → ℝ)
    (hb : ∀ a, |F a| ≤ 1) (hc : mean q F = 0) (t : ℝ) :
    mean q (fun a => Real.exp (t * F a)) ≤ Real.exp (t ^ 2 / 2) := by
  calc
    _ ≤ mean q (fun a => Real.cosh t + F a * Real.sinh t) := by
      apply sum_le_sum
      intro a _
      apply mul_le_mul_of_nonneg_left _ (q.nonneg a)
      simpa only [mul_comm t] using Real.exp_mul_le_cosh_add_mul_sinh (hb a) t
    _ = Real.cosh t := by
      rw [mean_add, mean_const]
      have hm : mean q (fun a => F a * Real.sinh t) = Real.sinh t * mean q F := by
        simpa only [mul_comm (Real.sinh t)] using mean_smul q (Real.sinh t) F
      rw [hm, hc, mul_zero, add_zero]
    _ ≤ _ := Real.cosh_le_exp_half_sq t

lemma mean_exp_mul_le_bounded (q : Law α) (F : α → ℝ) {B : ℝ}
    (hB : 0 ≤ B) (hb : ∀ a, |F a| ≤ B) (hc : mean q F = 0) (t : ℝ) :
    mean q (fun a => Real.exp (t * F a)) ≤ Real.exp (B ^ 2 * t ^ 2 / 2) := by
  rcases hB.eq_or_lt with hB | hB
  · have hz (a : α) : F a = 0 := abs_nonpos_iff.mp (hB ▸ hb a)
    simp only [hz, mul_zero, Real.exp_zero, mean_const, ← hB, zero_pow (by decide : 2 ≠ 0),
      zero_mul, zero_div, le_refl]
  · have hunit : ∀ a, |F a / B| ≤ 1 := by
      intro a
      rw [abs_div, abs_of_pos hB, div_le_one hB]
      exact hb a
    have hcenter : mean q (fun a => F a / B) = 0 := by
      simp only [mean] at hc ⊢
      simp only [← mul_div_assoc, ← sum_div, hc, zero_div]
    have hh := mean_exp_mul_le_unit q (fun a => F a / B) hunit hcenter (t * B)
    have he (a : α) : t * B * (F a / B) = t * F a := by field_simp
    simp only [he] at hh
    convert hh using 1
    congr 1
    ring

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {β : ι → Type*} [∀ i, Fintype (β i)]

/-- Product law on a finite family of finite coordinate spaces. -/
noncomputable def productLaw (q : ∀ i, Law (β i)) : Law (∀ i, β i) := by
  classical
  exact {
    mass := fun y => ∏ i, q i (y i)
    nonneg := fun y => prod_nonneg fun i _ => (q i).nonneg (y i)
    total := by rw [← Fintype.prod_sum]; simp only [Law.total, prod_const_one] }

lemma productLaw_apply (q : ∀ i, Law (β i)) (y : ∀ i, β i) :
    productLaw q y = ∏ i, q i (y i) := rfl

lemma mean_productLaw_exp_sum (q : ∀ i, Law (β i)) (F : ∀ i, β i → ℝ) (t : ℝ) :
    mean (productLaw q) (fun y => Real.exp (t * ∑ i, F i (y i))) =
      ∏ i, mean (q i) (fun b => Real.exp (t * F i b)) := by
  classical
  simp only [mean, productLaw_apply, mul_sum, Real.exp_sum, ← prod_mul_distrib]
  exact (Fintype.prod_sum (fun i b => q i b * Real.exp (t * F i b))).symm

/-- Finite product Hoeffding bound with coordinatewise bounds. -/
theorem mean_productLaw_exp_sum_le (q : ∀ i, Law (β i)) (F : ∀ i, β i → ℝ)
    (B : ι → ℝ) (hB : ∀ i, 0 ≤ B i) (hb : ∀ i b, |F i b| ≤ B i)
    (hc : ∀ i, mean (q i) (F i) = 0) (t : ℝ) :
    mean (productLaw q) (fun y => Real.exp (t * ∑ i, F i (y i))) ≤
      Real.exp ((∑ i, B i ^ 2) * t ^ 2 / 2) := by
  classical
  rw [mean_productLaw_exp_sum]
  calc
    _ ≤ ∏ i, Real.exp (B i ^ 2 * t ^ 2 / 2) := by
      apply prod_le_prod
      · intro i _
        exact (mean_exp_pos (q i) (fun b => t * F i b)).le
      · intro i _
        exact mean_exp_mul_le_bounded (q i) (F i) (hB i) (hb i) (hc i) t
    _ = _ := by rw [← Real.exp_sum, ← sum_div, ← sum_mul]

/-- Averages of independent centered unit-bounded coordinates are subgaussian
with variance proxy the inverse of the number of coordinates. -/
theorem mean_productLaw_exp_average_le [Nonempty ι]
    (q : ∀ i, Law (β i)) (F : ∀ i, β i → ℝ)
    (hb : ∀ i b, |F i b| ≤ 1) (hc : ∀ i, mean (q i) (F i) = 0) (t : ℝ) :
    mean (productLaw q) (fun y =>
      Real.exp (t * ((∑ i, F i (y i)) / Fintype.card ι))) ≤
      Real.exp ((Fintype.card ι : ℝ)⁻¹ * t ^ 2 / 2) := by
  have hcard : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hh := mean_productLaw_exp_sum_le q F (fun _ => 1) (fun _ => zero_le_one)
    hb hc (t / Fintype.card ι)
  have he (y : ∀ i, β i) :
      t * ((∑ i, F i (y i)) / Fintype.card ι) =
        t / Fintype.card ι * (∑ i, F i (y i)) := by ring
  simp only [he]
  convert hh using 1
  simp only [one_pow, sum_const, nsmul_eq_mul, mul_one, card_univ]
  congr 1
  field_simp

/-- Information decoupling of a coordinate average. Only the residue marginal
is required to be a product; dependence on the first variable is measured, not
assumed absent. -/
theorem average_sq_le_mutualInformation [Nonempty ι]
    (P : Law (α × (∀ i, β i))) (q : ∀ i, Law (β i))
    (hq : secondMarginal P = productLaw q) (G : α → ∀ i, β i → ℝ)
    (hb : ∀ a i b, |G a i b| ≤ 1) (hc : ∀ a i, mean (q i) (G a i) = 0) :
    (mean P (fun ay => (∑ i, G ay.1 i (ay.2 i)) / Fintype.card ι)) ^ 2 ≤
      2 * mutualInformation P / Fintype.card ι := by
  have hcard : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have hh := mean_sq_le_mutualInformation P
    (fun ay => (∑ i, G ay.1 i (ay.2 i)) / Fintype.card ι) (inv_pos.mpr hcard)
    (fun a t => by
      rw [hq]
      exact mean_productLaw_exp_average_le q (G a) (hb a) (hc a) t)
  convert hh using 1
  ring

#print axioms mean_productLaw_exp_sum_le
#print axioms average_sq_le_mutualInformation

end Erdos371.FiniteInformation
