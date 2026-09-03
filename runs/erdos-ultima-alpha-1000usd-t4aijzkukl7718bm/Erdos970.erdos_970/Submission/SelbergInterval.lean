import Submission.SelbergCoefficients
import Submission.SievePolynomial

/-! An interval error estimate for the finite Selberg majorant. -/
namespace Erdos970.FiniteSelberg

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem hitMonomial_mul (T R : Finset ι) (ω : ι → Bool) :
    hitMonomial T ω * hitMonomial R ω = hitMonomial (T ∪ R) ω := by
  classical
  simp only [hitMonomial_eq, Finset.forall_mem_union]
  split_ifs <;> simp_all

theorem average_hitMonomial (q : ι → ℝ) (T : Finset ι) :
    average q (hitMonomial T) = ∏ i ∈ T, q i := by
  classical
  have heq : hitMonomial T = fun ω =>
      ∏ i : ι, if i ∈ T then (if ω i then (1 : ℝ) else 0) else 1 := by
    funext ω
    simp [hitMonomial, Finset.prod_ite_mem]
  rw [heq, average_prod q (fun i b => if i ∈ T then (if b then 1 else 0) else 1)]
  calc
    _ = ∏ i : ι, if i ∈ T then q i else 1 := by
      apply Finset.prod_congr rfl
      intro i hi
      by_cases hiT : i ∈ T <;> simp only [hiT, if_true, if_false,
        Bool.false_eq_true, mul_one, mul_zero, add_zero] <;> ring
    _ = _ := by simp [Finset.prod_ite_mem]

theorem majorant_expansion (q : ι → ℝ) (D : Finset (Finset ι))
    (hD : ∀ A ∈ D, ∀ B ⊆ A, B ∈ D) (ω : ι → Bool) :
    majorant q D ω = ∑ T ∈ D, ∑ R ∈ D,
      (coefficient q D T * coefficient q D R) * hitMonomial (T ∪ R) ω := by
  rw [majorant, kernel_expansion q D hD, pow_two, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro T hT
  apply Finset.sum_congr rfl
  intro R hR
  rw [← hitMonomial_mul]
  ring

theorem majorant_mean_expansion (q : ι → ℝ) (D : Finset (Finset ι))
    (hD : ∀ A ∈ D, ∀ B ⊆ A, B ∈ D) :
    average q (majorant q D) = ∑ T ∈ D, ∑ R ∈ D,
      (coefficient q D T * coefficient q D R) * ∏ i ∈ T ∪ R, q i := by
  change average q (fun ω => majorant q D ω) = _
  simp_rw [majorant_expansion q D hD]
  rw [average_sum]
  apply Finset.sum_congr rfl
  intro T hT
  rw [average_sum]
  apply Finset.sum_congr rfl
  intro R hR
  rw [average_mul_const, average_hitMonomial]

/-- Uniform intersection errors yield the square of the support size as an error term. -/
theorem majorant_interval_error (q : ι → ℝ) (hq : ∀ i, 0 < q i ∧ q i < 1)
    (D : Finset (Finset ι)) (hDn : D.Nonempty)
    (hD : ∀ A ∈ D, ∀ B ⊆ A, B ∈ D)
    (m : ℕ) (ω : ℕ → ι → Bool)
    (herr : ∀ T : Finset ι,
      |(∑ j ∈ Finset.range m, hitMonomial T (ω j)) - (m : ℝ) * ∏ i ∈ T, q i| ≤ 1) :
    |(∑ j ∈ Finset.range m, majorant q D (ω j)) -
      (m : ℝ) / normalizer q D| ≤ (D.card : ℝ)^2 := by
  classical
  have hmean := majorant_mean_expansion q D hD
  rw [majorant_average q hq D hDn] at hmean
  have heq : (∑ j ∈ Finset.range m, majorant q D (ω j)) - (m : ℝ) / normalizer q D =
      ∑ T ∈ D, ∑ R ∈ D, (coefficient q D T * coefficient q D R) *
        ((∑ j ∈ Finset.range m, hitMonomial (T ∪ R) (ω j)) -
          (m : ℝ) * ∏ i ∈ T ∪ R, q i) := by
    simp_rw [majorant_expansion q D hD]
    rw [Finset.sum_comm]
    simp_rw [Finset.sum_comm (s := Finset.range m), ← Finset.mul_sum]
    rw [div_eq_mul_one_div, hmean]
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro T hT
    apply Finset.sum_congr rfl
    intro R hR
    rw [← Finset.mul_sum]
    ring
  rw [heq]
  calc
    _ ≤ ∑ T ∈ D, ∑ R ∈ D, |(coefficient q D T * coefficient q D R) *
        ((∑ j ∈ Finset.range m, hitMonomial (T ∪ R) (ω j)) -
          (m : ℝ) * ∏ i ∈ T ∪ R, q i)| := by
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      exact Finset.sum_le_sum (fun T hT => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ T ∈ D, ∑ R ∈ D, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro T hT
      apply Finset.sum_le_sum
      intro R hR
      rw [abs_mul, abs_mul]
      have hc : |coefficient q D T| * |coefficient q D R| ≤ 1 := by
        simpa using mul_le_mul (coefficient_abs_le_one q hq D hDn hD T)
          (coefficient_abs_le_one q hq D hDn hD R) (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
      simpa using mul_le_mul hc (herr (T ∪ R)) (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    _ = _ := by simp [pow_two]

/-- The associated finite upper sieve, with an explicit support-size error. -/
theorem survivors_le (q : ι → ℝ) (hq : ∀ i, 0 < q i ∧ q i < 1)
    (D : Finset (Finset ι)) (hDn : D.Nonempty)
    (hD : ∀ A ∈ D, ∀ B ⊆ A, B ∈ D)
    (m : ℕ) (ω : ℕ → ι → Bool)
    (herr : ∀ T : Finset ι,
      |(∑ j ∈ Finset.range m, hitMonomial T (ω j)) - (m : ℝ) * ∏ i ∈ T, q i| ≤ 1) :
    (((Finset.range m).filter (fun j => ∀ i, ω j i = false)).card : ℝ) ≤
      (m : ℝ) / normalizer q D + (D.card : ℝ)^2 := by
  classical
  have hbound := (abs_le.mp (majorant_interval_error q hq D hDn hD m ω herr)).2
  have hcount : (((Finset.range m).filter (fun j => ∀ i, ω j i = false)).card : ℝ) =
      ∑ j ∈ Finset.range m, if ω j = (fun _ => false) then (1 : ℝ) else 0 := by
    simp [← Finset.sum_filter, funext_iff]
  rw [hcount]
  have hh := Finset.sum_le_sum (fun j (_ : j ∈ Finset.range m) =>
    indicator_empty_le_majorant q hq D hDn (ω j))
  linarith

#print axioms majorant_interval_error
#print axioms survivors_le

end Erdos970.FiniteSelberg
