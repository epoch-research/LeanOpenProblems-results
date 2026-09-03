import Submission.SelbergEnergyCriterion
import Submission.PrimeSetMertens

/-! Exact coefficient costs for nonnegative orthogonal Selberg kernels, and
uniform linear bounds for divisor-cutoff cost sums. -/
namespace Erdos970.FiniteSelberg
open Finset Real
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma ordinaryCoefficient_abs_of_nonneg (q : ι → ℝ) (hq : ∀ i, 0 < q i)
    (c : Finset ι → ℝ) (hc : ∀ Q, 0 ≤ c Q) (T : Finset ι) :
    |ordinaryCoefficient q c T| = (∑ Q : Finset ι, if T ⊆ Q then c Q else 0) / ∏ i ∈ T, q i := by
  have hs : 0 ≤ ∑ Q : Finset ι, if T ⊆ Q then c Q else 0 :=
    sum_nonneg (fun Q _ => by split_ifs; exact hc Q; rfl)
  rw [ordinaryCoefficient, abs_mul, abs_div, abs_pow, abs_neg, abs_one, one_pow,
    abs_of_pos (prod_pos (fun i _ => hq i)), abs_of_nonneg hs]
  ring

/-- No triangle inequality is lost in this cost formula: the ordinary coefficients
have alternating signs when the orthogonal coefficients are nonnegative. -/
theorem kernelCost_of_nonneg (q : ι → ℝ) (hq : ∀ i, 0 < q i)
    (c : Finset ι → ℝ) (hc : ∀ Q, 0 ≤ c Q) :
    kernelCost q c = ∑ Q : Finset ι, c Q * ∏ i ∈ Q, (1 + (q i)⁻¹) := by
  unfold kernelCost
  simp_rw [ordinaryCoefficient_abs_of_nonneg q hq c hc, sum_div]
  rw [sum_comm]
  apply sum_congr rfl
  intro Q hQ
  rw [prod_one_add, mul_sum]
  simp only [prod_inv_distrib, ite_div, zero_div, div_eq_mul_inv]
  simp [← mem_powerset]

/-- In weighted coordinates the exact cost has a simple multiplicative summand. -/
theorem kernelCost_weighted (q : ι → ℝ) (hq : ∀ i, 0 < q i ∧ q i < 1)
    (f : Finset ι → ℝ) (hf : ∀ Q, 0 ≤ f Q) :
    kernelCost q (fun Q => weight q Q * f Q) =
      ∑ Q : Finset ι, f Q * ∏ i ∈ Q, ((1 + q i) / (1 - q i)) := by
  rw [kernelCost_of_nonneg q (fun i => (hq i).1) _
    (fun Q => mul_nonneg (weight_pos q hq Q).le (hf Q))]
  apply sum_congr rfl
  intro Q hQ
  rw [weight]
  calc
    _ = f Q * ∏ i ∈ Q, (q i / (1 - q i)) * (1 + (q i)⁻¹) := by rw [prod_mul_distrib]; ring
    _ = _ := by
      congr 1
      apply prod_congr rfl
      intro i hi
      have h0 := (hq i).1.ne'
      have h1 := (sub_pos.mpr (hq i).2).ne'
      field_simp
      <;> ring

lemma superset_divisorSupport_card_le (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hpinj : Function.Injective p) (R : ℕ) (T : Finset ι) :
    ((divisorSupport p R).filter (fun Q => T ⊆ Q)).card ≤ R / ∏ i ∈ T, p i := by
  classical
  let d := ∏ i ∈ T, p i
  have hd : 0 < d := prod_pos (fun i _ => (hp i).pos)
  have hdiv (Q : Finset ι) (hTQ : T ⊆ Q) : d ∣ ∏ i ∈ Q, p i := prod_dvd_prod_of_subset T Q p hTQ
  have hmap (Q : Finset ι) (hQ : Q ∈ (divisorSupport p R).filter (fun Q => T ⊆ Q)) :
      (∏ i ∈ Q, p i) / d ∈ Icc 1 (R / d) := by
    obtain ⟨hQR, hTQ⟩ := mem_filter.mp hQ
    refine mem_Icc.mpr ⟨?_, Nat.div_le_div_right ((mem_divisorSupport p R Q).mp hQR)⟩
    exact Nat.div_pos (Nat.le_of_dvd (prod_pos (fun i _ => (hp i).pos)) (hdiv Q hTQ)) hd
  have hinj : Set.InjOn (fun Q : Finset ι => (∏ i ∈ Q, p i) / d)
      (↑((divisorSupport p R).filter (fun Q => T ⊆ Q)) : Set (Finset ι)) := by
    intro A hA B hB hab
    apply prime_subset_product_injective p hp hpinj
    have hda := hdiv A (mem_filter.mp hA).2
    have hdb := hdiv B (mem_filter.mp hB).2
    have h := congrArg (fun n : ℕ => d * n) hab
    simpa only [Nat.mul_div_cancel' hda, Nat.mul_div_cancel' hdb] using h
  have h := card_le_card_of_injOn
    (s := (divisorSupport p R).filter (fun Q => T ⊆ Q)) (t := Icc 1 (R / d))
    (fun Q => (∏ i ∈ Q, p i) / d) (fun Q hQ => hmap Q hQ) hinj
  simpa only [Nat.card_Icc, Nat.add_sub_cancel] using h

/-- A divisor-cutoff multiplicative sum, bounded by an Euler product after counting multiples. -/
theorem divisor_cost_sum_le_product (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hpinj : Function.Injective p) (R : ℕ) (b : ι → ℝ) (hb : ∀ i, 0 ≤ b i) :
    (∑ Q ∈ divisorSupport p R, ∏ i ∈ Q, (1 + b i)) ≤
      (R : ℝ) * ∏ i, (1 + b i / p i) := by
  classical
  have heq : (∑ Q ∈ divisorSupport p R, ∏ i ∈ Q, (1 + b i)) =
      ∑ T : Finset ι, (∏ i ∈ T, b i) *
        (((divisorSupport p R).filter (fun Q => T ⊆ Q)).card : ℝ) := by
    have hpower (Q : Finset ι) : (∑ T ∈ Q.powerset, ∏ i ∈ T, b i) =
        ∑ T : Finset ι, if T ⊆ Q then ∏ i ∈ T, b i else 0 := by
      simp [← mem_powerset]
    simp_rw [prod_one_add, hpower]
    rw [sum_comm]
    apply sum_congr rfl
    intro T hT
    rw [← sum_filter]
    simp [mul_comm]
  rw [heq, prod_one_add, powerset_univ, mul_sum]
  apply sum_le_sum
  intro T hT
  have hcardR : (((divisorSupport p R).filter (fun Q => T ⊆ Q)).card : ℝ) ≤
      (R : ℝ) / ∏ i ∈ T, (p i : ℝ) := by
    have h := (Nat.cast_le.mpr (superset_divisorSupport_card_le p hp hpinj R T) :
      (((divisorSupport p R).filter (fun Q => T ⊆ Q)).card : ℝ) ≤ (R / (∏ i ∈ T, p i) : ℕ))
    have hd := Nat.cast_div_le (m := R) (n := ∏ i ∈ T, p i) (α := ℝ)
    rw [Nat.cast_prod] at hd
    exact h.trans hd
  have hh := mul_le_mul_of_nonneg_left hcardR (prod_nonneg (s := T) (fun i _ => hb i))
  rw [prod_div_distrib]
  convert hh using 1 <;> ring

/-- A uniform linear bound for the unnormalized absolute coefficient cost sum. -/
theorem divisor_cost_sum_le (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hpinj : Function.Injective p) (R : ℕ) :
    (∑ Q ∈ divisorSupport p R, ∏ i ∈ Q, ((p i : ℝ) + 1) / (p i - 1)) ≤ exp 2 * R := by
  have hpred (i : ι) : 0 < (p i : ℝ) - 1 := by
    have h : (1 : ℝ) < p i := by exact_mod_cast (hp i).one_lt
    linarith
  have hfactor (i : ι) : ((p i : ℝ) + 1) / (p i - 1) = 1 + 2 / ((p i : ℝ) - 1) := by
    field_simp [(hpred i).ne']
    <;> ring
  simp_rw [hfactor]
  apply (divisor_cost_sum_le_product p hp hpinj R (fun i => 2 / ((p i : ℝ) - 1))
    (fun i => div_nonneg (by norm_num) (hpred i).le)).trans
  have hc : (∑ i, 1 / ((p i : ℝ) * (p i - 1))) ≤ 1 := by
    have h := WeightedMertens.reciprocal_correction_le_one (univ.image p)
      (fun a ha => by obtain ⟨i, hi, rfl⟩ := mem_image.mp ha; exact (hp i).two_le)
    rw [sum_image hpinj.injOn] at h
    exact h
  have hs : (∑ i, (2 / ((p i : ℝ) - 1)) / p i) ≤ 2 := by
    have heq : (∑ i, (2 / ((p i : ℝ) - 1)) / p i) =
        2 * ∑ i, 1 / ((p i : ℝ) * (p i - 1)) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro i hi
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    rw [heq]
    linarith
  have hprod : (∏ i, (1 + (2 / ((p i : ℝ) - 1)) / p i)) ≤ exp 2 := by
    calc
      _ ≤ ∏ i, exp ((2 / ((p i : ℝ) - 1)) / p i) := by
        apply prod_le_prod
        · intro i hi
          have hp0 : (0 : ℝ) ≤ p i := Nat.cast_nonneg _
          have := hpred i
          positivity
        · intro i hi
          linarith [add_one_le_exp ((2 / ((p i : ℝ) - 1)) / p i)]
      _ = exp (∑ i, (2 / ((p i : ℝ) - 1)) / p i) := (exp_sum _ _).symm
      _ ≤ _ := exp_le_exp.mpr hs
  nlinarith [Nat.cast_nonneg (α := ℝ) R]

#print axioms kernelCost_weighted
#print axioms divisor_cost_sum_le
end Erdos970.FiniteSelberg
