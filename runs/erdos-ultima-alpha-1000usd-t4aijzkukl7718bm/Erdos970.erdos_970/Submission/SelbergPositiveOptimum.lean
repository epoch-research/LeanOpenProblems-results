import Submission.SelbergCost
import Submission.SelbergSignedExample

/-! Exact optimality in the nonnegative orthogonal-coefficient cone.
This does not assert optimality among signed coefficients, nor a Jacobsthal bound. -/
namespace Erdos970.SelbergPositiveOptimum
open Finset
variable {ι : Type*} [Fintype ι]

noncomputable def cost (a c : ι → ℝ) : ℝ := ∑ i, a i * c i
noncomputable def objective (v a : ι → ℝ) (X : ℝ) (c : ι → ℝ) : ℝ :=
  X * (∑ i, v i * c i ^ 2) + cost a c ^ 2

/-- The exact quadratic gap identity behind the nonnegative optimality test. -/
lemma gap_identity (v a b c : ι → ℝ) (X L : ℝ)
    (hX : cost a b = X) (hsum : (∑ i, c i) = ∑ i, b i)
    (hcomp : ∀ i, (v i * b i + a i - L) * b i = 0) :
    objective v a X c - objective v a X b =
      X * (∑ i, v i * (c i - b i) ^ 2) + (cost a c - X) ^ 2 +
        2 * X * (∑ i, (v i * b i + a i - L) * c i) := by
  have hcomp' : (∑ i, v i * b i ^ 2) + cost a b - L * (∑ i, b i) = 0 := by
    have h := sum_congr (s₁ := univ) rfl (fun i _ => hcomp i)
    simp only [sum_const_zero] at h
    convert h using 1
    simp only [cost, add_mul, sub_mul, sum_sub_distrib, sum_add_distrib, mul_sum]
    congr 2
    apply sum_congr rfl
    intro i hi
    ring
  have hsq : (∑ i, v i * (c i - b i) ^ 2) =
      (∑ i, v i * c i ^ 2) + (∑ i, v i * b i ^ 2) -
        2 * (∑ i, v i * b i * c i) := by
    rw [← sum_add_distrib, mul_sum, ← sum_sub_distrib]
    apply sum_congr rfl
    intro i hi
    ring
  have hlinear : (∑ i, (v i * b i + a i - L) * c i) =
      (∑ i, v i * b i * c i) + cost a c - L * (∑ i, c i) := by
    simp only [sub_mul, add_mul, sum_sub_distrib, sum_add_distrib, cost, mul_sum]
  rw [hsq, hlinear, hsum]
  dsimp only [objective]
  rw [hX] at hcomp' ⊢
  linear_combination -2 * X * hcomp'

/-- A sufficient KKT certificate, proved by a sum of nonnegative squares. -/
theorem minimizes_nonnegative (v a b : ι → ℝ) (X L : ℝ)
    (hv : ∀ i, 0 ≤ v i) (hXnonneg : 0 ≤ X) (hX : cost a b = X)
    (hgrad : ∀ i, L ≤ v i * b i + a i)
    (hcomp : ∀ i, (v i * b i + a i - L) * b i = 0)
    (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i) (hsum : (∑ i, c i) = ∑ i, b i) :
    objective v a X b ≤ objective v a X c := by
  have hg := gap_identity v a b c X L hX hsum hcomp
  have hq : 0 ≤ X * (∑ i, v i * (c i - b i) ^ 2) :=
    mul_nonneg hXnonneg (sum_nonneg (fun i _ => mul_nonneg (hv i) (sq_nonneg _)))
  have hl : 0 ≤ 2 * X * (∑ i, (v i * b i + a i - L) * c i) :=
    mul_nonneg (by positivity) (sum_nonneg (fun i _ => mul_nonneg (sub_nonneg.mpr (hgrad i)) (hc i)))
  linarith [sq_nonneg (cost a c - X)]

/-- The positive-part profile is a globally optimal nonnegative coefficient vector,
not merely a stationary point on its chosen support. -/
theorem cutoff_minimizes (v a : ι → ℝ) (L : ℝ) (hv : ∀ i, 0 < v i)
    (ha : ∀ i, 0 ≤ a i) :
    let b := fun i => max (L - a i) 0 / v i
    ∀ c : ι → ℝ, (∀ i, 0 ≤ c i) → (∑ i, c i) = ∑ i, b i →
      objective v a (cost a b) b ≤ objective v a (cost a b) c := by
  dsimp only
  intro c hc hsum
  apply minimizes_nonnegative v a (fun i => max (L - a i) 0 / v i)
    (cost a (fun i => max (L - a i) 0 / v i)) L
    (fun i => (hv i).le) _ rfl _ _ c hc hsum
  · exact sum_nonneg (fun i _ => mul_nonneg (ha i) (div_nonneg (le_max_right _ _) (hv i).le))
  · intro i
    rw [mul_div_cancel₀ _ (hv i).ne']
    linarith [le_max_left (L - a i) 0]
  · intro i
    rw [mul_div_cancel₀ _ (hv i).ne']
    by_cases hi : a i ≤ L
    · rw [max_eq_left (sub_nonneg.mpr hi)]
      ring
    · simp only [max_eq_right (by linarith : L - a i ≤ 0), zero_div, mul_zero]

#print axioms cutoff_minimizes
end Erdos970.SelbergPositiveOptimum

namespace Erdos970.SelbergSignedExample
open Finset

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The exact complementary-slackness certificate at the six-prime cutoff. -/
theorem positive_certificate :
    (∀ Q : Pattern, 0 < variance Q) ∧
    (∀ Q : Pattern, (24192 : ℚ) ≤ variance Q * base Q + height Q) ∧
    (∀ Q : Pattern, (variance Q * base Q + height Q - 24192) * base Q = 0) := by
  decide +kernel

noncomputable def sieveObjective (c : Pattern → ℝ) : ℝ :=
  (32668496 / 5 : ℝ) * FiniteSelberg.average marginal (fun ω =>
    FiniteSelberg.linearKernel marginal c ω ^ 2) + FiniteSelberg.kernelCost marginal c ^ 2

lemma real_height (Q : Pattern) :
    (∏ i ∈ Q, (1 + (marginal i)⁻¹)) = (height Q : ℝ) := by
  simp [height, marginal, add_comm]

lemma sieveObjective_eq_of_nonneg (c : Pattern → ℝ) (hc : ∀ Q, 0 ≤ c Q) :
    sieveObjective c = SelbergPositiveOptimum.objective
      (fun Q => (variance Q : ℝ)) (fun Q => (height Q : ℝ)) (32668496 / 5) c := by
  have havg : FiniteSelberg.average marginal (fun ω =>
      FiniteSelberg.linearKernel marginal c ω ^ 2) = ∑ Q : Pattern, (variance Q : ℝ) * c Q ^ 2 := by
    rw [show (fun ω => FiniteSelberg.linearKernel marginal c ω ^ 2) =
      (fun ω => (∑ Q : Pattern, c Q * FiniteSelberg.basis marginal Q ω) ^ 2) by rfl,
      FiniteSelberg.average_square_sum marginal (fun i => (marginal_bounds i).1.ne')]
    simp only [real_variance, mul_comm]
  have hcost : FiniteSelberg.kernelCost marginal c = SelbergPositiveOptimum.cost
      (fun Q => (height Q : ℝ)) c := by
    rw [FiniteSelberg.kernelCost_of_nonneg marginal (fun i => (marginal_bounds i).1) c hc]
    simp only [real_height, SelbergPositiveOptimum.cost, mul_comm]
  simp only [sieveObjective, havg, hcost, SelbergPositiveOptimum.objective]

lemma real_base_nonneg (Q : Pattern) : 0 ≤ (base Q : ℝ) := Rat.cast_nonneg.mpr (exact_example.1 Q)

/-- Global optimality over all real nonnegative orthogonal coefficients with
this fixed empty-pattern value, not just over cutoff profiles. -/
theorem base_minimizes_all_nonnegative (c : Pattern → ℝ) (hc : ∀ Q, 0 ≤ c Q)
    (hsum : (∑ Q : Pattern, c Q) = ∑ Q : Pattern, (base Q : ℝ)) :
    sieveObjective (fun Q => (base Q : ℝ)) ≤ sieveObjective c := by
  rw [sieveObjective_eq_of_nonneg _ real_base_nonneg, sieveObjective_eq_of_nonneg c hc]
  have hX : SelbergPositiveOptimum.cost (fun Q => (height Q : ℝ)) (fun Q => (base Q : ℝ)) =
      32668496 / 5 := by
    have hcost : FiniteSelberg.kernelCost marginal (fun Q => (base Q : ℝ)) =
        SelbergPositiveOptimum.cost (fun Q => (height Q : ℝ)) (fun Q => (base Q : ℝ)) := by
      rw [FiniteSelberg.kernelCost_of_nonneg marginal (fun i => (marginal_bounds i).1) _ real_base_nonneg]
      simp only [real_height, SelbergPositiveOptimum.cost, mul_comm]
    rw [← hcost, real_cost, exact_example.2.2.2.2.1]
    norm_num
  apply SelbergPositiveOptimum.minimizes_nonnegative
    (fun Q => (variance Q : ℝ)) (fun Q => (height Q : ℝ)) (fun Q => (base Q : ℝ))
    (32668496 / 5) 24192 (fun Q => le_of_lt (Rat.cast_pos.mpr (positive_certificate.1 Q)))
    (by positivity) hX _ _ c hc hsum
  · intro Q
    have h := (Rat.cast_le (K := ℝ)).mpr (positive_certificate.2.1 Q)
    simpa only [Rat.cast_ofNat, Rat.cast_add, Rat.cast_mul, Rat.cast_natCast] using h
  · intro Q
    have h := congrArg (fun x : ℚ => (x : ℝ)) (positive_certificate.2.2 Q)
    simpa only [Rat.cast_mul, Rat.cast_sub, Rat.cast_add, Rat.cast_natCast,
      Rat.cast_ofNat, Rat.cast_zero] using h

/-- The signed kernel is strictly better than EVERY nonnegative orthogonal
kernel with the same normalization. This is a finite-dimensional separation,
not an asymptotic Jacobsthal estimate. -/
theorem signed_beats_all_nonnegative (c : Pattern → ℝ) (hc : ∀ Q, 0 ≤ c Q)
    (hsum : (∑ Q : Pattern, c Q) = ∑ Q : Pattern, (base Q : ℝ)) :
    sieveObjective (fun Q => (signed Q : ℝ)) < sieveObjective c :=
  lt_of_lt_of_le real_objective_improves (base_minimizes_all_nonnegative c hc hsum)

#print axioms positive_certificate
#print axioms base_minimizes_all_nonnegative
#print axioms signed_beats_all_nonnegative
end Erdos970.SelbergSignedExample
