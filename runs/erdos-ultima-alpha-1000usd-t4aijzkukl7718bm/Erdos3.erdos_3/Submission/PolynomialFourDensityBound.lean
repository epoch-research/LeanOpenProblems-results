import Submission.PolynomialProgressionThresholds
import Submission.IntegerFourDensityBound

/-! A power-iteration upper bound for the four-term density threshold.
Polynomial dependence on the requested next length does not by itself give
reciprocal summability. -/
namespace Erdos3PolynomialFourDensityBound
open Finset Erdos3PolynomialProgressionThresholds Erdos3IntegerFourDensityBound
  Erdos3IntegerFourDensityIncrement Erdos3ProgressionIncrementParameters
  Erdos3NormalizedQuadraticInverse Erdos3CyclicIntervalMask
open scoped Classical
set_option maxHeartbeats 3000000
set_option maxRecDepth 3000

lemma HasPolyBound.mono {f g : ℕ → ℕ} {e : ℕ}
    (hf : HasPolyBound f e) (hgf : ∀ n, g n ≤ f n) : HasPolyBound g e := by
  obtain ⟨C,hC⟩ := hf
  exact ⟨C,fun n ↦ (Nat.add_le_add_right (hgf n) 1).trans (hC n)⟩

noncomputable def fourStepDegree (α : ℝ) : ℕ :=
  69*(2*normalizedRank (intervalUniformityThreshold α)+1)

lemma intervalStepThreshold_poly (α : ℝ) :
    HasPolyBound (intervalStepThreshold α) (fourStepDegree α) := by
  have hL : HasPolyBound (requestedCyclicLength α) 1 :=
    poly_id.rounded (intervalGain α)
  have hbase := (incrementThreshold_poly
    (normalizedRank (intervalUniformityThreshold α)) (intervalGain α)).comp hL
  have hbase' : HasPolyBound (fun ℓ ↦ incrementThreshold
      (normalizedRank (intervalUniformityThreshold α)) (requestedCyclicLength α ℓ)
      (intervalGain α)) (fourStepDegree α) := by
    simpa only [Nat.one_mul,fourStepDegree] using hbase
  apply HasPolyBound.mono (hbase'.affine 1 (8+⌈4096/α^4⌉₊))
  intro ℓ
  unfold intervalStepThreshold
  omega

/-- Iterating a degree-e polynomial upper bound requires at most a power whose
exponent grows geometrically with the number of iterations. -/
lemma polynomial_iteration_bound (f Q : ℕ → ℕ) {e C : ℕ}
    (hf : ∀ n, f n+1 ≤ C*(n+1)^e)
    (hQ0 : Q 0 = 1) (hQ : ∀ t, Q (t+1) = f (Q t)) (t : ℕ) :
    Q t+1 ≤ (C+2)^((e+1)^t) := by
  induction t with
  | zero => simp only [hQ0,pow_zero,pow_one]; omega
  | succ t ih =>
    rw [hQ]
    calc
      _ ≤ C*(Q t+1)^e := hf _
      _ ≤ (C+2)*((C+2)^((e+1)^t))^e := Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left ih e)
      _ = (C+2)^(1+(e+1)^t*e) := by rw [pow_add,pow_one,pow_mul]
      _ ≤ (C+2)^((e+1)^(t+1)) := by
        apply Nat.pow_le_pow_right (by omega)
        have hp : 1 ≤ (e+1)^t := Nat.one_le_pow _ _ (by omega)
        rw [pow_succ]
        nlinarith only [hp]

theorem fourIterationThreshold_power_bound (α : ℝ) :
    ∃ B : ℕ, 2 ≤ B ∧ ∀ t : ℕ,
      fourIterationThreshold α t+1 ≤ B^((fourStepDegree α+1)^t) := by
  obtain ⟨C,hC⟩ := intervalStepThreshold_poly α
  refine ⟨C+2,by omega,?_⟩
  intro t
  exact polynomial_iteration_bound (intervalStepThreshold α) (fourIterationThreshold α)
    hC rfl (fun _ ↦ rfl) t

/-- Quantitative four-term theorem with a power-iteration bound. The base B
and degree depend on the density; neither is uniform in that density. -/
theorem integer_four_power_density_bound {α : ℝ} (hα : 0 < α) :
    ∃ B : ℕ, 2 ≤ B ∧ ∀ N : ℕ, ∀ S : Finset ℕ,
      S ⊆ range N → (S : Set ℕ).IsAPOfLengthFree 4 → α ≤ intervalDensity S N →
      N < B^((fourStepDegree α+1)^(fourIterationCount α)) := by
  obtain ⟨B,hB,hbound⟩ := fourIterationThreshold_power_bound α
  refine ⟨B,hB,?_⟩
  intro N S hS hfree hden
  have hh := integer_four_density_bound hα N S hS hfree hden
  have hb := hbound (fourIterationCount α)
  change N < fourIterationThreshold α (fourIterationCount α) at hh
  exact hh.trans_le ((Nat.le_succ _).trans hb)

#print axioms intervalStepThreshold_poly
#print axioms integer_four_power_density_bound
end Erdos3PolynomialFourDensityBound
