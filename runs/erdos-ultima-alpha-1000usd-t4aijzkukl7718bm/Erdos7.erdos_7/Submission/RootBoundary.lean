import Submission.FiniteRetainedMixture

/-! A nonconstant boundary budget can yield a strict bound for every finite
initial exponent cap. This is a criterion, not a construction of such a budget
and not a proof of the odd covering conjecture. -/
namespace Erdos7RootBoundary
open scoped BigOperators
open Erdos7FiniteRetainedMixture
set_option maxHeartbeats 1000000

/-- Scaling every positive tail by 1/(1+r) mixes the comparison with a point
mass at its baseline. The scalar test is allowed to take negative values. -/
lemma scaled_mixture_identity (q f : ℕ → ℝ) (R : ℕ) (r : ℝ) (hr : 1+r ≠ 0) :
    mixture 1 (fun j => q j/(1+r)) f R =
      (r*f 0+mixture 1 q f R)/(1+r) := by
  unfold mixture
  simp only [one_mul]
  have he : (∑ j ∈ Finset.range R, q j/(1+r)*(f (j+1)-f j)) =
      (∑ j ∈ Finset.range R, q j*(f (j+1)-f j))/(1+r) := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he]
  field_simp
  <;> ring

/-- A bound at most one, together with a strict baseline value, is enough
once the finite initial profile has a positive baseline mixing weight. -/
theorem finite_boundary_strict (q f : ℕ → ℝ) (R : ℕ) (r : ℝ)
    (hr : 0 < r) (hf : f 0 < 1) (hbound : mixture 1 q f R ≤ 1) :
    mixture 1 (fun j => q j/(1+r)) f R < 1 := by
  have hd : 0 < 1+r := by linarith
  rw [scaled_mixture_identity q f R r hd.ne']
  apply (div_lt_one hd).mpr
  have hh := mul_lt_mul_of_pos_left hf hr
  linarith

/-- An infinite monotone budget at the boundary can control every finite cap
strictly, without a uniform positive gap as the cap grows. -/
theorem infinite_boundary_finite_strict (q f : ℕ → ℝ)
    (hq : ∀ j, 0 ≤ q j) (hf : Monotone f)
    (hs : Summable (fun j => q j*(f (j+1)-f j)))
    (hbase : f 0 < 1)
    (hbound : f 0+(∑' j, q j*(f (j+1)-f j)) ≤ 1)
    (R : ℕ) (r : ℝ) (hr : 0 < r) :
    mixture 1 (fun j => q j/(1+r)) f R < 1 := by
  apply finite_boundary_strict q f R r hr hbase
  have hh := mixture_le_infinite 1 q f hq hf hs R
  simp only [one_mul] at hh
  exact hh.trans hbound

/-- For the prime3 initial coordinate, the finite zero-loss density cap is
2/(1+3^(-E)), rather than its limiting value2. This strict difference cannot
be discarded when investigating a boundary certificate. -/
theorem ternary_boundary_strict (f : ℕ → ℝ) (hf : Monotone f)
    (hs : Summable (fun j => (2/(3:ℝ)^(j+1))*(f (j+1)-f j)))
    (hbase : f 0 < 1)
    (hbound : f 0+(∑' j, (2/(3:ℝ)^(j+1))*(f (j+1)-f j)) ≤ 1)
    (E : ℕ) :
    mixture 1 (fun j => (2/(1+1/(3:ℝ)^E))/(3:ℝ)^(j+1)) f E < 1 := by
  have hq : ∀ j, 0 ≤ 2/(3:ℝ)^(j+1) := fun _ => by positivity
  have hr : 0 < 1/(3:ℝ)^E := by positivity
  have hh := infinite_boundary_finite_strict (fun j => 2/(3:ℝ)^(j+1)) f
    hq hf hs hbase hbound E (1/(3:ℝ)^E) hr
  convert hh using 2
  funext j
  ring

#print axioms infinite_boundary_finite_strict
#print axioms ternary_boundary_strict
end Erdos7RootBoundary
