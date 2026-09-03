import FormalConjecturesUtil

/-!
An exponent check for one proposed use of the divisor-cycle bound. This
concerns only the combination of a size-based exclusion threshold and a
particular trace-to-operator bound. It rules out neither stronger signed
moment estimates nor the density conjecture.
-/
namespace Erdos371
open Filter
open scoped Topology

/-- For a moment of length `2*k`, the size-based cycle exclusion threshold
is strictly above the threshold for a power saving from the crude moment
budget when `k > 1`. -/
lemma cycle_moment_threshold_gap (k : ℕ) (hk : 1 < k) :
    (k : ℝ) / (k+1) < 1 - 1/(2*k : ℝ) := by
  have hkR : (1 : ℝ) < k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  apply (div_lt_iff₀ (by positivity : (0 : ℝ) < k+1)).mpr
  have he : (1 - 1/(2*k : ℝ))*(k+1) - k = (k-1)/(2*k : ℝ) := by
    field_simp
    ring
  have hp : 0 < (k-1)/(2*k : ℝ) := div_pos (by linarith) (by positivity)
  linarith

/-- This normalized exponent comes from multiplying the `2*k`-th root
of `N^k/P^(k-1)` by the label count `P`, and then dividing by `N`, with
`P=N^beta`. It is not an assertion about the actual signed moment. -/
noncomputable def crudeCycleMomentExponent (k : ℕ) (β : ℝ) : ℝ :=
  β*(k+1)/(2*k : ℝ)-1/2

lemma crudeCycleMomentExponent_lower (k : ℕ) (hk : 0 < k) (β : ℝ)
    (hβ : 1-1/(2*k : ℝ) ≤ β) :
    (k-1 : ℝ)/(4*(k : ℝ)^2) ≤ crudeCycleMomentExponent k β := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hm := mul_le_mul_of_nonneg_right hβ
    (show 0 ≤ (k+1 : ℝ)/(2*k : ℝ) by positivity)
  unfold crudeCycleMomentExponent
  have he : (1-1/(2*k : ℝ))*((k+1 : ℝ)/(2*k : ℝ))-1/2 =
      (k-1 : ℝ)/(4*(k : ℝ)^2) := by
    field_simp
    ring
  rw [← he]
  simpa only [mul_div_assoc] using sub_le_sub_right hm (1/2)

lemma crudeCycleMomentExponent_pos (k : ℕ) (hk : 1 < k) (β : ℝ)
    (hβ : 1-1/(2*k : ℝ) ≤ β) :
    0 < crudeCycleMomentExponent k β := by
  have hkR : (1 : ℝ) < k := by exact_mod_cast hk
  exact (div_pos (by linarith) (by positivity) :
    0 < (k-1 : ℝ)/(4*(k : ℝ)^2)).trans_le
      (crudeCycleMomentExponent_lower k (by omega) β hβ)

/-- At every admissible size-exclusion exponent, the crude normalized
budget grows, rather than tending to zero. Increasing the moment length
alone therefore does not justify a power saving by this argument. -/
theorem crudeCycleMomentBudget_tendsto_atTop (k : ℕ) (hk : 1 < k) (β : ℝ)
    (hβ : 1-1/(2*k : ℝ) ≤ β) :
    Tendsto (fun N : ℕ => (N : ℝ) ^ crudeCycleMomentExponent k β) atTop atTop := by
  exact (tendsto_rpow_atTop (crudeCycleMomentExponent_pos k hk β hβ)).comp
    tendsto_natCast_atTop_atTop

#print axioms cycle_moment_threshold_gap
#print axioms crudeCycleMomentBudget_tendsto_atTop
end Erdos371
