import FormalConjecturesUtil

/-! Order estimates for prefixes of positive linear-operator iterations. -/
namespace Erdos7KilledSieve
set_option maxHeartbeats 4000000
section Operator
variable {ι : Type*}

lemma monotone_operator_pow_nonneg (T : Module.End ℚ (ι → ℚ)) (hT : Monotone T)
    (H : ι → ℚ) (hH : 0 ≤ H) (k : ℕ) : 0 ≤ (T^k) H := by
  induction k with
  | zero => simpa using hH
  | succ k ih =>
    rw [pow_succ',Module.End.mul_apply]
    simpa only [map_zero] using hT ih

lemma scalar_add_operator_monotone (T : Module.End ℚ (ι → ℚ)) (hT : Monotone T)
    (α : ℚ) (hα : 0 ≤ α) : Monotone (α • (1:Module.End ℚ (ι → ℚ))+T) := by
  intro H J hHJ i
  change α*H i+T H i ≤ α*J i+T J i
  exact add_le_add (mul_le_mul_of_nonneg_left (hHJ i) hα) (hT hHJ i)

lemma positive_operator_powers_mono (T U : Module.End ℚ (ι → ℚ))
    (hT : Monotone T) (hU : Monotone U)
    (hTU : ∀ H : ι → ℚ,0 ≤ H → T H ≤ U H)
    (H : ι → ℚ) (hH : 0 ≤ H) (k : ℕ) : (T^k) H ≤ (U^k) H := by
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
    rw [pow_succ',pow_succ',Module.End.mul_apply,Module.End.mul_apply]
    exact (hTU _ (monotone_operator_pow_nonneg T hT H hH k)).trans (hU ih)

lemma identity_add_operator_pow_le_succ (T : Module.End ℚ (ι → ℚ)) (hT : Monotone T)
    (H : ι → ℚ) (hH : 0 ≤ H) (k : ℕ) :
    ((1+T)^k) H ≤ ((1+T)^(k+1)) H := by
  have hB : Monotone ((1:Module.End ℚ (ι → ℚ))+T) := by
    simpa only [one_smul] using scalar_add_operator_monotone T hT 1 (by norm_num)
  have hpos := monotone_operator_pow_nonneg (1+T) hB H hH k
  have hposT : 0 ≤ T (((1+T)^k) H) := by simpa only [map_zero] using hT hpos
  rw [pow_succ',Module.End.mul_apply]
  intro i
  change ((1+T)^k) H i ≤ ((1+T)^k) H i+T (((1+T)^k) H) i
  exact le_add_of_nonneg_right (hposT i)

lemma identity_add_operator_pow_mono (T : Module.End ℚ (ι → ℚ)) (hT : Monotone T)
    (H : ι → ℚ) (hH : 0 ≤ H) {j k : ℕ} (hjk : j ≤ k) :
    ((1+T)^j) H ≤ ((1+T)^k) H := by
  exact monotone_nat_of_le_succ (identity_add_operator_pow_le_succ T hT H hH) hjk

/-- Dropping the negative diagonal correction is needed only for a uniform
upper bound on intermediate losses, not for the final block profile. -/
theorem scalar_add_operator_prefix_bound (T : Module.End ℚ (ι → ℚ)) (hT : Monotone T)
    (α : ℚ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (H : ι → ℚ) (hH : 0 ≤ H)
    {j k : ℕ} (hjk : j ≤ k) :
    ((α • (1:Module.End ℚ (ι → ℚ))+T)^j) H ≤ ((1+T)^k) H := by
  have hA := scalar_add_operator_monotone T hT α hα0
  have hB : Monotone ((1:Module.End ℚ (ι → ℚ))+T) := by
    simpa only [one_smul] using scalar_add_operator_monotone T hT 1 (by norm_num)
  have hAB : ∀ F : ι → ℚ,0 ≤ F → (α • (1:Module.End ℚ (ι → ℚ))+T) F ≤ (1+T) F := by
    intro F hF i
    change α*F i+T F i ≤ F i+T F i
    exact add_le_add_left (mul_le_of_le_one_left (hF i) hα1) _
  exact (positive_operator_powers_mono _ _ hA hB hAB H hH j).trans
    (identity_add_operator_pow_mono T hT H hH hjk)

end Operator
#print axioms scalar_add_operator_prefix_bound
end Erdos7KilledSieve
