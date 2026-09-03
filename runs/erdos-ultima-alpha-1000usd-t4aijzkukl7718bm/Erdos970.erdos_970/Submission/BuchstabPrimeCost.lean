import Submission.BuchstabRefinementCost

/-! Uniform marginal power sums and a valid level cutoff for prime lists.
The power-sum bound needs only injectivity into the positive integers. -/
namespace Erdos970.RecursiveSieve.Buchstab
open Finset Real

noncomputable def reciprocalPowerConstant (a : ℝ) : ℝ := ∑' j : ℕ, ((j : ℝ)^a)⁻¹

lemma reciprocalPowerConstant_nonneg (a : ℝ) : 0 ≤ reciprocalPowerConstant a :=
  tsum_nonneg (fun j => inv_nonneg.mpr (rpow_nonneg (Nat.cast_nonneg j) a))

lemma reciprocal_power_sum_le (p : ℕ → ℕ) (hp : Function.Injective p)
    (a : ℝ) (ha : 1 < a) (k : ℕ) :
    (∑ i : Fin k, (1/(p i.val : ℝ))^a) ≤ reciprocalPowerConstant a := by
  simp_rw [one_div, inv_rpow (Nat.cast_nonneg _)]
  rw [Fin.sum_univ_eq_sum_range (fun j => ((p j : ℝ)^a)⁻¹) k,
    ← sum_image (f := fun j : ℕ => ((j : ℝ)^a)⁻¹) hp.injOn]
  exact Summable.sum_le_tsum _ (fun j _ => inv_nonneg.mpr (rpow_nonneg (Nat.cast_nonneg j) a))
    (summable_nat_rpow_inv.mpr ha)

/-- The NEXT prime, including at the empty prefix, determines the cutoff. -/
def primeKeep (p : ℕ → ℕ) (k : ℕ) (D : ℝ) : Prop := (p k : ℝ)^2 ≤ D

lemma primeKeep_levels (p : ℕ → ℕ) (hp : ∀ i, (p i).Prime) (hmono : StrictMono p)
    (k : ℕ) (D : ℝ) (hk : primeKeep p k D) :
    1 ≤ D ∧ ∀ i < k, 1 ≤ D*(1/(p i : ℝ)) := by
  have hpk : (1 : ℝ) ≤ p k := by exact_mod_cast (hp k).one_lt.le
  change (p k : ℝ)^2 ≤ D at hk
  constructor
  · nlinarith
  · intro i hi
    have hpi : (1 : ℝ) ≤ p i := by exact_mod_cast (hp i).one_lt.le
    have hip : (p i : ℝ) ≤ p k := by exact_mod_cast (hmono hi).le
    rw [mul_one_div]
    exact (one_le_div (by linarith)).mpr (by nlinarith)

/-- A base error bounded by the divisor level has a uniform power bound after
any fixed number of alternating refinements. -/
theorem prime_refined_lowerError_le (p : ℕ → ℕ) (hp : ∀ i, (p i).Prime)
    (hmono : StrictMono p) (cost : ℕ → ℝ → ℝ)
    (hcost : ∀ k D, 1 ≤ D → cost k D ≤ D)
    (a : ℝ) (ha : 1 < a) (n k : ℕ) (D : ℝ) (hD : 0 ≤ D) :
    lowerErrorStep (fun i => 1/(p i : ℝ)) (primeKeep p)
      (upperError (fun i => 1/(p i : ℝ)) (primeKeep p) cost n) k D ≤
        (1+reciprocalPowerConstant a)^(2*n+1)*D^a := by
  have hh := refined_lowerError_le_rpow (fun i => 1/(p i : ℝ)) (primeKeep p)
    cost a 1 (reciprocalPowerConstant a) (by linarith) le_rfl (reciprocalPowerConstant_nonneg a)
      (fun i => by positivity) (reciprocal_power_sum_le p hmono.injective a ha)
      (primeKeep_levels p hp hmono) (fun k D hD => (hcost k D hD).trans (by
        simpa using rpow_le_rpow_of_exponent_le hD ha.le)) n k D hD
  simpa only [one_mul] using hh

#print axioms reciprocal_power_sum_le
#print axioms prime_refined_lowerError_le
end Erdos970.RecursiveSieve.Buchstab
