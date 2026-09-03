import Submission.BuchstabPrimeCost

/-! Depth-uniform power error estimates. Strictly decreasing prefix indices
allow the entire incurred error to be dominated by a finite Euler product.
This is a quantitative auxiliary result, not the quadratic Jacobsthal bound. -/
namespace Erdos970.RecursiveSieve.Buchstab
open Finset Real
set_option maxHeartbeats 0

noncomputable def orderedPowerProduct (q : ℕ → ℝ) (a : ℝ) (k : ℕ) : ℝ :=
  ∏ i ∈ range k, (1 + q i ^ a)

lemma orderedPowerProduct_ge_one (q : ℕ → ℝ) (a : ℝ)
    (hq : ∀ i, 0 ≤ q i) (k : ℕ) :
    1 ≤ orderedPowerProduct q a k := by
  unfold orderedPowerProduct
  apply Finset.one_le_prod
  intro i
  linarith [rpow_nonneg (hq i) a]

lemma orderedPowerProduct_first (q : ℕ → ℝ) (a : ℝ) (k : ℕ) :
    1 + ∑ i : Fin k, q i.val ^ a * orderedPowerProduct q a i.val =
      orderedPowerProduct q a k := by
  rw [Fin.sum_univ_eq_sum_range (fun i => q i ^ a * orderedPowerProduct q a i) k]
  induction k with
  | zero => simp [orderedPowerProduct]
  | succ k ih =>
    have hp : orderedPowerProduct q a (k+1) =
        orderedPowerProduct q a k * (1 + q k^a) := by
      simp only [orderedPowerProduct, prod_range_succ]
    rw [sum_range_succ, hp]
    linarith only [ih]

lemma orderedPowerProduct_le_exp (q : ℕ → ℝ) (a : ℝ) (k : ℕ)
    (hq : ∀ i, 0 ≤ q i) :
    orderedPowerProduct q a k ≤ exp (∑ i : Fin k, q i.val ^ a) := by
  rw [Fin.sum_univ_eq_sum_range (fun i => q i ^ a) k, exp_sum]
  unfold orderedPowerProduct
  apply prod_le_prod
  · intro i hi
    linarith [rpow_nonneg (hq i) a]
  · intro i hi
    linarith [add_one_le_exp (q i ^ a)]

/-- The prefix product absorbs one whole lower step, including its unit cost. -/
theorem lowerErrorStep_le_ordered_product (q : ℕ → ℝ)
    (keep : ℕ → ℝ → Prop) (E : ℕ → ℝ → ℝ) (a C : ℝ)
    (ha : 0 ≤ a) (hC : 1 ≤ C) (hq : ∀ i, 0 ≤ q i)
    (hkeep : ∀ k D, keep k D → 1 ≤ D ∧ ∀ i < k, 1 ≤ D*q i)
    (hE : ∀ k D, 1 ≤ D → E k D ≤ C*D^a*orderedPowerProduct q a k)
    (k : ℕ) (D : ℝ) (hD : 0 ≤ D) :
    lowerErrorStep q keep E k D ≤ C*D^a*orderedPowerProduct q a k := by
  classical
  have hDa : 0 ≤ D^a := rpow_nonneg hD a
  have hC0 : 0 ≤ C := by linarith
  unfold lowerErrorStep
  split_ifs with hk
  · obtain ⟨hD1, hchild⟩ := hkeep k D hk
    have hs : (∑ i : Fin k, E i.val (D*q i.val)) ≤
        C*D^a*(∑ i : Fin k, q i.val^a*orderedPowerProduct q a i.val) := by
      rw [mul_sum]
      apply sum_le_sum
      intro i hi
      have hh := hE i.val (D*q i.val) (hchild i.val i.isLt)
      rw [mul_rpow hD (hq i.val)] at hh
      convert hh using 1; ring
    have hunit : 1 ≤ C*D^a :=
      one_le_mul_of_one_le_of_one_le hC (one_le_rpow hD1 ha)
    calc
      _ ≤ C*D^a + C*D^a*(∑ i : Fin k, q i.val^a*orderedPowerProduct q a i.val) :=
        add_le_add hunit hs
      _ = C*D^a*(1 + ∑ i : Fin k, q i.val^a*orderedPowerProduct q a i.val) := by ring
      _ = _ := by rw [orderedPowerProduct_first]
  · exact mul_nonneg (mul_nonneg hC0 hDa)
      ((by norm_num : (0 : ℝ) ≤ 1).trans (orderedPowerProduct_ge_one q a hq k))

/-- Unlike the scalar prefix-sum bound, this bound is uniform in depth.
The maximum in the upper-error recurrence is retained verbatim. -/
theorem upperError_le_ordered_product (q : ℕ → ℝ)
    (keep : ℕ → ℝ → Prop) (cost : ℕ → ℝ → ℝ) (a C : ℝ)
    (ha : 0 ≤ a) (hC : 1 ≤ C) (hq : ∀ i, 0 ≤ q i)
    (hkeep : ∀ k D, keep k D → 1 ≤ D ∧ ∀ i < k, 1 ≤ D*q i)
    (hcost : ∀ k D, 1 ≤ D → cost k D ≤ C*D^a)
    (n k : ℕ) (D : ℝ) (hD : 1 ≤ D) :
    upperError q keep cost n k D ≤ C*D^a*orderedPowerProduct q a k := by
  have hC0 : 0 ≤ C := by linarith
  have hD0 : 0 ≤ D := by linarith
  induction n generalizing k D with
  | zero =>
    exact (hcost k D hD).trans (le_mul_of_one_le_right
      (mul_nonneg hC0 (rpow_nonneg hD0 a)) (orderedPowerProduct_ge_one q a hq k))
  | succ n ih =>
    change max (upperError q keep cost n k D)
      (1 + ∑ i : Fin k, lowerErrorStep q keep (upperError q keep cost n)
        i.val (D*q i.val)) ≤ _
    apply max_le (ih k D hD hD0)
    have hl := lowerErrorStep_le_ordered_product q keep (upperError q keep cost n)
      a C ha hC hq hkeep (fun j E hE => ih j E hE (by linarith))
    have hs : (∑ i : Fin k, lowerErrorStep q keep (upperError q keep cost n)
        i.val (D*q i.val)) ≤
        C*D^a*(∑ i : Fin k, q i.val^a*orderedPowerProduct q a i.val) := by
      rw [mul_sum]
      apply sum_le_sum
      intro i hi
      have hh := hl i.val (D*q i.val) (mul_nonneg hD0 (hq i.val))
      rw [mul_rpow hD0 (hq i.val)] at hh
      convert hh using 1; ring
    have hunit : 1 ≤ C*D^a :=
      one_le_mul_of_one_le_of_one_le hC (one_le_rpow hD ha)
    calc
      _ ≤ C*D^a + C*D^a*(∑ i : Fin k, q i.val^a*orderedPowerProduct q a i.val) :=
        add_le_add hunit hs
      _ = C*D^a*(1 + ∑ i : Fin k, q i.val^a*orderedPowerProduct q a i.val) := by ring
      _ = _ := by rw [orderedPowerProduct_first]

theorem refined_lowerError_le_ordered_product (q : ℕ → ℝ)
    (keep : ℕ → ℝ → Prop) (cost : ℕ → ℝ → ℝ) (a C : ℝ)
    (ha : 0 ≤ a) (hC : 1 ≤ C) (hq : ∀ i, 0 ≤ q i)
    (hkeep : ∀ k D, keep k D → 1 ≤ D ∧ ∀ i < k, 1 ≤ D*q i)
    (hcost : ∀ k D, 1 ≤ D → cost k D ≤ C*D^a)
    (n k : ℕ) (D : ℝ) (hD : 0 ≤ D) :
    lowerErrorStep q keep (upperError q keep cost n) k D ≤
      C*D^a*orderedPowerProduct q a k :=
  lowerErrorStep_le_ordered_product q keep _ a C ha hC hq hkeep
    (fun j E hE => upperError_le_ordered_product q keep cost a C ha hC hq hkeep hcost n j E hE)
    k D hD

/-- A summable family of marginal powers gives a constant independent of
both prefix length and refinement depth. -/
theorem refined_lowerError_le_depth_uniform (q : ℕ → ℝ)
    (keep : ℕ → ℝ → Prop) (cost : ℕ → ℝ → ℝ) (a C Z : ℝ)
    (ha : 0 ≤ a) (hC : 1 ≤ C) (hq : ∀ i, 0 ≤ q i)
    (hpow : ∀ k, (∑ i : Fin k, q i.val^a) ≤ Z)
    (hkeep : ∀ k D, keep k D → 1 ≤ D ∧ ∀ i < k, 1 ≤ D*q i)
    (hcost : ∀ k D, 1 ≤ D → cost k D ≤ C*D^a)
    (n k : ℕ) (D : ℝ) (hD : 0 ≤ D) :
    lowerErrorStep q keep (upperError q keep cost n) k D ≤ C*exp Z*D^a := by
  have hh := refined_lowerError_le_ordered_product q keep cost a C
    ha hC hq hkeep hcost n k D hD
  have hp := (orderedPowerProduct_le_exp q a k hq).trans (exp_le_exp.mpr (hpow k))
  have hm := mul_le_mul_of_nonneg_left hp
    (mul_nonneg (show 0 ≤ C by linarith) (rpow_nonneg hD a))
  exact hh.trans (by simpa only [mul_assoc, mul_left_comm, mul_comm] using hm)

/-- The old prime power estimate had an exponential dependence on depth.
Here the same hypotheses give a depth-independent bound. This still uses
an exponent strictly larger than one and is not a logarithmic cost saving. -/
theorem prime_refined_lowerError_le_depth_uniform
    (p : ℕ → ℕ) (hp : ∀ i, (p i).Prime) (hmono : StrictMono p)
    (cost : ℕ → ℝ → ℝ) (hcost : ∀ k D, 1 ≤ D → cost k D ≤ D)
    (a : ℝ) (ha : 1 < a) (n k : ℕ) (D : ℝ) (hD : 0 ≤ D) :
    lowerErrorStep (fun i => 1/(p i : ℝ)) (primeKeep p)
      (upperError (fun i => 1/(p i : ℝ)) (primeKeep p) cost n) k D ≤
        exp (reciprocalPowerConstant a)*D^a := by
  have hh := refined_lowerError_le_depth_uniform
    (fun i => 1/(p i : ℝ)) (primeKeep p) cost a 1 (reciprocalPowerConstant a)
    (by linarith) le_rfl (fun i => by positivity)
    (reciprocal_power_sum_le p hmono.injective a ha)
    (primeKeep_levels p hp hmono)
    (fun j E hE => (hcost j E hE).trans (by
      simpa using rpow_le_rpow_of_exponent_le hE ha.le)) n k D hD
  simpa only [one_mul] using hh

#print axioms refined_lowerError_le_ordered_product
#print axioms refined_lowerError_le_depth_uniform
#print axioms prime_refined_lowerError_le_depth_uniform
end Erdos970.RecursiveSieve.Buchstab
