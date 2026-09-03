import Submission.BoundaryPairCountsExplore
import Submission.DisjointMatchingPolynomialExplore

/-! Summable positive penalties enforce arbitrarily small boundary counts,
by choosing a sufficiently small fixed relative boundary window. -/
namespace Erdos66BoundaryPairPotential
open Erdos66BoundaryPairMean Erdos66BoundaryPairCounts Erdos66TripleIntersectionMean
  Erdos66DisjointMatchingPolynomial Erdos66BernoulliMatchingPolynomial
  Erdos66FiniteBernoulli Erdos66FiniteRepBernoulli Erdos66Fractional
open scoped Classical
set_option maxHeartbeats 1600000

noncomputable def cutoff (j : ℕ) : ℕ := max 2 ⌈4*Real.exp ((j:ℝ)+1)⌉₊
noncomputable def boundaryWeight (n : ℕ) : ℝ := Real.exp (-3*ell n)
noncomputable def boundaryTail (n : ℕ) : ℝ := Real.exp (-2)/((n:ℝ)+1)^2

lemma cutoff_ge_two (j : ℕ) : 2 ≤ cutoff j := le_max_left _ _
lemma cutoff_ge_exp (j : ℕ) : 4*Real.exp ((j:ℝ)+1) ≤ (cutoff j:ℝ) := by
  unfold cutoff
  exact (Nat.le_ceil _).trans (by exact_mod_cast le_max_right 2 ⌈4*Real.exp ((j:ℝ)+1)⌉₊)
lemma boundaryWeight_pos (n : ℕ) : 0 < boundaryWeight n := Real.exp_pos _

lemma boundaryTail_summable : Summable boundaryTail := by
  have hh := (Real.summable_one_div_nat_add_rpow 1 (2:ℕ)).mpr (by norm_num)
  have hh' := hh.mul_left (Real.exp (-2))
  simpa only [boundaryTail,Real.rpow_natCast,abs_of_nonneg (by positivity : (0:ℝ) ≤ (↑(_:ℕ):ℝ)+1),
    mul_one_div] using hh'

lemma boundary_raw_mean (L j n : ℕ) (hn : (cutoff j)^2 ≤ n) :
    matchingPoly (boundaryPairs L (cutoff j) n) pairCoords ((j:ℝ)+1)
      (fun i ↦ profile i.val) ≤ Real.exp 1*((n:ℝ)+1) := by
  have hm := (boundary_pair_mean L (cutoff j) n).trans
    (boundaryMean_bound (cutoff j) n (cutoff_ge_two j) hn)
  have ht : 0 ≤ (j:ℝ)+1 := by positivity
  have hd : (0:ℝ) < cutoff j := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0<2) (cutoff_ge_two j))
  have hfrac : Real.exp ((j:ℝ)+1)*(4/(cutoff j:ℝ)) ≤ 1 := by
    rw [←mul_div_assoc]
    apply (div_le_one hd).mpr
    nlinarith only [cutoff_ge_exp j]
  have hsum : 0 ≤ ∑ a∈boundaryPairs L (cutoff j) n, ∏ i∈pairCoords a, profile i.val :=
    Finset.sum_nonneg (fun a _ ↦ Finset.prod_nonneg (fun i _ ↦ profile_nonneg i.val))
  have he0 : 0 ≤ ell n := (by norm_num : (0:ℝ) ≤ 1).trans (ell_one_le n)
  have h1 := mul_le_mul_of_nonneg_right
    (show Real.exp ((j:ℝ)+1)-1 ≤ Real.exp ((j:ℝ)+1) by linarith) hsum
  have h2 := mul_le_mul_of_nonneg_left hm (Real.exp_pos ((j:ℝ)+1)).le
  have h3 := mul_le_mul_of_nonneg_right hfrac he0
  have hexp : (Real.exp ((j:ℝ)+1)-1)*
      (∑ a∈boundaryPairs L (cutoff j) n, ∏ i∈pairCoords a, profile i.val) ≤ ell n := by
    nlinarith only [h1,h2,h3]
  have hpoly := (matchingPoly_upper (boundaryPairs L (cutoff j) n) pairCoords ((j:ℝ)+1) ht
    (fun i ↦ profile i.val) (fun i ↦ profile_nonneg i.val)).trans (Real.exp_le_exp.mpr hexp)
  apply hpoly.trans_eq
  rw [ell,Real.exp_add,Real.exp_log (by positivity)]

lemma weighted_boundary_mean (L j n : ℕ) (hn : (cutoff j)^2 ≤ n) :
    boundaryWeight n*matchingPoly (boundaryPairs L (cutoff j) n) pairCoords ((j:ℝ)+1)
      (fun i ↦ profile i.val) ≤ boundaryTail n := by
  have hm := (boundary_pair_mean L (cutoff j) n).trans
    (boundaryMean_bound (cutoff j) n (cutoff_ge_two j) hn)
  have ht : 0 ≤ (j:ℝ)+1 := by positivity
  have hd : (0:ℝ) < cutoff j := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0<2) (cutoff_ge_two j))
  have hfrac : Real.exp ((j:ℝ)+1)*(4/(cutoff j:ℝ)) ≤ 1 := by
    rw [←mul_div_assoc]
    apply (div_le_one hd).mpr
    nlinarith only [cutoff_ge_exp j]
  have hsum : 0 ≤ ∑ a∈boundaryPairs L (cutoff j) n, ∏ i∈pairCoords a, profile i.val :=
    Finset.sum_nonneg (fun a _ ↦ Finset.prod_nonneg (fun i _ ↦ profile_nonneg i.val))
  have he0 : 0 ≤ ell n := (by norm_num : (0:ℝ) ≤ 1).trans (ell_one_le n)
  have h1 := mul_le_mul_of_nonneg_right
    (show Real.exp ((j:ℝ)+1)-1 ≤ Real.exp ((j:ℝ)+1) by linarith) hsum
  have h2 := mul_le_mul_of_nonneg_left hm (Real.exp_pos ((j:ℝ)+1)).le
  have h3 := mul_le_mul_of_nonneg_right hfrac he0
  have hexp : (Real.exp ((j:ℝ)+1)-1)*
      (∑ a∈boundaryPairs L (cutoff j) n, ∏ i∈pairCoords a, profile i.val) ≤ ell n := by
    nlinarith only [h1,h2,h3]
  have hpoly := (matchingPoly_upper (boundaryPairs L (cutoff j) n) pairCoords ((j:ℝ)+1) ht
    (fun i ↦ profile i.val) (fun i ↦ profile_nonneg i.val)).trans (Real.exp_le_exp.mpr hexp)
  apply (mul_le_mul_of_nonneg_left hpoly (boundaryWeight_pos n).le).trans_eq
  rw [boundaryWeight,←Real.exp_add,show -3*ell n+ell n = -2*ell n by ring]
  dsimp only [ell,boundaryTail]
  rw [show -2*(1+Real.log ((n:ℝ)+1)) = -2-2*Real.log ((n:ℝ)+1) by ring,Real.exp_sub]
  congr 1
  simpa only [Nat.cast_ofNat,Real.exp_log (by positivity : (0:ℝ) < (n:ℝ)+1)] using
    Real.exp_nat_mul (Real.log ((n:ℝ)+1)) 2

lemma weighted_boundary_bounds_count (L j n : ℕ) (ω : Fin (L+1) → Bool)
    (hcost : boundaryWeight n*matchingPoly (boundaryPairs L (cutoff j) n) pairCoords ((j:ℝ)+1)
      (fun i ↦ bit (ω i)) < 1) :
    ((j:ℝ)+1)*((boundary (selected L ω) (cutoff j) n).card:ℝ) ≤ 3*ell n := by
  rw [matchingPoly_binary_disjoint _ _ (boundaryPairs_disjoint L (cutoff j) n),
    selected_boundary_card L (cutoff j) n (cutoff_ge_two j),boundaryWeight,←Real.exp_add,
    Real.exp_lt_one_iff] at hcost
  linarith

end Erdos66BoundaryPairPotential
