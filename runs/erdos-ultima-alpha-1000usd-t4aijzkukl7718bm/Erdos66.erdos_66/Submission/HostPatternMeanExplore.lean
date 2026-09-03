import Submission.GeneralCentralTripleMeanExplore
import Submission.BoundaryPairPotentialExplore

/-! Boundary and triple-pattern mean bounds for probability profiles dominated
by 32 times the harmonic profile (allowing coefficient 1024 hosts). -/
namespace Erdos66HostPatternMean
open Filter Erdos66Fractional Erdos66BoundaryPairMean Erdos66BoundaryPairPotential
  Erdos66TripleIntersectionGeometry Erdos66TripleIntersectionMean Erdos66GeneralCentralTripleMean
  Erdos66BernoulliMatchingPolynomial Erdos66FiniteRepBernoulli
open scoped Classical Topology
set_option maxHeartbeats 2000000

noncomputable def hostCutoff (j : ℕ) : ℕ := cutoff (j+1024)
lemma hostCutoff_ge_two (j : ℕ) : 2 ≤ hostCutoff j := cutoff_ge_two _
lemma hostCutoff_ge_exp (j : ℕ) : 4096*Real.exp ((j:ℝ)+1) ≤ (hostCutoff j:ℝ) := by
  have he : (1024:ℝ) ≤ Real.exp 1024 := by linarith [Real.add_one_le_exp (1024:ℝ)]
  have hm := mul_le_mul_of_nonneg_left he (show 0 ≤ 4*Real.exp ((j:ℝ)+1) by positivity)
  have hc := cutoff_ge_exp (j+1024)
  change _ ≤ (hostCutoff j:ℝ) at hc
  push_cast at hc
  rw [show (j:ℝ)+1024+1=((j:ℝ)+1)+1024 by ring,Real.exp_add] at hc
  nlinarith only [hm,hc]

lemma boundary_mean_dom (p : ℕ → ℝ) (hp : ∀ i, 0 ≤ p i) (hdom : ∀ i, p i ≤ 32*profile i)
    (L d n : ℕ) :
    (∑ a∈boundaryPairs L d n, ∏ i∈pairCoords a, p i.val) ≤ 1024*boundaryMean d n := by
  calc
    _ ≤ ∑ a∈boundaryPairs L d n, 1024*(∏ i∈pairCoords a, profile i.val) := by
      apply Finset.sum_le_sum
      intro a ha
      have hne := (mem_boundaryPairs.mp ha).2.2.ne
      simp only [pairCoords,Finset.prod_pair hne]
      have hh := mul_le_mul (hdom a.1.val) (hdom a.2.val) (hp a.2.val) (mul_nonneg (by norm_num) (profile_nonneg a.1.val))
      nlinarith only [hh]
    _ = 1024*(∑ a∈boundaryPairs L d n, ∏ i∈pairCoords a, profile i.val) := (Finset.mul_sum _ _ _).symm
    _ ≤ 1024*boundaryMean d n := mul_le_mul_of_nonneg_left (boundary_pair_mean L d n) (by norm_num)

lemma triple_mean_dom (p : ℕ → ℝ) (hp : ∀ i, 0 ≤ p i) (hdom : ∀ i, p i ≤ 32*profile i)
    (L N n z : ℕ) :
    (∑ e∈triples L N n z, ∏ i∈coords e, p i.val) ≤ 32768*tripleMean L N n z := by
  calc
    _ ≤ ∑ e∈triples L N n z, 32768*(∏ i∈coords e, profile i.val) := by
      apply Finset.sum_le_sum
      intro e he
      rw [triple_monomial_mean he,triple_monomial_mean he]
      have h1 := mul_le_mul (hdom e.1.val) (hdom e.2.1.val) (hp e.2.1.val)
        (mul_nonneg (by norm_num) (profile_nonneg e.1.val))
      have h2 := mul_le_mul h1 (hdom e.2.2.val) (hp e.2.2.val)
        (mul_nonneg (mul_nonneg (by norm_num) (profile_nonneg e.1.val))
          (mul_nonneg (by norm_num) (profile_nonneg e.2.1.val)))
      nlinarith only [h2]
    _ = 32768*tripleMean L N n z := (Finset.mul_sum _ _ _).symm

lemma host_boundary_raw_mean (p : ℕ → ℝ) (hp : ∀ i, 0 ≤ p i) (hdom : ∀ i, p i ≤ 32*profile i)
    (L j n : ℕ) (hn : (hostCutoff j)^2 ≤ n) :
    matchingPoly (boundaryPairs L (hostCutoff j) n) pairCoords ((j:ℝ)+1) (fun i ↦ p i.val) ≤
      Real.exp 1*((n:ℝ)+1) := by
  have hm := (boundary_mean_dom p hp hdom L (hostCutoff j) n).trans
    (mul_le_mul_of_nonneg_left (boundaryMean_bound (hostCutoff j) n (hostCutoff_ge_two j) hn)
      (by norm_num : (0:ℝ) ≤ 1024))
  have hd : (0:ℝ) < hostCutoff j := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0<2) (hostCutoff_ge_two j))
  have hfrac : Real.exp ((j:ℝ)+1)*(4096/(hostCutoff j:ℝ)) ≤ 1 := by
    rw [←mul_div_assoc]
    apply (div_le_one hd).mpr
    nlinarith only [hostCutoff_ge_exp j]
  have hsum : 0 ≤ ∑ a∈boundaryPairs L (hostCutoff j) n, ∏ i∈pairCoords a, p i.val :=
    Finset.sum_nonneg (fun a _ ↦ Finset.prod_nonneg (fun i _ ↦ hp i.val))
  have he0 : 0 ≤ ell n := (by norm_num : (0:ℝ) ≤ 1).trans (ell_one_le n)
  have h1 := mul_le_mul_of_nonneg_right
    (show Real.exp ((j:ℝ)+1)-1 ≤ Real.exp ((j:ℝ)+1) by linarith) hsum
  have h2 := mul_le_mul_of_nonneg_left hm (Real.exp_pos ((j:ℝ)+1)).le
  have h3 := mul_le_mul_of_nonneg_right hfrac he0
  have hexp : (Real.exp ((j:ℝ)+1)-1)*
      (∑ a∈boundaryPairs L (hostCutoff j) n, ∏ i∈pairCoords a, p i.val) ≤ ell n := by
    have heq : 1024*(4/(hostCutoff j:ℝ)*ell n)=(4096/(hostCutoff j:ℝ))*ell n := by ring
    rw [heq] at h2
    nlinarith only [h1,h2,h3]
  have hpoly := (matchingPoly_upper (boundaryPairs L (hostCutoff j) n) pairCoords ((j:ℝ)+1)
    (by positivity) (fun i ↦ p i.val) (fun i ↦ hp i.val)).trans (Real.exp_le_exp.mpr hexp)
  apply hpoly.trans_eq
  rw [ell,Real.exp_add,Real.exp_log (by positivity)]

lemma eventually_host_triple_mean (p : ℕ → ℝ) (hp : ∀ i, 0 ≤ p i) (hdom : ∀ i, p i ≤ 32*profile i)
    (C : ℕ) : ∀ᶠ N : ℕ in atTop, ∀ L n z, n ≤ C*N →
      matchingPoly (triples L N n z) coords (tilt N) (fun i ↦ p i.val) ≤ Real.exp 1 := by
  have hlim := (comparable_tilted_mean_limit C).const_mul 32768
  simp only [mul_zero] at hlim
  filter_upwards [hlim.eventually_le_const (show (0:ℝ)<1 by norm_num)] with N hN
  intro L n z hn
  have hm := (triple_mean_dom p hp hdom L N n z).trans
    (mul_le_mul_of_nonneg_left (tripleMean_comparable L C N n z hn) (by norm_num : (0:ℝ) ≤ 32768))
  have hsum : 0 ≤ ∑ e∈triples L N n z, ∏ i∈coords e, p i.val :=
    Finset.sum_nonneg (fun e _ ↦ Finset.prod_nonneg (fun i _ ↦ hp i.val))
  have h1 := mul_le_mul_of_nonneg_right (show Real.exp (tilt N)-1 ≤ Real.exp (tilt N) by linarith) hsum
  have h2 := mul_le_mul_of_nonneg_left hm (Real.exp_pos (tilt N)).le
  have he : (Real.exp (tilt N)-1)*(∑ e∈triples L N n z, ∏ i∈coords e, p i.val) ≤ 1 := by
    nlinarith only [hN,h1,h2]
  exact (matchingPoly_upper (triples L N n z) coords (tilt N) (tilt_nonneg N)
    (fun i ↦ p i.val) (fun i ↦ hp i.val)).trans (Real.exp_le_exp.mpr he)

end Erdos66HostPatternMean
