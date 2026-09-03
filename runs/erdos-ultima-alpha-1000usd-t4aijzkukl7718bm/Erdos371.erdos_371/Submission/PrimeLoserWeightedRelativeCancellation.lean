import Submission.PrimeLoserWeightedCollisionMass

/-! A relative cancellation criterion at the natural quadratic scale of the
prime-weighted collision mass. The asymptotic symmetry is not proved. -/
namespace Erdos371
open Finset Filter
open scoped Topology

noncomputable def primeLoserWeightedOppositeRatio (N : ℕ) : ℝ :=
  primeLoserWeightedOppositeMass N / primeLoserWeightedCollisionMass N

lemma weighted_collision_relative_identity (N : ℕ)
    (hQ : primeLoserWeightedCollisionMass N ≠ 0) :
    primeLoserPrimeWeightedCollisions N / primeLoserWeightedCollisionMass N =
      1-2*primeLoserWeightedOppositeRatio N := by
  rw [primeLoserPrimeWeightedCollisions_eq_mass_sub_twice_opposite,
    primeLoserWeightedOppositeRatio]
  field_simp

lemma weighted_collision_normalized_identity (N : ℕ)
    (hQ : primeLoserWeightedCollisionMass N ≠ 0) :
    primeLoserPrimeWeightedCollisions N/(N : ℝ)^2 =
      (primeLoserWeightedCollisionMass N/(N : ℝ)^2)*
        (1-2*primeLoserWeightedOppositeRatio N) := by
  rw [← weighted_collision_relative_identity N hQ]
  field_simp

lemma weighted_collision_relative_eventually_bounds :
    ∀ᶠ N : ℕ in atTop,
      ‖primeLoserPrimeWeightedCollisions N/(N : ℝ)^2‖ ≤
        2*‖1-2*primeLoserWeightedOppositeRatio N‖ ∧
      ‖1-2*primeLoserWeightedOppositeRatio N‖ ≤
        3200*‖primeLoserPrimeWeightedCollisions N/(N : ℝ)^2‖ := by
  filter_upwards [primeLoserWeightedCollisionMass_eventually_lower,
    eventually_gt_atTop (0 : ℕ)] with N hlow hN
  have hN0 : (0 : ℝ)<N := by exact_mod_cast hN
  have hN2 : 0<(N : ℝ)^2 := sq_pos_of_pos hN0
  have hQ : 0<primeLoserWeightedCollisionMass N := lt_of_lt_of_le (by positivity) hlow
  have hupper : primeLoserWeightedCollisionMass N/(N : ℝ)^2 ≤ 2 :=
    (div_le_iff₀ hN2).mpr (primeLoserWeightedCollisionMass_bound N)
  have hnorm : ‖primeLoserWeightedCollisionMass N/(N : ℝ)^2‖ =
      primeLoserWeightedCollisionMass N/(N : ℝ)^2 := Real.norm_of_nonneg (by positivity)
  constructor
  · rw [weighted_collision_normalized_identity N hQ.ne',norm_mul,hnorm]
    exact mul_le_mul_of_nonneg_right hupper (norm_nonneg _)
  · rw [← weighted_collision_relative_identity N hQ.ne',norm_div,norm_div,
      Real.norm_of_nonneg hQ.le,Real.norm_of_nonneg hN2.le,← mul_div_assoc]
    apply (div_le_div_iff₀ hQ hN2).mpr
    have hh := mul_le_mul_of_nonneg_left hlow (norm_nonneg (primeLoserPrimeWeightedCollisions N))
    nlinarith

/-- At this weighted scale, ordinary relative cancellation is equivalent to
the signed o(N^2) criterion; no additional convergence rate is needed. -/
theorem weightedSignedCollisions_tendsto_iff_opposite_half :
    Tendsto (fun N : ℕ => primeLoserPrimeWeightedCollisions N/(N : ℝ)^2)
      atTop (nhds 0) ↔
    Tendsto primeLoserWeightedOppositeRatio atTop (nhds (1/2)) := by
  constructor
  · intro h
    have ht := h.norm.const_mul 3200
    simp only [norm_zero,mul_zero] at ht
    have he : Tendsto (fun N : ℕ => 1-2*primeLoserWeightedOppositeRatio N)
        atTop (nhds 0) := by
      apply squeeze_zero_norm' _ ht
      filter_upwards [weighted_collision_relative_eventually_bounds] with N hN
      exact hN.2
    have hh := (he.const_sub 1).div_const 2
    norm_num only at hh
    convert hh using 1
    ext N
    ring
  · intro h
    have ht := (h.const_mul 2).const_sub 1
    norm_num only at ht
    have hn := ht.norm.const_mul 2
    simp only [norm_zero,mul_zero] at hn
    apply squeeze_zero_norm' _ hn
    filter_upwards [weighted_collision_relative_eventually_bounds] with N hN
    exact hN.1

/-- Equivalent formulation of the sufficient prime-weighted energy limit. -/
theorem primeWeightedEnergy_tendsto_iff_weighted_opposite_half :
    Tendsto (fun N : ℕ => primeWinnerPrimeWeightedEnergy N/(N : ℝ)^2)
      atTop (nhds 0) ↔
    Tendsto primeLoserWeightedOppositeRatio atTop (nhds (1/2)) :=
  primeWeightedEnergy_tendsto_iff_weightedSignedCollisions.trans
    weightedSignedCollisions_tendsto_iff_opposite_half

/-- A precise relative-symmetry hypothesis that would prove the ORIGINAL
conjecture. Neither the hypothesis nor the conjecture is established here. -/
theorem density_of_primeWeightedOppositeCollision_half
    (h : Tendsto primeLoserWeightedOppositeRatio atTop (nhds (1/2))) :
    {n | Nat.maxPrimeFac (n+1)>Nat.maxPrimeFac n}.HasDensity (1/2) :=
  density_of_primeWeightedSignedCollisions (weightedSignedCollisions_tendsto_iff_opposite_half.mpr h)

/-- Positivity of the weighted loser energy gives the easy direction:
the opposite-sign fraction is asymptotically at most one half. -/
theorem primeLoserWeightedOppositeRatio_eventually_upper (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ N : ℕ in atTop, primeLoserWeightedOppositeRatio N ≤ 1/2+ε := by
  have hdiag := primeLoserPrimeWeightedDiagonal_tendsto_zero.eventually_lt_const
    (show 0<ε/1600 by positivity)
  filter_upwards [hdiag,primeLoserWeightedCollisionMass_eventually_lower,
    eventually_gt_atTop (0 : ℕ)] with N hd hlow hN
  have hN0 : (0 : ℝ)<N := by exact_mod_cast hN
  have hN2 : 0<(N : ℝ)^2 := sq_pos_of_pos hN0
  have hQ : 0<primeLoserWeightedCollisionMass N := lt_of_lt_of_le (by positivity) hlow
  have hE : 0≤primeLoserPrimeWeightedEnergy N := by
    unfold primeLoserPrimeWeightedEnergy
    positivity
  rw [primeLoserPrimeWeightedEnergy_formula,
    primeLoserPrimeWeightedCollisions_eq_mass_sub_twice_opposite] at hE
  have hd' := (div_lt_iff₀ hN2).mp hd
  have hm := mul_le_mul_of_nonneg_left hlow hε.le
  unfold primeLoserWeightedOppositeRatio
  apply (div_le_iff₀ hQ).mpr
  nlinarith

/-- Only the reverse one-sided relative bound remains to imply the target.
It is not supplied by positivity or by the unsigned collision bounds. -/
theorem density_of_weightedOpposite_liminf
    (h : ∀ ε : ℝ, 0<ε → ∀ᶠ N : ℕ in atTop,
      1/2-ε ≤ primeLoserWeightedOppositeRatio N) :
    {n | Nat.maxPrimeFac (n+1)>Nat.maxPrimeFac n}.HasDensity (1/2) := by
  apply density_of_primeWeightedOppositeCollision_half
  apply tendsto_order.mpr
  constructor
  · intro a ha
    have he : 0<((1/2 : ℝ)-a)/2 := by linarith
    filter_upwards [h (((1/2 : ℝ)-a)/2) he] with N hN
    linarith
  · intro a ha
    have he : 0<(a-(1/2 : ℝ))/2 := by linarith
    filter_upwards [primeLoserWeightedOppositeRatio_eventually_upper ((a-(1/2 : ℝ))/2) he] with N hN
    linarith

#print axioms weighted_collision_relative_eventually_bounds
#print axioms primeWeightedEnergy_tendsto_iff_weighted_opposite_half
#print axioms density_of_primeWeightedOppositeCollision_half
#print axioms primeLoserWeightedOppositeRatio_eventually_upper
#print axioms density_of_weightedOpposite_liminf
end Erdos371
