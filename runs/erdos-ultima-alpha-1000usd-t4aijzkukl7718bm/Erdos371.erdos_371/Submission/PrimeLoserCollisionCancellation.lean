import Submission.PrimeLoserSignedCollisions

/-! The amount of signed cancellation required in a range with superlinear
unsigned collisions. The equivalence here gives no cancellation rate. -/
namespace Erdos371
open Finset Filter FiniteSieve
open scoped Topology

lemma primeLoserEndpointCorrection_le_nine_mul (B N : ℕ) (hN : 0<N) :
    ‖primeLoserEndpointCorrection B N‖ ≤ 9*(N : ℝ) := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hh : 4*(N : ℝ)/(B+1) ≤ 4*N := by
    apply div_le_self (by positivity)
    have := Nat.cast_nonneg (α := ℝ) B
    linarith
  exact (primeLoserEndpointCorrection_bound B N).trans (by linarith)

lemma collision_energy_balance_error (B N : ℕ) (hN : 0<N)
    (hQ : 0<(primeLoserCollisions B N).card) :
    ‖primeWinnerEnergyAbove B N / (primeLoserCollisions B N).card +
      2*((primeLoserOppositeCollisions B N).card : ℝ)/(primeLoserCollisions B N).card - 1‖ ≤
        10*(N : ℝ)/(primeLoserCollisions B N).card := by
  have hQ0 : (0 : ℝ)<(primeLoserCollisions B N).card := by exact_mod_cast hQ
  have he := primeWinnerEnergyAbove_signed_collision_formula B N
  rw [primeLoserSignedCollisions_eq_card_sub_twice_opposite] at he
  have hid : primeWinnerEnergyAbove B N / (primeLoserCollisions B N).card +
      2*((primeLoserOppositeCollisions B N).card : ℝ)/(primeLoserCollisions B N).card - 1 =
      ((bothAboveSet B N).card + primeLoserEndpointCorrection B N)/
        (primeLoserCollisions B N).card := by
    rw [he]
    field_simp
    ring
  rw [hid, norm_div,Real.norm_natCast]
  apply div_le_div_of_nonneg_right _ hQ0.le
  have hm : ((bothAboveSet B N).card : ℝ) ≤ N := by
    exact_mod_cast (card_filter_le (range N) _).trans_eq (card_range N)
  have hh := norm_add_le ((bothAboveSet B N).card : ℝ) (primeLoserEndpointCorrection B N)
  rw [Real.norm_natCast] at hh
  have hend := primeLoserEndpointCorrection_le_nine_mul B N hN
  linarith

/-- When Q/N diverges, the energy fraction plus twice the fraction of
opposite-sign collisions tends to one. This is an identity, not an estimate
that the energy fraction vanishes. -/
theorem collision_energy_balance_tendsto (B : ℕ → ℕ)
    (hQ : Tendsto (fun N : ℕ => ((primeLoserCollisions (B N) N).card : ℝ)/N)
      atTop atTop) :
    Tendsto (fun N : ℕ =>
      primeWinnerEnergyAbove (B N) N/(primeLoserCollisions (B N) N).card +
      2*((primeLoserOppositeCollisions (B N) N).card : ℝ)/
        (primeLoserCollisions (B N) N).card) atTop (nhds 1) := by
  have hrec : Tendsto (fun N : ℕ => (N : ℝ)/(primeLoserCollisions (B N) N).card)
      atTop (nhds 0) := by
    have hh := hQ.inv_tendsto_atTop
    change Tendsto (fun N : ℕ =>
      (((primeLoserCollisions (B N) N).card : ℝ)/N)⁻¹) atTop (nhds 0) at hh
    simpa only [inv_div] using hh
  have herr : Tendsto (fun N : ℕ =>
      primeWinnerEnergyAbove (B N) N/(primeLoserCollisions (B N) N).card +
      2*((primeLoserOppositeCollisions (B N) N).card : ℝ)/
        (primeLoserCollisions (B N) N).card - 1) atTop (nhds 0) := by
    have hsmall := hrec.const_mul 10
    simp only [mul_zero,← mul_div_assoc] at hsmall
    apply squeeze_zero_norm' _ hsmall
    filter_upwards [eventually_gt_atTop (0 : ℕ),hQ.eventually_gt_atTop 0] with N hN hQN
    have hQ0 : 0<(primeLoserCollisions (B N) N).card := by
      have hh := (div_pos_iff.mp hQN)
      have hcard := Nat.cast_nonneg (α := ℝ) (primeLoserCollisions (B N) N).card
      have hpos : (0 : ℝ)<(primeLoserCollisions (B N) N).card := by rcases hh with h | h <;> linarith
      exact_mod_cast hpos
    exact collision_energy_balance_error (B N) N hN hQ0
  convert herr.add_const 1 using 1 <;> simp

/-- Half of the unsigned collisions having opposite signs is equivalent to
energy being o(Q), not to the much stronger estimate energy=O(N). -/
theorem collision_half_iff_energy_small_relative_to_collisions (B : ℕ → ℕ)
    (hQ : Tendsto (fun N : ℕ => ((primeLoserCollisions (B N) N).card : ℝ)/N)
      atTop atTop) :
    Tendsto (fun N : ℕ => ((primeLoserOppositeCollisions (B N) N).card : ℝ)/
      (primeLoserCollisions (B N) N).card) atTop (nhds (1/2)) ↔
    Tendsto (fun N : ℕ => primeWinnerEnergyAbove (B N) N/
      (primeLoserCollisions (B N) N).card) atTop (nhds 0) := by
  have ht := collision_energy_balance_tendsto B hQ
  constructor
  · intro h
    have hh := ht.sub (h.const_mul 2)
    norm_num only at hh
    convert hh using 1
    ext N
    ring
  · intro h
    have hh := (ht.sub h).div_const 2
    norm_num only at hh
    convert hh using 1
    ext N
    ring

/-- Any eventual linear energy bound would force asymptotically half of
these superlinearly many collisions to have opposite signs. -/
theorem collision_half_of_linear_energy (B : ℕ → ℕ) (C : ℝ)
    (hQ : Tendsto (fun N : ℕ => ((primeLoserCollisions (B N) N).card : ℝ)/N)
      atTop atTop)
    (hE : ∀ᶠ N : ℕ in atTop, primeWinnerEnergyAbove (B N) N ≤ C*N) :
    Tendsto (fun N : ℕ => ((primeLoserOppositeCollisions (B N) N).card : ℝ)/
      (primeLoserCollisions (B N) N).card) atTop (nhds (1/2)) := by
  apply (collision_half_iff_energy_small_relative_to_collisions B hQ).mpr
  have hrec : Tendsto (fun N : ℕ => (N : ℝ)/(primeLoserCollisions (B N) N).card)
      atTop (nhds 0) := by
    have hh := hQ.inv_tendsto_atTop
    change Tendsto (fun N : ℕ =>
      (((primeLoserCollisions (B N) N).card : ℝ)/N)⁻¹) atTop (nhds 0) at hh
    simpa only [inv_div] using hh
  have ht := hrec.const_mul C
  simp only [mul_zero,← mul_div_assoc] at ht
  apply squeeze_zero' _ _ ht
  · exact Eventually.of_forall fun N => by unfold primeWinnerEnergyAbove; positivity
  · filter_upwards [hE] with N hEN
    exact div_le_div_of_nonneg_right hEN (Nat.cast_nonneg _)

/-- Concrete specialization to the previously verified interior collision
obstruction. Its linear-energy hypothesis is still unproved. -/
theorem upperHalf_collision_half_of_linear_energy (C : ℝ)
    (hE : ∀ᶠ N : ℕ in atTop,
      primeWinnerEnergyAbove (ceilPowerCutoff (21/40) N) N ≤ C*N) :
    Tendsto (fun N : ℕ =>
      ((primeLoserOppositeCollisions (ceilPowerCutoff (21/40) N) N).card : ℝ)/
        (primeLoserCollisions (ceilPowerCutoff (21/40) N) N).card)
      atTop (nhds (1/2)) :=
  collision_half_of_linear_energy _ C
    primeLoserCollisions_upperHalf_ratio_tendsto_atTop hE

#print axioms collision_energy_balance_tendsto
#print axioms collision_half_iff_energy_small_relative_to_collisions
#print axioms upperHalf_collision_half_of_linear_energy
end Erdos371
