import Submission.ParametricWidePools

/-!
# Power-saving distribution for the parametric wide families

The three conductor groups are treated separately. All parameters are
fixed before the scale variable tends to infinity.
-/
open Nat Finset Filter
open scoped Classical BigOperators Topology
namespace Erdos821
open AnalyticSieve HigherDivisors
set_option maxHeartbeats 3000000

def widePairLiftConstant (a : ℕ) : ℕ := 8*64*widePairScale a*64*(2*a+4)
def widePairErrorConstant (a : ℕ) : ℕ :=
  2*(130*(a+3))*wideMeanConstant (widePairScale a)+wideMeanConstant (widePairScale a)+widePairLiftConstant a

lemma widePair_pool_primitive_bounds (a m : ℕ) (ha : 21 ≤ a) :
    let E : ℝ := (wideMeanConstant (widePairScale a) : ℝ)*((m : ℝ)+1)^5*
      (2 : ℝ)^((64*widePairScale a-1)*m)
    primitivePoolMean (widePairLeft a m) (independentN (widePairScale a) m) ≤ E ∧
    primitivePoolMean (widePairRight a m) (independentN (widePairScale a) m) ≤ E ∧
    primitivePoolMean (widePairPool a m) (independentN (widePairScale a) m) ≤ E := by
  dsimp only
  have hleft := wide_primitive_mean_bound (widePairLeft a m) a (a+2) (widePairScale a) m
    (by omega) (by dsimp [widePairScale]; omega) (by dsimp [widePairScale]; omega)
    (by dsimp [widePairScale]; omega) (by dsimp [widePairScale]; omega)
    (fun p hp => by simpa only [independentN,progressionScaleN,mul_assoc] using
      widePairPools_bounds a m p (Or.inl hp))
  have hright := wide_primitive_mean_bound (widePairRight a m) a (a+2) (widePairScale a) m
    (by omega) (by dsimp [widePairScale]; omega) (by dsimp [widePairScale]; omega)
    (by dsimp [widePairScale]; omega) (by dsimp [widePairScale]; omega)
    (fun p hp => by simpa only [independentN,progressionScaleN,mul_assoc] using
      widePairPools_bounds a m p (Or.inr hp))
  have hpair := wide_primitive_mean_bound (widePairPool a m) (2*a) (2*a+4) (widePairScale a) m
    (by omega) (by dsimp [widePairScale]; omega) (by dsimp [widePairScale]; omega)
    (by dsimp [widePairScale]; omega) (by dsimp [widePairScale]; omega)
    (fun d hd => by simpa only [independentN,progressionScaleN,mul_assoc] using
      widePairPool_bounds a m d hd)
  simp only [independentN,progressionScaleN,mul_assoc] at hleft hright hpair ⊢
  exact ⟨hleft,hright,hpair⟩

lemma widePair_product_lift_bound (a m : ℕ) :
    8*((widePairPool a m).card : ℝ)*(Nat.log 2 (independentN (widePairScale a) m) : ℝ)*
      Real.log (independentN (2*a+4) m) ≤
      (widePairLiftConstant a : ℝ)*((m : ℝ)+1)^6*(2 : ℝ)^((64*widePairScale a-1)*m) := by
  have hc : ((widePairPool a m).card : ℝ) ≤ (2 : ℝ)^((64*widePairScale a-1)*m) := by
    apply (show ((widePairPool a m).card : ℝ) ≤ independentN (2*a+4) m by
      exact_mod_cast widePairPool_card_le a m).trans
    simp only [independentN,Nat.cast_pow,Nat.cast_ofNat]
    apply pow_le_pow_right₀ (by norm_num)
    exact Nat.mul_le_mul_right m (by dsimp [widePairScale]; omega)
  have hlog : Real.log (independentN (2*a+4) m : ℝ) ≤ 64*((2*a+4 : ℕ) : ℝ)*m := by
    simpa only [independentN,Nat.cast_mul,Nat.cast_ofNat] using log_two_pow_le (64*(2*a+4)*m)
  have hm0 : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
  have hz : 1 ≤ (m : ℝ)+1 := by linarith
  have hm26 : (m : ℝ)^2 ≤ ((m : ℝ)+1)^6 :=
    (pow_le_pow_left₀ hm0 (by linarith) 2).trans (pow_le_pow_right₀ hz (by decide))
  have hlogNat : (Nat.log 2 (independentN (widePairScale a) m) : ℝ) =
      64*(widePairScale a : ℝ)*m := by
    simp only [independentN,Nat.log_pow (by decide : 1<2),Nat.cast_mul,Nat.cast_ofNat]
  rw [hlogNat]
  calc
    _ ≤ 8*(2 : ℝ)^((64*widePairScale a-1)*m)*(64*(widePairScale a : ℝ)*m)*
        (64*((2*a+4 : ℕ) : ℝ)*m) := by gcongr
    _ = (widePairLiftConstant a : ℝ)*(m : ℝ)^2*(2 : ℝ)^((64*widePairScale a-1)*m) := by
      simp only [widePairLiftConstant,Nat.cast_mul,Nat.cast_ofNat]
      ring
    _ ≤ _ := by gcongr

lemma widePair_composite_error_bound (a m : ℕ) (ha : 21 ≤ a) :
    (∑ d ∈ widePairPool a m, compositeProgressionError d (independentN (widePairScale a) m)) ≤
      (widePairErrorConstant a : ℝ)*((m : ℝ)+1)^6*(2 : ℝ)^((64*widePairScale a-1)*m) := by
  let z : ℝ := (m : ℝ)+1
  let F : ℝ := (2 : ℝ)^((64*widePairScale a-1)*m)
  let C : ℝ := wideMeanConstant (widePairScale a)
  let W : ℝ := 130*((a : ℝ)+3)
  have hz : 1 ≤ z := by dsimp [z]; linarith [Nat.cast_nonneg (α := ℝ) m]
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hC : 0 ≤ C := Nat.cast_nonneg _
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hm := widePair_pool_primitive_bounds a m ha
  change primitivePoolMean (widePairLeft a m) _ ≤ C*z^5*F ∧
    primitivePoolMean (widePairRight a m) _ ≤ C*z^5*F ∧
      primitivePoolMean (widePairPool a m) _ ≤ C*z^5*F at hm
  have hleft : poolTotientMass (widePairLeft a m) ≤ W*z := by
    apply (widePrimePool_mass_upper a (a+1) m).trans
    dsimp [W,z]
    push_cast
    nlinarith [Nat.cast_nonneg (α := ℝ) a,Nat.cast_nonneg (α := ℝ) m]
  have hright : poolTotientMass (widePairRight a m) ≤ W*z := by
    simpa only [widePairRight,W,z,Nat.cast_add,Nat.cast_ofNat,add_assoc,
      show (2 : ℝ)+1=3 by norm_num] using widePrimePool_mass_upper (a+1) (a+2) m
  have herror := pair_composite_error_le _ _ (widePairLeft_prime a m) (widePairRight_prime a m)
    (widePairPools_disjoint a m) (independentN (widePairScale a) m) (independentN (2*a+4) m)
    (fun d hd => (widePairPool_bounds a m d hd).2.2)
  change (∑ d ∈ widePairPool a m, compositeProgressionError d (independentN (widePairScale a) m)) ≤ _ at herror
  change _ ≤ poolTotientMass (widePairRight a m)*primitivePoolMean (widePairLeft a m) _+
    poolTotientMass (widePairLeft a m)*primitivePoolMean (widePairRight a m) _+
      primitivePoolMean (widePairPool a m) _+_ at herror
  rw [← widePairPool] at herror
  have hmean56 := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hz (by decide : 5 ≤ 6)) hC) hF
  have h1 := mul_le_mul hright hm.1 (primitivePoolMean_nonneg _ _) (mul_nonneg hW (by linarith : 0 ≤ z))
  have h2 := mul_le_mul hleft hm.2.1 (primitivePoolMean_nonneg _ _) (mul_nonneg hW (by linarith : 0 ≤ z))
  have hlift := widePair_product_lift_bound a m
  change _ ≤ (widePairLiftConstant a : ℝ)*z^6*F at hlift
  have heq : W*z*(C*z^5*F)=W*C*z^6*F := by ring
  rw [heq] at h1 h2
  have heqC : (widePairErrorConstant a : ℝ)=2*W*C+C+widePairLiftConstant a := by
    simp only [widePairErrorConstant,W,C,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
  change _ ≤ (widePairErrorConstant a : ℝ)*z^6*F
  rw [heqC]
  nlinarith only [herror,h1,h2,hm.2.2,hmean56,hlift]

/-- Full Chebyshev lower constants are retained for each fixed wide family. -/
theorem eventually_widePair_progression_lower (a : ℕ) (ha : 21 ≤ a)
    (c : ℝ) (hc0 : 0 ≤ c) (hc : c<chebyshevRatioConstant) :
    ∀ᶠ m : ℕ in atTop,
      c*(independentN (widePairScale a) m : ℝ)*poolTotientMass (widePairPool a m) ≤
        ∑ d ∈ widePairPool a m, residueOneMangoldt d (independentN (widePairScale a) m) := by
  apply fixed_mass_progression_lower (widePairPool a) (widePairScale a) (widePairMassDenom a)
    (widePairErrorConstant a) 6 (by dsimp [widePairScale]; omega) (widePairMassDenom_pos a) ?_ ?_ ?_ c hc0 hc
  · exact Eventually.of_forall (fun m d hd => lt_of_lt_of_le (by decide) (widePairPool_bounds a m d hd).1)
  · filter_upwards [eventually_ge_atTop 1] with m hm
    exact widePairPool_mass_lower a m hm
  · exact Eventually.of_forall (fun m => widePair_composite_error_bound a m ha)

end Erdos821
