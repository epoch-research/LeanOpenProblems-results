import Submission.BuchstabDepthSharpTransfer
import Submission.BuchstabDepthSharpCost
import Submission.BuchstabFourGridMain
import Submission.BuchstabLinearGrowth

/-! Four actual upper refinements lower the base exponent to51/25.
The complete error retains eight reciprocal-prefix factors. This is not quadratic. -/
namespace Erdos970.RecursiveSieve.Buchstab
open Finset Real Filter FiniteSelberg
set_option maxHeartbeats 0

noncomputable def fourGrowthConstant : ℝ := sharpRefinementCostConstant*(1+firstHitReciprocalConstant)^8

lemma fourGrowthConstant_pos : 0 < fourGrowthConstant := by
  have hh := firstHitReciprocalConstant_ge
  have hB : 0 < sharpRefinementCostConstant := (by norm_num : (0 : ℝ) < 4).trans_le sharpRefinementCostConstant_ge
  dsimp only [fourGrowthConstant]
  positivity

lemma reference_four_cost_loglog (k : ℕ) (hk : 0 < k) :
    sharpRefinementCostConstant*(1+prefixReciprocal nthPrime k)^8 ≤ fourGrowthConstant*(firstHitLogLog k)^8 := by
  have hZ := (prefixReciprocal_loglog nthPrime nthPrime_prime nthPrime_strictMono.injective k).trans
    (firstHit_reciprocal_budget k hk)
  have hH := firstHitLogLog_ge k hk
  have hbound : 1+prefixReciprocal nthPrime k ≤ (1+firstHitReciprocalConstant)*firstHitLogLog k := by
    nlinarith only [hZ,hH]
  have hp := pow_le_pow_left₀ (by have := prefixReciprocal_nonneg nthPrime k; linarith) hbound 8
  rw [mul_pow] at hp
  have hB : 0 ≤ sharpRefinementCostConstant := (by norm_num : (0 : ℝ) ≤ 4).trans sharpRefinementCostConstant_ge
  simpa only [fourGrowthConstant,mul_assoc] using mul_le_mul_of_nonneg_left hp hB

lemma eventual_four_prime_growth : ∃ C > (0 : ℝ), ∃ N : ℕ, ∀ k : ℕ, 0 < k → N ≤ k →
    (jacobsthalFunction k : ℝ) ≤ C*(nthPrime k : ℝ)^(51/25 : ℝ)*log (nthPrime k : ℝ)*(firstHitLogLog k)^8 := by
  let A := fourGrowthConstant
  have hA : 0 < A := fourGrowthConstant_pos
  have hlog2 : 0 < log (2 : ℝ) := log_pos (by norm_num)
  obtain ⟨N₀,hN₀⟩ := exists_referenceLower_four_positive
  obtain ⟨N₁,hN₁⟩ := eventually_atTop.mp eventually_eulerMass_initial_le_nine_fifths_log
  refine ⟨450*A+1/log (2 : ℝ),by positivity,max N₀ N₁,fun k hk0 hk => ?_⟩
  let p := nthPrime k
  let H := firstHitLogLog k
  have hH : 1 ≤ H := firstHitLogLog_ge k hk0
  have hH8 : 1 ≤ H^8 := one_le_pow₀ hH
  have hp := nthPrime_prime k
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hkP : k ≤ p := nthPrime_strictMono.id_le k
  have hNp : max N₀ N₁ ≤ p := hk.trans hkP
  have hlogp : 0 < log (p : ℝ) := log_pos (by linarith)
  have hEuler := (eulerMass_strict_prefix_le p hp).trans (hN₁ p ((le_max_right _ _).trans hNp))
  let D : ℝ := exp ((51/25 : ℝ)*log (p : ℝ))
  have hD : 0 < D := exp_pos _
  have hpow : D = (p : ℝ)^(51/25 : ℝ) := by rw [rpow_def_of_pos hp0]; dsimp only [D]; congr 1; ring
  have hmain := hN₀ k ((le_max_left _ _).trans hNp)
  have hE := eulerMass_pos p.primesBelow (fun q hq => (Nat.mem_primesBelow.mp hq).2)
  have hmainlog : 1/(450*log (p : ℝ)) ≤ referenceLower 4 k D := by
    apply le_trans _ hmain
    rw [nthPrime_prefix_density,div_div]
    exact one_div_le_one_div_of_le (by positivity) (by nlinarith only [hEuler])
  let X : ℝ := 450*log (p : ℝ)*A*H^8*D
  let m : ℕ := ⌊X⌋₊+1
  have hX : 0 ≤ X := by dsimp only [X]; positivity
  have hXm : X < (m : ℝ) := by
    simpa only [m,Nat.cast_add,Nat.cast_one] using Nat.lt_floor_add_one X
  have hcost : A*H^8*D < (m : ℝ)/(450*log (p : ℝ)) := by
    apply (lt_div_iff₀ (by positivity : (0 : ℝ) < 450*log (p : ℝ))).mpr
    dsimp only [X] at hXm
    nlinarith only [hXm]
  have hcostA := mul_le_mul_of_nonneg_right (reference_four_cost_loglog k hk0) hD.le
  have hpos : sharpRefinementCostConstant*(1+prefixReciprocal nthPrime k)^8*D < (m : ℝ)*referenceLower 4 k D := by
    apply hcostA.trans_lt
    exact hcost.trans_le (by simpa only [mul_one_div] using
      mul_le_mul_of_nonneg_left hmainlog (Nat.cast_nonneg m))
  have hcostAll (j : ℕ) (hj : j ≤ k) :
      lowerErrorStep primeMarginal (primeKeep nthPrime)
        (upperError primeMarginal (primeKeep nthPrime) (scaledSharpSelbergCost nthPrime) 4) j D ≤
          sharpRefinementCostConstant*(1+prefixReciprocal nthPrime k)^8*D := by
    simpa only [show 3+1=4 by omega,show 2*3+2=8 by omega] using sharp_lower_depth_le_linear 3 j k hj D hD.le
  have hj := (jacobsthalFunction_le_iff k m).mpr
    (isJacobsthalBound_of_depth_sharp_cost 4 k m D hD.le (primeKeep_exp k _ (by norm_num))
      (sharpRefinementCostConstant*(1+prefixReciprocal nthPrime k)^8*D) hcostAll hpos)
  have hjR : (jacobsthalFunction k : ℝ) ≤ m := by exact_mod_cast hj
  have hmupper : (m : ℝ) ≤ X+1 := by
    dsimp only [m]
    push_cast
    exact add_le_add (Nat.floor_le hX) le_rfl
  have hpow1 : 1 ≤ (p : ℝ)^(51/25 : ℝ) := one_le_rpow (by linarith) (by norm_num)
  have hl2 : log (2 : ℝ) ≤ log (p : ℝ) := log_le_log (by norm_num) hp2
  have hunit : 1 ≤ ((p : ℝ)^(51/25 : ℝ)*log (p : ℝ))/log (2 : ℝ) := by
    apply (le_div_iff₀ hlog2).mpr
    nlinarith only [hpow1,hl2,hlog2]
  have hunit' : 1 ≤ (1/log (2 : ℝ))*(p : ℝ)^(51/25 : ℝ)*log (p : ℝ)*H^8 := by
    have hh := one_le_mul_of_one_le_of_one_le hunit hH8
    convert hh using 1
    ring
  dsimp only [X] at hmupper
  rw [hpow] at hmupper
  change (jacobsthalFunction k : ℝ) ≤ (450*A+1/log (2 : ℝ))*(p : ℝ)^(51/25 : ℝ)*log (p : ℝ)*H^8
  nlinarith only [hjR,hmupper,hunit']

/-- A single constant, valid for all positive budgets, with no auxiliary
positive power allowance. This still does not settle quadratic growth. -/
theorem exists_fourBuchstab_loglog_bound : ∃ C > (0 : ℝ), ∀ k : ℕ, 0 < k →
    (jacobsthalFunction k : ℝ) ≤ C*(k : ℝ)^(51/25 : ℝ)*log ((k : ℝ)+2)^(76/25 : ℝ)*
      (1+log (log ((k : ℝ)+3)))^8 := by
  obtain ⟨A,hA,N,hN⟩ := eventual_four_prime_growth
  let B : ℝ := 2+log (160 : ℝ)/log (2 : ℝ)
  have hB : 0 < B := by
    have h1 : 0 ≤ log (160 : ℝ) := log_nonneg (by norm_num)
    have h2 : 0 < log (2 : ℝ) := log_pos (by norm_num)
    dsimp only [B]
    positivity
  let C : ℝ := A*(160 : ℝ)^(51/25 : ℝ)*B
  have hC : 0 < C := by dsimp only [C]; positivity
  obtain ⟨C',hC',hCbound⟩ := absorb_finitely_many_bounds
    (fun k => (k : ℝ)^(51/25 : ℝ)*log ((k : ℝ)+2)^(76/25 : ℝ)*(firstHitLogLog k)^8) (by
      intro k hk
      have hkR : (0 : ℝ) < k := by exact_mod_cast hk
      have ht : 0 < log ((k : ℝ)+2) := log_pos (by linarith)
      have hH := firstHitLogLog_ge k hk
      positivity) C hC N (by
    intro k hk hkN
    let t := log ((k : ℝ)+2)
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have ht : 0 < t := log_pos (by linarith)
    have hH := firstHitLogLog_ge k hk
    have hp0 : (0 : ℝ) < nthPrime k := by exact_mod_cast (nthPrime_prime k).pos
    have hpbound : (nthPrime k : ℝ) ≤ 160*(k : ℝ)*t := by
      have hh := PrimeCountingLower.nth_prime_mul_log k
      change (nthPrime k : ℝ) ≤ 80*((k : ℝ)+1)*t at hh
      nlinarith only [hh,hk1,ht]
    have hpow := rpow_le_rpow hp0.le hpbound (by norm_num : (0 : ℝ) ≤ 51/25)
    have hlog := nthPrime_log_upper k hk
    change log (nthPrime k : ℝ) ≤ B*t at hlog
    have hu := mul_le_mul (mul_le_mul_of_nonneg_left hpow hA.le) hlog
      (log_natCast_nonneg _) (by positivity)
    have hh := (hN k hk hkN).trans (mul_le_mul_of_nonneg_right hu (by positivity : 0 ≤ (firstHitLogLog k)^8))
    rw [mul_rpow (by positivity : (0 : ℝ) ≤ 160*k) ht.le,
      mul_rpow (by norm_num : (0 : ℝ) ≤ 160) hk0.le] at hh
    dsimp only [C]
    rw [show (76/25 : ℝ)=51/25+1 by norm_num,rpow_add ht,rpow_one]
    convert hh using 1
    ring)
  exact ⟨C',hC',fun k hk => by simpa only [firstHitLogLog,mul_assoc] using hCbound k hk⟩

#print axioms reference_four_cost_loglog
#print axioms eventual_four_prime_growth
#print axioms exists_fourBuchstab_loglog_bound
end Erdos970.RecursiveSieve.Buchstab
