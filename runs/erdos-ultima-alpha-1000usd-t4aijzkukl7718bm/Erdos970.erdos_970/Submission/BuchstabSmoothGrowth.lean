import Submission.BuchstabSmoothCost
import Submission.BuchstabFourGridMain
import Submission.BuchstabDepthSharpTransfer
import Submission.BuchstabGrowth

/-! Smooth-support costs yield an unrestricted exponent51/25 bound with only
logarithmic exponent26/25. This remains weaker than the quadratic target. -/
namespace Erdos970.RecursiveSieve.Buchstab
open Finset Real Filter FiniteSelberg
set_option maxHeartbeats 0

noncomputable def smoothRefinementConstant (n : ℕ) : ℝ := 60*smoothLeafConstant 1*3600^n

lemma smoothRefinementConstant_pos (n : ℕ) : 0 < smoothRefinementConstant n := by
  have := smoothLeafConstant_pos 1
  unfold smoothRefinementConstant
  positivity

lemma smooth_cost_uniform_prefix (n k j : ℕ) (hj : j ≤ k) (D : ℝ)
    (hpkD : (nthPrime k : ℝ) ≤ D) :
    lowerErrorStep primeMarginal (primeKeep nthPrime)
      (upperError primeMarginal (primeKeep nthPrime) (scaledSharpSelbergCost nthPrime) n) j D ≤
      smoothRefinementConstant n*smoothLevelShape k D := by
  have hpjk : (nthPrime j : ℝ) ≤ nthPrime k := by exact_mod_cast nthPrime_strictMono.monotone hj
  have hpjD := hpjk.trans hpkD
  have hh := smooth_refined_lower_cost n j D hpjD
  have hp1 : (1 : ℝ) < nthPrime j := by exact_mod_cast (nthPrime_prime j).one_lt
  have hD1 : 1 < D := hp1.trans_le hpjD
  have hlD : 0 < log D := log_pos hD1
  have hlog := log_le_log (by linarith : (0 : ℝ) < nthPrime j) hpjk
  have hm := mul_le_mul_of_nonneg_left hlog (show 0 ≤ D/log D^3 by positivity)
  have hshape : smoothLevelShape j D ≤ smoothLevelShape k D := by
    unfold smoothLevelShape
    convert hm using 1 <;> ring
  exact hh.trans (mul_le_mul_of_nonneg_left hshape (smoothRefinementConstant_pos n).le)

lemma smooth_shape_exp_le (k : ℕ) (s : ℝ) (hs : 1 ≤ s) :
    smoothLevelShape k (exp (s*log (nthPrime k : ℝ))) ≤
      exp (s*log (nthPrime k : ℝ))/log (nthPrime k : ℝ)^2 := by
  have hp1 : (1 : ℝ) < nthPrime k := by exact_mod_cast (nthPrime_prime k).one_lt
  have hlp : 0 < log (nthPrime k : ℝ) := log_pos hp1
  have hsl : 0 < s*log (nthPrime k : ℝ) := by positivity
  have hpow : 1 ≤ s^3 := one_le_pow₀ hs
  unfold smoothLevelShape
  rw [log_exp,mul_pow]
  apply (div_le_div_iff₀ (by positivity : 0 < s^3*log (nthPrime k : ℝ)^3) (sq_pos_of_pos hlp)).mpr
  have hh := mul_le_mul_of_nonneg_left hpow
    (show 0 ≤ exp (s*log (nthPrime k : ℝ))*log (nthPrime k : ℝ)^3 by positivity)
  nlinarith only [hh]

lemma eventual_smooth_prime_growth : ∃ C > (0 : ℝ), ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
    (jacobsthalFunction k : ℝ) ≤ C*(nthPrime k : ℝ)^(51/25 : ℝ)/log (nthPrime k : ℝ) := by
  let A := smoothRefinementConstant 4
  have hA : 0 < A := smoothRefinementConstant_pos 4
  obtain ⟨N₀,hN₀⟩ := exists_referenceLower_four_positive
  obtain ⟨N₁,hN₁⟩ := eventually_atTop.mp eventually_eulerMass_initial_le_nine_fifths_log
  refine ⟨450*A+1,by positivity,max N₀ N₁,fun k hk => ?_⟩
  let p := nthPrime k
  have hp := nthPrime_prime k
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hkP : k ≤ p := nthPrime_strictMono.id_le k
  have hNp : max N₀ N₁ ≤ p := hk.trans hkP
  have hlp : 0 < log (p : ℝ) := log_pos hp1
  have hEuler := (eulerMass_strict_prefix_le p hp).trans (hN₁ p ((le_max_right _ _).trans hNp))
  let D : ℝ := exp ((51/25 : ℝ)*log (p : ℝ))
  have hD : 0 < D := exp_pos _
  have hpow : D = (p : ℝ)^(51/25 : ℝ) := by rw [rpow_def_of_pos hp0]; dsimp only [D]; congr 1; ring
  have hpD : (p : ℝ) ≤ D := by
    calc
      _ = exp (log (p : ℝ)) := (exp_log hp0).symm
      _ ≤ _ := exp_le_exp.mpr (by nlinarith only [hlp])
  have hmain := hN₀ k ((le_max_left _ _).trans hNp)
  have hEpos := eulerMass_pos p.primesBelow (fun q hq => (Nat.mem_primesBelow.mp hq).2)
  have hmainlog : 1/(450*log (p : ℝ)) ≤ referenceLower 4 k D := by
    apply le_trans _ hmain
    rw [nthPrime_prefix_density,div_div]
    exact one_div_le_one_div_of_le (by positivity) (by nlinarith only [hEuler])
  let E : ℝ := A*D/log (p : ℝ)^2
  have hcostAll (j : ℕ) (hj : j ≤ k) :
      lowerErrorStep primeMarginal (primeKeep nthPrime)
        (upperError primeMarginal (primeKeep nthPrime) (scaledSharpSelbergCost nthPrime) 4) j D ≤ E := by
    apply (smooth_cost_uniform_prefix 4 k j hj D hpD).trans
    have hh := mul_le_mul_of_nonneg_left (smooth_shape_exp_le k (51/25) (by norm_num)) hA.le
    convert hh using 1
    dsimp only [E,A,D,p]
    ring
  let X : ℝ := 450*A*D/log (p : ℝ)
  let m : ℕ := ⌊X⌋₊+1
  have hX : 0 ≤ X := by dsimp only [X]; positivity
  have hXm : X < (m : ℝ) := by simpa only [m,Nat.cast_add,Nat.cast_one] using Nat.lt_floor_add_one X
  have hcost : E < (m : ℝ)/(450*log (p : ℝ)) := by
    apply (lt_div_iff₀ (by positivity : 0 < 450*log (p : ℝ))).mpr
    have heq : E*(450*log (p : ℝ)) = X := by dsimp only [E,X]; field_simp
    rw [heq]
    exact hXm
  have hpos : E < (m : ℝ)*referenceLower 4 k D := hcost.trans_le (by
    simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hmainlog (Nat.cast_nonneg m))
  have hj := (jacobsthalFunction_le_iff k m).mpr
    (isJacobsthalBound_of_depth_sharp_cost 4 k m D hD.le (primeKeep_exp k _ (by norm_num)) E hcostAll hpos)
  have hjR : (jacobsthalFunction k : ℝ) ≤ m := by exact_mod_cast hj
  have hmupper : (m : ℝ) ≤ X+1 := by
    dsimp only [m]
    push_cast
    exact add_le_add (Nat.floor_le hX) le_rfl
  have hlogp : log (p : ℝ) ≤ D := (log_le_sub_one_of_pos hp0).trans (by linarith only [hpD])
  have hunit : 1 ≤ D/log (p : ℝ) := (le_div_iff₀ hlp).mpr (by simpa using hlogp)
  have ht : (jacobsthalFunction k : ℝ) ≤ (450*A+1)*D/log (p : ℝ) := by
    dsimp only [X] at hmupper
    have heq : (450*A+1)*D/log (p : ℝ) = 450*A*D/log (p : ℝ)+D/log (p : ℝ) := by ring
    rw [heq]
    linarith only [hjR,hmupper,hunit]
  rwa [hpow] at ht

/-- A logarithmic saving in the unrestricted bound, with a single constant
valid for all positive budgets. The base exponent is still greater than2. -/
theorem exists_smoothBuchstab_bound : ∃ C > (0 : ℝ), ∀ k : ℕ, 0 < k →
    (jacobsthalFunction k : ℝ) ≤ C*(k : ℝ)^(51/25 : ℝ)*log ((k : ℝ)+2)^(26/25 : ℝ) := by
  obtain ⟨A,hA,N,hN⟩ := eventual_smooth_prime_growth
  let C : ℝ := 2*A*(160 : ℝ)^(51/25 : ℝ)
  have hC : 0 < C := by dsimp only [C]; positivity
  obtain ⟨C',hC',hbound⟩ := absorb_finitely_many_bounds
    (fun k => (k : ℝ)^(51/25 : ℝ)*log ((k : ℝ)+2)^(26/25 : ℝ)) (by
      intro k hk
      have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
      have hl : 0 < log ((k : ℝ)+2) := log_pos (by linarith)
      positivity) C hC N (by
    intro k hk hkN
    let t := log ((k : ℝ)+2)
    let p := nthPrime k
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have ht : 0 < t := log_pos (by linarith)
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (nthPrime_prime k).pos
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (nthPrime_prime k).two_le
    have hlp : 0 < log (p : ℝ) := log_pos (by linarith)
    have hkp : (k : ℝ) ≤ p := by exact_mod_cast nthPrime_strictMono.id_le k
    have htlog : t ≤ 2*log (p : ℝ) := by
      have hh := log_le_log (by positivity : 0 < (k : ℝ)+2) (show (k : ℝ)+2 ≤ 2*p by linarith)
      rw [log_mul (by norm_num) hp0.ne'] at hh
      have hl2 := log_le_log (by norm_num : (0 : ℝ) < 2) hp2
      linarith only [hh,hl2]
    have hinv : 1/log (p : ℝ) ≤ 2/t := by
      apply (div_le_div_iff₀ hlp ht).mpr
      linarith only [htlog]
    have hpbound : (p : ℝ) ≤ 160*(k : ℝ)*t := by
      have hh := PrimeCountingLower.nth_prime_mul_log k
      change (p : ℝ) ≤ 80*((k : ℝ)+1)*t at hh
      nlinarith only [hh,hk1,ht]
    have hpow := rpow_le_rpow hp0.le hpbound (by norm_num : (0 : ℝ) ≤ 51/25)
    have hu := mul_le_mul (mul_le_mul_of_nonneg_left hpow hA.le) hinv
      (by positivity : 0 ≤ 1/log (p : ℝ)) (by positivity)
    have hj := hN k hkN
    have hh : (jacobsthalFunction k : ℝ) ≤ A*(160*(k : ℝ)*t)^(51/25 : ℝ)*(2/t) := by
      apply hj.trans
      simpa only [mul_one_div] using hu
    rw [mul_rpow (by positivity : (0 : ℝ) ≤ 160*k) ht.le,
      mul_rpow (by norm_num : (0 : ℝ) ≤ 160) hk0.le] at hh
    have he : t^(51/25 : ℝ)/t = t^(26/25 : ℝ) := by
      rw [show (51/25 : ℝ)=26/25+1 by norm_num,rpow_add ht,rpow_one]
      field_simp
    change (jacobsthalFunction k : ℝ) ≤ C*((k : ℝ)^(51/25 : ℝ)*t^(26/25 : ℝ))
    rw [← he]
    dsimp only [C]
    convert hh using 1
    ring)
  exact ⟨C',hC',fun k hk => by simpa only [mul_assoc] using hbound k hk⟩

#print axioms eventual_smooth_prime_growth
#print axioms exists_smoothBuchstab_bound
end Erdos970.RecursiveSieve.Buchstab
