import Submission.BuchstabLowerTail
import Submission.BuchstabGridCertificate

/-! The rounded initial profile table bounds the actual canonical upper
source, uniformly over all of its finitely many logarithmic nodes. -/
namespace Erdos970.FiniteSelberg
open Finset Real Filter
open Erdos970.BuchstabGrid
open Erdos970.RecursiveSieve Erdos970.RecursiveSieve.Buchstab
set_option maxRecDepth 100000
set_option maxHeartbeats 0

lemma profile_value_cast (j : ℕ) (hj : j < 18) :
    (profileValues[j]! : ℝ) = firstHitGridUpper j := by
  interval_cases j <;> norm_num [profileValues, firstHitGridUpper]

lemma buchstabBaseRatio_le_baseFormula (p : ℕ) (hp : p.Prime) (j : ℕ)
    (hj0 : 55 ≤ j) (hj : j < 601)
    (hLp : 20000*firstHitProfileError ≤ log (p : ℝ))
    (hLp' : 50*WeightedMertens.sharpMomentError ≤ log (p : ℝ))
    (hEuler : eulerMass (p+1).primesBelow ≤ (9/5 : ℝ)*log (p : ℝ)) :
    buchstabBaseRatio p ((j : ℝ)/50) ≤ (baseFormula j : ℝ) := by
  have hjR : (55 : ℝ) ≤ j := by exact_mod_cast hj0
  have hjQ : (0 : ℝ) < j := by linarith
  have hjne : j ≠ 0 := by omega
  unfold baseFormula
  rw [if_neg hjne]
  by_cases h100 : j ≤ 100
  · rw [if_pos h100]
    push_cast
    have h100R : (j : ℝ) ≤ 100 := by exact_mod_cast h100
    have hh := buchstabBaseRatio_middle p hp ((j : ℝ)/50) (by linarith) (by linarith) hLp hEuler
    rw [firstHitFullProfile, if_pos (by linarith : ((j : ℝ)/50)/2 ≤ 1)] at hh
    convert hh using 1 <;> ring
  rw [if_neg h100]
  by_cases h270 : j < 270
  · rw [if_pos h270]
    push_cast
    let a : ℕ := j/10-10
    let r : ℕ := j%10
    have ha : a < 17 := by dsimp [a]; omega
    have hr : r < 10 := Nat.mod_lt _ (by omega)
    have hjrel : j = 100+10*a+r := by dsimp [a,r]; omega
    have hjrelR : (j : ℝ) = 100+10*(a : ℝ)+(r : ℝ) := by exact_mod_cast hjrel
    have haR : (0 : ℝ) ≤ a := Nat.cast_nonneg a
    have haR' : (a : ℝ) ≤ 16 := by exact_mod_cast (show a ≤ 16 by omega)
    have hrR : (0 : ℝ) ≤ r := Nat.cast_nonneg r
    have hrR' : (r : ℝ) ≤ 10 := by exact_mod_cast hr.le
    have hA : 1+(a : ℝ)/10 ∈ Set.Icc (1 : ℝ) 3 := by constructor <;> linarith
    have hB : 1+((a+1 : ℕ) : ℝ)/10 ∈ Set.Icc (1 : ℝ) 3 := by
      push_cast
      constructor <;> linarith
    have hw0 : 0 ≤ 1-(r : ℝ)/10 := by linarith
    have hw1 : 0 ≤ (r : ℝ)/10 := by positivity
    have hc := firstHitReciprocal_convex.2 hA hB hw0 hw1
      (show 1-(r : ℝ)/10+(r : ℝ)/10 = 1 by ring)
    simp only [smul_eq_mul] at hc
    have he : (1-(r : ℝ)/10)*(1+(a : ℝ)/10)+
        ((r : ℝ)/10)*(1+((a+1 : ℕ) : ℝ)/10) = (j : ℝ)/100 := by
      push_cast
      nlinarith only [hjrelR]
    rw [he] at hc
    have hvA := firstHitReciprocal_grid_bound a (by omega)
    have hvB := firstHitReciprocal_grid_bound (a+1) (by omega)
    rw [← profile_value_cast a (by omega)] at hvA
    rw [← profile_value_cast (a+1) (by omega)] at hvB
    have hchord := hc.trans (add_le_add
      (mul_le_mul_of_nonneg_left hvA hw0) (mul_le_mul_of_nonneg_left hvB hw1))
    have hjgt : (100 : ℝ) < j := by exact_mod_cast (show 100 < j by omega)
    have h270R : (j : ℝ) < 270 := by exact_mod_cast h270
    have hm := buchstabBaseRatio_middle p hp ((j : ℝ)/50) (by linarith) (by linarith) hLp hEuler
    rw [show ((j : ℝ)/50)/2 = (j : ℝ)/100 by ring, firstHitFullProfile,
      if_neg (by linarith : ¬(j : ℝ)/100 ≤ 1)] at hm
    have hh := hm.trans (mul_le_mul_of_nonneg_left hchord (by norm_num : (0 : ℝ) ≤ 90009/50000))
    exact hh
  rw [if_neg h270]
  by_cases h400 : j < 400
  · rw [if_pos h400]
    push_cast
    exact buchstabBaseRatio_saturated p hp ((j : ℝ)/50)
      (by
        have hj' : (270 : ℝ) ≤ j := by exact_mod_cast (show 270 ≤ j by omega)
        linarith) hLp hEuler
  rw [if_neg h400]
  push_cast
  have hj' : (400 : ℝ) ≤ j := by exact_mod_cast (show 400 ≤ j by omega)
  have hh := buchstabBaseRatio_eighth_tail p hp ((j : ℝ)/50) (by linarith) hLp'
  rw [show 8/((j : ℝ)/50) = 400/(j : ℝ) by ring] at hh
  apply hh.trans
  have hz : (0 : ℝ) ≤ (400/(j : ℝ))^8 := by positivity
  nlinarith

lemma referenceUpper_zero_le_grid (k j : ℕ) (hj0 : 55 ≤ j) (hj : j < 601)
    (hLp : 20000*firstHitProfileError ≤ log (nthPrime k : ℝ))
    (hLp' : 50*WeightedMertens.sharpMomentError ≤ log (nthPrime k : ℝ))
    (hEuler : eulerMass (nthPrime k+1).primesBelow ≤ (9/5 : ℝ)*log (nthPrime k : ℝ)) :
    referenceUpper 0 k (exp (((j : ℝ)/50)*log (nthPrime k : ℝ))) ≤
      prefixDensity primeMarginal k*((baseNodes j : ℝ)/1000000) := by
  have hb := scaled_base_le_normalized_profile k ((j : ℝ)/50) (by positivity)
  have hm := buchstabBaseRatio_le_baseFormula (nthPrime k) (nthPrime_prime k) j hj0 hj hLp hLp' hEuler
  have hrat := base_formula_bound_nat j hj
  change baseFormula j ≤ (baseNodes j : ℚ)/1000000 at hrat
  have hreal : (baseFormula j : ℝ) ≤ (baseNodes j : ℝ)/1000000 := by
    have hh : (baseFormula j : ℝ) ≤ (((baseNodes j : ℚ)/1000000 : ℚ) : ℝ) := Rat.cast_le.mpr hrat
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hh
  exact hb.trans (mul_le_mul_of_nonneg_left (hm.trans hreal) (nthPrime_prefix_density_pos k).le)

/-- One absolute threshold suffices for every initial grid node. -/
theorem exists_referenceUpper_zero_grid : ∃ N : ℕ, ∀ k : ℕ, N ≤ nthPrime k →
    ∀ j : ℕ, 55 ≤ j → j < 601 →
      referenceUpper 0 k (exp (((j : ℝ)/50)*log (nthPrime k : ℝ))) ≤
        prefixDensity primeMarginal k*((baseNodes j : ℝ)/1000000) := by
  have hlog : Tendsto (fun n : ℕ => log (n : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨N,hN⟩ := eventually_atTop.mp
    ((hlog.eventually_ge_atTop (20000*firstHitProfileError)).and
      ((hlog.eventually_ge_atTop (50*WeightedMertens.sharpMomentError)).and
        eventually_eulerMass_initial_le_nine_fifths_log))
  refine ⟨N,fun k hk j hj0 hj => ?_⟩
  obtain ⟨h1,h2,h3⟩ := hN (nthPrime k) hk
  exact referenceUpper_zero_le_grid k j hj0 hj h1 h2 h3

#print axioms buchstabBaseRatio_le_baseFormula
#print axioms exists_referenceUpper_zero_grid
end Erdos970.FiniteSelberg
