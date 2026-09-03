import Submission.FirstHitCardinalityCost
import Submission.FirstHitRefinedLogPower

/-! Recover one full logarithmic factor in the unrestricted first-hit bound.
The resulting k^(54/25) log(k+2)^(79/25) (1+log log(k+3)) estimate still does
NOT imply the conjectured quadratic bound. -/
namespace Erdos970.FiniteSelberg
open Finset Real

noncomputable def firstHitReciprocalConstant : ℝ := 1+|WeightedMertens.reciprocalConstant|
noncomputable def firstHitLogLog (k : ℕ) : ℝ := 1+log (log ((k : ℝ)+3))

lemma firstHitReciprocalConstant_ge : 1 ≤ firstHitReciprocalConstant := by
  unfold firstHitReciprocalConstant
  linarith [abs_nonneg WeightedMertens.reciprocalConstant]

lemma firstHitLogLog_ge (k : ℕ) (hk : 0 < k) : 1 ≤ firstHitLogLog k := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hfour : (1 : ℝ) ≤ log 4 := by
    rw [show (4 : ℝ) = 2^2 by norm_num, log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith [log_two_gt_d9]
  have hlog : 1 ≤ log ((k : ℝ)+3) :=
    hfour.trans (log_le_log (by norm_num) (by linarith))
  have hh := log_nonneg hlog
  unfold firstHitLogLog
  linarith

lemma firstHit_reciprocal_budget (k : ℕ) (hk : 0 < k) :
    log (log ((k : ℝ)+2))+WeightedMertens.reciprocalConstant ≤
      firstHitReciprocalConstant*firstHitLogLog k := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hlog := log_le_log (log_pos (by linarith : (1 : ℝ) < (k : ℝ)+2))
    (log_le_log (by positivity : (0 : ℝ) < (k : ℝ)+2) (by linarith : (k : ℝ)+2 ≤ (k : ℝ)+3))
  have hb := firstHitLogLog_ge k hk
  have ha := le_abs_self WeightedMertens.reciprocalConstant
  have hn := abs_nonneg WeightedMertens.reciprocalConstant
  dsimp [firstHitReciprocalConstant, firstHitLogLog] at *
  nlinarith

lemma firstHit_remainder_loglog_bound (k : ℕ) (hk : 0 < k) (L : ℝ) (hL : 0 ≤ L) :
    200*L*(1+4*exp L*(log (log ((k : ℝ)+2))+WeightedMertens.reciprocalConstant)) ≤
      1000*(1+L)*exp L*firstHitReciprocalConstant*firstHitLogLog k := by
  have hB := firstHitReciprocalConstant_ge
  have hb := firstHitLogLog_ge k hk
  have hprod : 1 ≤ firstHitReciprocalConstant*firstHitLogLog k := by nlinarith
  have hE : 1 ≤ exp L*firstHitReciprocalConstant*firstHitLogLog k := by
    have hh := mul_le_mul (one_le_exp hL) hprod (by norm_num : (0 : ℝ) ≤ 1) (exp_pos L).le
    nlinarith only [hh]
  have hr := mul_le_mul_of_nonneg_left (firstHit_reciprocal_budget k hk) (exp_pos L).le
  have hc : 1+4*exp L*(log (log ((k : ℝ)+2))+WeightedMertens.reciprocalConstant) ≤
      5*(exp L*firstHitReciprocalConstant*firstHitLogLog k) := by nlinarith only [hr,hE]
  have hh := mul_le_mul_of_nonneg_left hc (show 0 ≤ 200*L by positivity)
  have he0 : 0 ≤ exp L*firstHitReciprocalConstant*firstHitLogLog k := by linarith
  nlinarith only [hh,he0]

/-- Unconditional, with a fixed constant independent of the prime budget. -/
theorem exists_saturatedHit_loglog_bound : ∃ C > (0 : ℝ), ∀ k : ℕ, 0 < k →
    (jacobsthalFunction k : ℝ) ≤
      C*(k : ℝ)^(54/25 : ℝ)*log ((k : ℝ)+2)^(79/25 : ℝ)*
        (1+log (log ((k : ℝ)+3))) := by
  obtain ⟨L₀,hL₀,hmain⟩ := exists_saturatedHitMainSum_slack
  let K : ℝ := 2*(1+L₀)+362
  have hK : 0 < K := by dsimp [K]; linarith
  have hB : 1 ≤ firstHitReciprocalConstant := firstHitReciprocalConstant_ge
  have hB0 : 0 < firstHitReciprocalConstant := by linarith
  refine ⟨1001*K*exp L₀*(160 : ℝ)^(54/25 : ℝ)*firstHitReciprocalConstant, by positivity, ?_⟩
  intro k hk
  let p := Nat.nth Nat.Prime k
  let t := log ((k : ℝ)+2)
  let b := firstHitLogLog k
  have hb : 1 ≤ b := firstHitLogLog_ge k hk
  have hb0 : 0 < b := by linarith
  have hp := Nat.prime_nth_prime k
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hlp : 0 ≤ log (p : ℝ) := log_nonneg (by exact_mod_cast hp.one_lt.le)
  have hlog2 : log (2 : ℝ) ≤ t := log_le_log (by norm_num) (by linarith)
  have ht : (1/2 : ℝ) ≤ t := by linarith [log_two_gt_d9]
  have ht0 : 0 < t := by linarith
  let L : ℝ := L₀+(54/25 : ℝ)*log (p : ℝ)
  have hLL : L₀ ≤ L := by dsimp [L]; linarith
  have hL : 0 < L := hL₀.trans_le hLL
  have hLp := nth_prime_log_bound k hk
  have hLupper : 1+L ≤ K*t := by
    change log (p : ℝ) ≤ 160*t at hLp
    have hbase : 1+L₀ ≤ 2*(1+L₀)*t := by nlinarith
    dsimp only [L,K]
    nlinarith only [hbase,hLp,ht0]
  let X : ℝ := 1000*(1+L)*exp L*firstHitReciprocalConstant*b
  let m : ℕ := ⌊X⌋₊+1
  have hx : 0 ≤ X := by dsimp [X]; positivity
  have hXm : X < (m : ℝ) := by
    simpa only [m,Nat.cast_add,Nat.cast_one] using Nat.lt_floor_add_one X
  have hm : 200*L*(1+4*exp L*(log (log ((k : ℝ)+2))+WeightedMertens.reciprocalConstant)) < (m : ℝ) :=
    (firstHit_remainder_loglog_bound k hk L hL.le).trans_lt hXm
  have hpZ : p ≤ saturatedHitPrimeCut L 0 := by
    have hex : (p : ℝ) ≤ exp (L/(2*saturatedHitNode 0+1)) := by
      calc
        (p : ℝ) = exp (log (p : ℝ)) := (exp_log hp0).symm
        _ ≤ exp (L/(2*saturatedHitNode 0+1)) := by
          apply exp_le_exp.mpr
          norm_num [saturatedHitNode,L]
          linarith
    exact Nat.le_floor hex
  have hj := (jacobsthalFunction_le_iff k m).mpr
    (isJacobsthalBound_of_saturatedHitCardCost k L hL m hpZ (hmain L hLL) hm)
  have hmupper : (m : ℝ) ≤ X+1 := by
    dsimp [m]
    push_cast
    exact add_le_add (Nat.floor_le hx) le_rfl
  have hunit : 1 ≤ (1+L)*exp L*firstHitReciprocalConstant*b := by
    have h1 : 1 ≤ (1+L)*exp L := by nlinarith [one_le_exp hL.le]
    have h2 := mul_le_mul h1 hB (by norm_num : (0 : ℝ) ≤ 1) (by positivity : 0 ≤ (1+L)*exp L)
    have h3 := mul_le_mul h2 hb (by norm_num : (0 : ℝ) ≤ 1) (by positivity : 0 ≤ (1+L)*exp L*firstHitReciprocalConstant)
    simpa only [one_mul] using h3
  have hupper : (jacobsthalFunction k : ℝ) ≤ 1001*(1+L)*exp L*firstHitReciprocalConstant*b := by
    have hjR : (jacobsthalFunction k : ℝ) ≤ m := by exact_mod_cast hj
    dsimp [X] at hmupper
    nlinarith only [hjR,hmupper,hunit]
  have hpowbase : (p : ℝ) ≤ 160*(k : ℝ)*t := by
    have hh := PrimeCountingLower.nth_prime_mul_log k
    change (p : ℝ) ≤ 80*((k : ℝ)+1)*t at hh
    have hh' := mul_le_mul_of_nonneg_right (show 80*((k : ℝ)+1) ≤ 160*k by linarith) ht0.le
    exact hh.trans hh'
  have hpow := rpow_le_rpow hp0.le hpowbase (by norm_num : (0 : ℝ) ≤ 54/25)
  have heq : exp L = exp L₀*(p : ℝ)^(54/25 : ℝ) := by
    rw [rpow_def_of_pos hp0, ← exp_add]
    congr 1
    dsimp [L]
    ring
  have heupper : exp L ≤ exp L₀*(160*(k : ℝ)*t)^(54/25 : ℝ) := by
    rw [heq]
    exact mul_le_mul_of_nonneg_left hpow (exp_pos _).le
  calc
    (jacobsthalFunction k : ℝ) ≤
        (1001*firstHitReciprocalConstant*b)*((1+L)*exp L) := by nlinarith only [hupper]
    _ ≤ (1001*firstHitReciprocalConstant*b)*
        ((K*t)*(exp L₀*(160*(k : ℝ)*t)^(54/25 : ℝ))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul hLupper heupper (exp_pos _).le (by positivity)) (by positivity)
    _ = (1001*K*exp L₀*(160 : ℝ)^(54/25 : ℝ)*firstHitReciprocalConstant)*
        (k : ℝ)^(54/25 : ℝ)*t^(79/25 : ℝ)*(1+log (log ((k : ℝ)+3))) := by
      rw [mul_rpow (by positivity : (0 : ℝ) ≤ 160*k) ht0.le,
        mul_rpow (by norm_num : (0 : ℝ) ≤ 160) hk0.le,
        show (79/25 : ℝ) = 1+54/25 by norm_num, rpow_add ht0, rpow_one]
      dsimp only [b,firstHitLogLog]
      ring

#print axioms exists_saturatedHit_loglog_bound
end Erdos970.FiniteSelberg
