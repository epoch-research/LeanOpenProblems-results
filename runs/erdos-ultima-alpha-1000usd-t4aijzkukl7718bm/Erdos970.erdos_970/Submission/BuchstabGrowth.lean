import Submission.BuchstabIntervalSurvivor
import Submission.FirstHitRefinedLogPower

/-! Unrestricted power bounds furnished by the fully charged finite Buchstab
refinement. The critical exponent remains strictly above two. -/
namespace Erdos970.RecursiveSieve.Buchstab
open Finset Real Filter FiniteSelberg
set_option maxHeartbeats 0

lemma eventual_refined_prime_growth (b : ℝ) (hb : 21/10 < b) :
    ∃ C > (0 : ℝ), ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
      (jacobsthalFunction k : ℝ) ≤ C*(nthPrime k : ℝ)^b*log (nthPrime k : ℝ) := by
  let a : ℝ := b/(21/10)
  have ha : 1 < a := by dsimp [a]; linarith
  let A : ℝ := 4*(1+reciprocalPowerConstant a)^3
  have hA : 0 < A := by
    have hh := reciprocalPowerConstant_nonneg a
    dsimp [A]
    positivity
  have hlog2 : 0 < log (2 : ℝ) := log_pos (by norm_num)
  obtain ⟨N₀,hN₀⟩ := exists_referenceLower_one_positive
  obtain ⟨N₁,hN₁⟩ := eventually_atTop.mp eventually_eulerMass_initial_le_nine_fifths_log
  refine ⟨360*A+1/log (2 : ℝ),by positivity,max N₀ N₁,fun k hk => ?_⟩
  let p := nthPrime k
  have hp := nthPrime_prime k
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hkP : k ≤ p := nthPrime_strictMono.id_le k
  have hNp : max N₀ N₁ ≤ p := hk.trans hkP
  have hlogp : 0 < log (p : ℝ) := log_pos (by linarith)
  have hEuler := (eulerMass_strict_prefix_le p hp).trans (hN₁ p ((le_max_right _ _).trans hNp))
  let D : ℝ := exp ((21/10 : ℝ)*log (p : ℝ))
  have hD : 0 < D := exp_pos _
  have hpow : D^a = (p : ℝ)^b := by
    rw [rpow_def_of_pos hD]
    dsimp only [D,a]
    rw [log_exp,rpow_def_of_pos hp0]
    congr 1
    ring
  have hmain := hN₀ k ((le_max_left _ _).trans hNp)
  have hE := eulerMass_pos p.primesBelow (fun q hq => (Nat.mem_primesBelow.mp hq).2)
  have hmainlog : 1/(360*log (p : ℝ)) ≤ referenceLower 1 k D := by
    apply le_trans _ hmain
    rw [nthPrime_prefix_density,div_div]
    exact one_div_le_one_div_of_le (by positivity) (by nlinarith only [hEuler])
  let X : ℝ := 360*log (p : ℝ)*A*D^a
  let m : ℕ := ⌊X⌋₊+1
  have hX : 0 ≤ X := by dsimp [X]; positivity
  have hXm : X < (m : ℝ) := by
    simpa only [m,Nat.cast_add,Nat.cast_one] using Nat.lt_floor_add_one X
  have hcost : A*D^a < (m : ℝ)/(360*log (p : ℝ)) := by
    apply (lt_div_iff₀ (by positivity : (0 : ℝ) < 360*log (p : ℝ))).mpr
    dsimp only [X] at hXm
    nlinarith only [hXm]
  have hpos : 4*(1+reciprocalPowerConstant a)^3*D^a < (m : ℝ)*referenceLower 1 k D := by
    exact hcost.trans_le (by simpa only [mul_one_div] using
      mul_le_mul_of_nonneg_left hmainlog (Nat.cast_nonneg m))
  have hj := (jacobsthalFunction_le_iff k m).mpr
    (isJacobsthalBound_of_refined_main k m D hD.le (primeKeep_exp k _ (by norm_num)) a ha hpos)
  have hjR : (jacobsthalFunction k : ℝ) ≤ m := by exact_mod_cast hj
  have hmupper : (m : ℝ) ≤ X+1 := by
    dsimp only [m]
    push_cast
    exact add_le_add (Nat.floor_le hX) le_rfl
  have hpow1 : 1 ≤ (p : ℝ)^b := one_le_rpow (by linarith) (by linarith)
  have hl2 : log (2 : ℝ) ≤ log (p : ℝ) := log_le_log (by norm_num) hp2
  have hunit : 1 ≤ ((p : ℝ)^b*log (p : ℝ))/log (2 : ℝ) := by
    apply (le_div_iff₀ hlog2).mpr
    nlinarith only [hpow1,hl2,hlog2]
  dsimp only [X] at hmupper
  rw [hpow] at hmupper
  change (jacobsthalFunction k : ℝ) ≤ (360*A+1/log (2 : ℝ))*(p : ℝ)^b*log (p : ℝ)
  have hunit' : 1 ≤ (1/log (2 : ℝ))*(p : ℝ)^b*log (p : ℝ) := by
    convert hunit using 1
    ring
  nlinarith only [hjR,hmupper,hunit']

lemma absorb_finitely_many_bounds (f : ℕ → ℝ) (hf : ∀ k : ℕ, 0 < k → 0 < f k)
    (C : ℝ) (hC : 0 < C) (N : ℕ)
    (hbound : ∀ k : ℕ, 0 < k → N ≤ k → (jacobsthalFunction k : ℝ) ≤ C*f k) :
    ∃ C' > (0 : ℝ), ∀ k : ℕ, 0 < k → (jacobsthalFunction k : ℝ) ≤ C'*f k := by
  let S : ℝ := ∑ k ∈ range N, |(jacobsthalFunction k : ℝ)/f k|
  have hS : 0 ≤ S := sum_nonneg (fun k hk => abs_nonneg _)
  refine ⟨C+1+S,by positivity,fun k hk => ?_⟩
  by_cases hNk : N ≤ k
  · exact (hbound k hk hNk).trans (mul_le_mul_of_nonneg_right (by linarith) (hf k hk).le)
  · have hsmall : (jacobsthalFunction k : ℝ)/f k ≤ S :=
      (le_abs_self _).trans (single_le_sum (f := fun i : ℕ => |(jacobsthalFunction i : ℝ)/f i|)
        (s := range N) (a := k) (fun i hi => abs_nonneg _) (mem_range.mpr (by omega)))
    exact (div_le_iff₀ (hf k hk)).mp (hsmall.trans (by linarith))

lemma nthPrime_log_upper (k : ℕ) (hk : 0 < k) :
    log (nthPrime k : ℝ) ≤ (2+log (160 : ℝ)/log (2 : ℝ))*log ((k : ℝ)+2) := by
  let t := log ((k : ℝ)+2)
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have ht : 0 < t := log_pos (by linarith)
  have hlog2 : 0 < log (2 : ℝ) := log_pos (by norm_num)
  have h2t : log (2 : ℝ) ≤ t := log_le_log (by norm_num) (by linarith)
  have hp0 : (0 : ℝ) < nthPrime k := by exact_mod_cast (nthPrime_prime k).pos
  have hpbound : (nthPrime k : ℝ) ≤ 160*(k : ℝ)*t := by
    have hh := PrimeCountingLower.nth_prime_mul_log k
    change (nthPrime k : ℝ) ≤ 80*((k : ℝ)+1)*t at hh
    nlinarith only [hh,hk1,ht]
  have hlog := log_le_log hp0 hpbound
  rw [log_mul (by positivity : (160 : ℝ)*(k : ℝ) ≠ 0) ht.ne',
    log_mul (by norm_num : (160 : ℝ) ≠ 0) hk0.ne'] at hlog
  have hlk : log (k : ℝ) ≤ t := log_le_log hk0 (by linarith)
  have hlt : log t ≤ t := (log_le_sub_one_of_pos ht).trans (by linarith)
  have hl160 : 0 ≤ log (160 : ℝ) := log_nonneg (by norm_num)
  have hscale : log (160 : ℝ) ≤ (log (160 : ℝ)/log (2 : ℝ))*t := by
    have hh := mul_le_mul_of_nonneg_left h2t (div_nonneg hl160 hlog2.le)
    rw [div_mul_cancel₀ _ hlog2.ne'] at hh
    exact hh
  change log (nthPrime k : ℝ) ≤ (2+log (160 : ℝ)/log (2 : ℝ))*t
  nlinarith only [hlog,hlk,hlt,hscale]

/-- Any fixed exponent strictly above21/10 is available, with its logarithmic
factor and one constant valid for every positive budget. -/
theorem exists_refinedBuchstab_logpower_bound (b : ℝ) (hb : 21/10 < b) :
    ∃ C > (0 : ℝ), ∀ k : ℕ, 0 < k → (jacobsthalFunction k : ℝ) ≤
      C*(k : ℝ)^b*log ((k : ℝ)+2)^(b+1) := by
  obtain ⟨A,hA,N,hN⟩ := eventual_refined_prime_growth b hb
  let B : ℝ := 2+log (160 : ℝ)/log (2 : ℝ)
  have hB : 0 < B := by
    have h1 : 0 ≤ log (160 : ℝ) := log_nonneg (by norm_num)
    have h2 : 0 < log (2 : ℝ) := log_pos (by norm_num)
    dsimp [B]
    positivity
  let C : ℝ := A*(160 : ℝ)^b*B
  have hC : 0 < C := by dsimp [C]; positivity
  obtain ⟨C',hC',hCbound⟩ := absorb_finitely_many_bounds
    (fun k => (k : ℝ)^b*log ((k : ℝ)+2)^(b+1)) (by
      intro k hk
      have hkR : (0 : ℝ) < k := by exact_mod_cast hk
      have ht : 0 < log ((k : ℝ)+2) := log_pos (by linarith)
      positivity) C hC N (by
    intro k hk hkN
    let t := log ((k : ℝ)+2)
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have ht : 0 < t := log_pos (by linarith)
    have hp0 : (0 : ℝ) < nthPrime k := by exact_mod_cast (nthPrime_prime k).pos
    have hpbound : (nthPrime k : ℝ) ≤ 160*(k : ℝ)*t := by
      have hh := PrimeCountingLower.nth_prime_mul_log k
      change (nthPrime k : ℝ) ≤ 80*((k : ℝ)+1)*t at hh
      nlinarith only [hh,hk1,ht]
    have hpow := rpow_le_rpow hp0.le hpbound (by linarith : 0 ≤ b)
    have hlog := nthPrime_log_upper k hk
    change log (nthPrime k : ℝ) ≤ B*t at hlog
    have hh := (hN k hkN).trans (mul_le_mul
      (mul_le_mul_of_nonneg_left hpow hA.le) hlog (log_natCast_nonneg _) (by positivity))
    rw [mul_rpow (by positivity : (0 : ℝ) ≤ 160*k) ht.le,
      mul_rpow (by norm_num : (0 : ℝ) ≤ 160) hk0.le] at hh
    dsimp only [C]
    rw [rpow_add ht,rpow_one]
    convert hh using 1
    ring)
  exact ⟨C',hC',fun k hk => by simpa only [mul_assoc] using hCbound k hk⟩

/-- The rounded finite refinement gives every power exponent above21/10.
The constants depend on ε; no bound at exponent two is inferred. -/
theorem exists_refinedBuchstab_power_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C > (0 : ℝ), ∀ k : ℕ, 0 < k → (jacobsthalFunction k : ℝ) ≤ C*(k : ℝ)^((21/10 : ℝ)+ε) := by
  let b : ℝ := 21/10+ε/2
  have hb : 21/10 < b := by dsimp [b]; linarith
  obtain ⟨C,hC,hbound⟩ := exists_refinedBuchstab_logpower_bound b hb
  let D : ℝ := ((3 : ℝ)^((ε/2)/(b+1))/((ε/2)/(b+1)))^(b+1)
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨C*D,mul_pos hC hD,fun k hk => ?_⟩
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hl := log_rpow_le_small_power (b+1) (ε/2) (by linarith) (by linarith) k hk
  change log ((k : ℝ)+2)^(b+1) ≤ D*(k : ℝ)^(ε/2) at hl
  have hh := (hbound k hk).trans (mul_le_mul_of_nonneg_left hl (by positivity : 0 ≤ C*(k : ℝ)^b))
  have he : (21/10 : ℝ)+ε = b+ε/2 := by dsimp [b]; ring
  rw [he,rpow_add hk0]
  convert hh using 1
  ring

#print axioms eventual_refined_prime_growth
#print axioms exists_refinedBuchstab_logpower_bound
#print axioms exists_refinedBuchstab_power_bound
end Erdos970.RecursiveSieve.Buchstab
