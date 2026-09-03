import Submission.BuchstabCountTransfer
import Submission.BuchstabLinearGrowth

/-! Uniform m/log(k) survivor counts above every fixed power scale larger
than21/10. This supplies a quantitative input for low-tail exposure. -/
namespace Erdos970.RecursiveSieve.Buchstab
open Finset Real Filter FiniteSelberg
set_option maxHeartbeats 0

lemma firstHitLogLog_le_twice_log (k : ℕ) (hk : 0 < k) :
    firstHitLogLog k ≤ 2*log ((k : ℝ)+2) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hlog := log_le_sub_one_of_pos (log_pos (by linarith : (1 : ℝ) < (k : ℝ)+3))
  have hsq : (k : ℝ)+3 ≤ ((k : ℝ)+2)^2 := by nlinarith
  have hs := log_le_log (by positivity : (0 : ℝ) < (k : ℝ)+3) hsq
  rw [log_pow] at hs
  norm_num only [Nat.cast_ofNat] at hs
  dsimp only [firstHitLogLog]
  linarith

noncomputable def buchstabCountLogConstant : ℝ := 720*(2+log (160 : ℝ)/log (2 : ℝ))

lemma buchstabCountLogConstant_pos : 0 < buchstabCountLogConstant := by
  have h1 : 0 ≤ log (160 : ℝ) := log_nonneg (by norm_num)
  have h2 : 0 < log (2 : ℝ) := log_pos (by norm_num)
  dsimp only [buchstabCountLogConstant]
  positivity

noncomputable def referenceCountCost (k : ℕ) : ℝ :=
  720*log (nthPrime k : ℝ)*(4*(1+prefixReciprocal nthPrime k)^3)*
    exp ((21/10 : ℝ)*log (nthPrime k : ℝ))

lemma referenceCountCost_log_bound (k : ℕ) (hk : 0 < k) :
    referenceCountCost k ≤
      (8*linearRefinementConstant*(160 : ℝ)^(21/10 : ℝ)*buchstabCountLogConstant)*
        (k : ℝ)^(21/10 : ℝ)*log ((k : ℝ)+2)^(61/10 : ℝ) := by
  let t := log ((k : ℝ)+2)
  let B := 2+log (160 : ℝ)/log (2 : ℝ)
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have ht : 0 < t := log_pos (by linarith)
  have hH := firstHitLogLog_ge k hk
  have hHup := firstHitLogLog_le_twice_log k hk
  have hp0 : (0 : ℝ) < nthPrime k := by exact_mod_cast (nthPrime_prime k).pos
  have hpbound : (nthPrime k : ℝ) ≤ 160*(k : ℝ)*t := by
    have hh := PrimeCountingLower.nth_prime_mul_log k
    change (nthPrime k : ℝ) ≤ 80*((k : ℝ)+1)*t at hh
    nlinarith only [hh,hk1,ht]
  have hpow := rpow_le_rpow hp0.le hpbound (by norm_num : (0 : ℝ) ≤ 21/10)
  have hlog := nthPrime_log_upper k hk
  change log (nthPrime k : ℝ) ≤ B*t at hlog
  have hcost := (reference_linear_cost_loglog k hk).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith : 0 ≤ firstHitLogLog k) hHup 3)
      linearRefinementConstant_pos.le)
  have hB0 : 0 ≤ B := by
    have hh := buchstabCountLogConstant_pos
    dsimp only [buchstabCountLogConstant] at hh
    dsimp only [B]
    linarith
  have hZ := prefixReciprocal_nonneg nthPrime k
  have hA := linearRefinementConstant_pos
  have hh := mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left hlog (by norm_num : (0 : ℝ) ≤ 720))
    hcost (by positivity) (by positivity)) hpow (rpow_nonneg hp0.le _) (by positivity)
  have he : exp ((21/10 : ℝ)*log (nthPrime k : ℝ)) = (nthPrime k : ℝ)^(21/10 : ℝ) := by
    rw [rpow_def_of_pos hp0]
    congr 1
    ring
  rw [mul_rpow (by positivity : (0 : ℝ) ≤ 160*k) ht.le,
    mul_rpow (by norm_num : (0 : ℝ) ≤ 160) hk0.le] at hh
  dsimp only [referenceCountCost]
  rw [he,show (61/10 : ℝ)=21/10+4 by norm_num,rpow_add ht,rpow_ofNat]
  dsimp only [buchstabCountLogConstant,B] at *
  convert hh using 1
  ring

lemma eventually_referenceCountCost_le_power (b : ℝ) (hb : 21/10 < b) :
    ∀ᶠ k : ℕ in atTop, referenceCountCost k ≤ (k : ℝ)^b := by
  let d := (b-21/10)/2
  have hd : 0 < d := by dsimp only [d]; linarith
  let C := 8*linearRefinementConstant*(160 : ℝ)^(21/10 : ℝ)*buchstabCountLogConstant
  let A := ((3 : ℝ)^(d/(61/10))/(d/(61/10)))^(61/10 : ℝ)
  have hC : 0 < C := by dsimp only [C]; exact mul_pos (mul_pos (mul_pos (by norm_num) linearRefinementConstant_pos)
    (rpow_pos_of_pos (by norm_num) _)) buchstabCountLogConstant_pos
  have hA : 0 < A := by dsimp only [A]; positivity
  have hp : Tendsto (fun k : ℕ => (k : ℝ)^d) atTop atTop :=
    (tendsto_rpow_atTop hd).comp tendsto_natCast_atTop_atTop
  filter_upwards [hp.eventually_ge_atTop (C*A),eventually_ge_atTop 1] with k hlarge hk
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hl := log_rpow_le_small_power (61/10) d (by norm_num) hd k (by omega)
  change log ((k : ℝ)+2)^(61/10 : ℝ) ≤ A*(k : ℝ)^d at hl
  have hh := (referenceCountCost_log_bound k (by omega)).trans
    (mul_le_mul_of_nonneg_left hl (by positivity : 0 ≤ C*(k : ℝ)^(21/10 : ℝ)))
  have hh' : referenceCountCost k ≤ (C*A)*(k : ℝ)^((21/10 : ℝ)+d) := by
    rw [rpow_add hk0]
    convert hh using 1
    ring
  apply hh'.trans
  have hmul := mul_le_mul_of_nonneg_right hlarge (rpow_nonneg hk0.le ((21/10 : ℝ)+d))
  have he : b = d+((21/10 : ℝ)+d) := by dsimp only [d]; ring
  rwa [← rpow_add hk0,← he] at hmul

/-- One absolute count denominator works for every exponent b>21/10.
Only the eventual budget threshold depends on b. -/
theorem eventually_prime_count_power (b : ℝ) (hb : 21/10 < b) :
    ∀ᶠ k : ℕ in atTop, ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → P.card ≤ k →
      ∀ r : ℕ → ℕ, ∀ m : ℕ, (k : ℝ)^b ≤ m →
        (m : ℝ)/(buchstabCountLogConstant*log ((k : ℝ)+2)) ≤
          (((range m).filter (fun j => ∀ p ∈ P, ¬j ≡ r p [MOD p])).card : ℝ) := by
  obtain ⟨N₀,hN₀⟩ := exists_referenceLower_one_positive
  obtain ⟨N₁,hN₁⟩ := eventually_atTop.mp eventually_eulerMass_initial_le_nine_fifths_log
  filter_upwards [eventually_referenceCountCost_le_power b hb,
    eventually_ge_atTop (max (max N₀ N₁) 1)] with k hcost hk
  intro P hP hPk r m hm
  have hkpos : 0 < k := by omega
  have hNp : max N₀ N₁ ≤ nthPrime k :=
    ((le_max_left _ _).trans hk).trans (nthPrime_strictMono.id_le k)
  have hp := nthPrime_prime k
  have hlogp : 0 < log (nthPrime k : ℝ) := log_pos (by exact_mod_cast hp.one_lt)
  have hEuler := (eulerMass_strict_prefix_le (nthPrime k) hp).trans
    (hN₁ (nthPrime k) ((le_max_right _ _).trans hNp))
  let D : ℝ := exp ((21/10 : ℝ)*log (nthPrime k : ℝ))
  let E : ℝ := 4*(1+prefixReciprocal nthPrime k)^3*D
  have hmain := hN₀ k ((le_max_left _ _).trans hNp)
  have hEu := eulerMass_pos (nthPrime k).primesBelow (fun q hq => (Nat.mem_primesBelow.mp hq).2)
  have hmainlog : 1/(360*log (nthPrime k : ℝ)) ≤ referenceLower 1 k D := by
    apply le_trans _ hmain
    rw [nthPrime_prefix_density,div_div]
    exact one_div_le_one_div_of_le (by positivity) (by nlinarith only [hEuler])
  have hE : E ≤ (m : ℝ)/(720*log (nthPrime k : ℝ)) := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 720*log (nthPrime k : ℝ))).mpr
    have hh := hcost.trans hm
    dsimp only [referenceCountCost,D,E] at *
    nlinarith only [hh]
  have hc := prime_count_of_linear_refinement P hP r k m hPk D (exp_pos _).le (primeKeep_exp k _ (by norm_num))
  have hmainm := mul_le_mul_of_nonneg_left hmainlog (Nat.cast_nonneg m)
  have hcount : (m : ℝ)/(720*log (nthPrime k : ℝ)) ≤
      (((range m).filter (fun j => ∀ p ∈ P, ¬j ≡ r p [MOD p])).card : ℝ) := by
    change (m : ℝ)*referenceLower 1 k D-E ≤ _ at hc
    have he : (m : ℝ)*(1/(360*log (nthPrime k : ℝ))) = 2*((m : ℝ)/(720*log (nthPrime k : ℝ))) := by ring
    rw [he] at hmainm
    linarith
  apply le_trans _ hcount
  apply div_le_div_of_nonneg_left (Nat.cast_nonneg m) (by positivity)
  have hh := nthPrime_log_upper k hkpos
  dsimp only [buchstabCountLogConstant]
  nlinarith only [hh]

#print axioms eventually_referenceCountCost_le_power
#print axioms eventually_prime_count_power
end Erdos970.RecursiveSieve.Buchstab
