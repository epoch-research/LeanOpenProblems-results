import Submission.FirstHitIntegerCutoff

/-! Extension of the medium reciprocal estimate to ratios at least three fifths. -/
namespace Erdos970.FiniteSelberg
open Finset Real

lemma firstHitFullProfile_ge_three_fifths (u : ℝ) (hu : 3 / 5 ≤ u) (hu3 : u ≤ 3) :
    3 / 5 ≤ firstHitFullProfile u := by
  unfold firstHitFullProfile
  split_ifs with hu1
  · exact hu
  · exact (by norm_num : (3 / 5 : ℝ) ≤ 1).trans (firstHitProfile_ge_one u ⟨by linarith, hu3⟩)

/-- The integer ceiling perturbs the middle-range normalizer only by an
absolute additive error. -/
theorem firstHitCutoff_normalizer_lower_three_fifths (L u : ℝ) (p : ℕ) (hp : p.Prime)
    (hLp : 1 ≤ log (p : ℝ)) (hu : 3 / 5 ≤ u) (hu3 : u ≤ 3)
    (harg : (L - log (p : ℝ)) / 2 = u * log p) :
    firstHitFullProfile u * log p - firstHitProfileError ≤
      primeNormalizer p.primesBelow (firstHitCutoff L p) := by
  let N := firstHitCutoff L p
  have hN := firstHitCutoff_pos L p
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hpp : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hLp0 : 0 < log (p : ℝ) := by linarith
  have hlow := firstHitCutoff_log_lower L p
  rw [harg] at hlow
  have hL : log (p : ℝ) ≤ L := by nlinarith
  have hupp := firstHitCutoff_log_upper L p hL
  rw [harg] at hupp
  change u * log p ≤ log (N : ℝ) at hlow
  change log (N : ℝ) ≤ u * log p + log 2 at hupp
  by_cases hu1 : u ≤ 1
  · have hNp' : N ≤ p := by
      have hh := firstHitCutoff_le_power L p 1 hp.pos (by rw [harg]; norm_num; nlinarith)
      simpa using hh
    have hHN : (harmonic N : ℝ) ≤ primeNormalizer (p + 1).primesBelow N :=
      harmonic_le_smallDivisorFamily _ (fun q hq => (WeightedMertens.mem_primes.mp hq).1) N
        (fun q hq hqN => WeightedMertens.mem_primes.mpr ⟨hq, hqN.trans hNp'⟩)
    have hh := log_le_harmonic_floor (N : ℝ) hNp.le
    rw [Nat.floor_natCast] at hh
    have hmul := mul_le_mul_of_nonneg_left (hh.trans hHN) (prime_density_pos hp).le
    have hn := normalizer_strict_prefix_ge (N := N) hp
    have hlogp := log_le_log hNp (show (N : ℝ) ≤ p by exact_mod_cast hNp')
    have hquot : log (N : ℝ) / (p : ℝ) ≤ 1 := by
      apply (div_le_iff₀ hpp).mpr
      linarith [log_le_sub_one_of_pos hpp]
    have he : (1 - 1 / (p : ℝ)) * log (N : ℝ) = log (N : ℝ) - log (N : ℝ) / p := by ring
    rw [he] at hmul
    unfold firstHitFullProfile
    rw [if_pos hu1]
    linarith [firstHitProfileError_ge_one]
  · let v := log (N : ℝ) / log (p : ℝ)
    have hvu : u ≤ v := (le_div_iff₀ hLp0).mpr hlow
    have hv1 : 1 ≤ v := by linarith
    have hNcube : N ≤ p ^ 3 := firstHitCutoff_le_power L p 3 hp.pos (by rw [harg]; norm_num; nlinarith)
    have hv3 : v ≤ 3 := by
      apply (div_le_iff₀ hLp0).mpr
      have hh := log_le_log hNp (show (N : ℝ) ≤ (p : ℝ) ^ 3 by exact_mod_cast hNcube)
      simpa only [log_pow, Nat.cast_ofNat] using hh
    have hlog : log (N : ℝ) = v * log (p : ℝ) := by dsimp [v]; field_simp
    have hpN : p ≤ N := by
      have hh : log (p : ℝ) ≤ log (N : ℝ) := by nlinarith
      exact_mod_cast (log_le_log_iff hpp hNp).mp hh
    have hn := strict_normalizer_lower_through_cube p N hp hpN hLp v hv1 hv3 hlog
    have hdrop := mul_le_mul_of_nonneg_right (firstHitProfile_drop_le u v (by linarith) hvu hv3) hLp0.le
    have hpert : (v - u) * log (p : ℝ) ≤ log 2 := by rw [hlog] at hupp; nlinarith only [hupp]
    have hl2 : log (2 : ℝ) ≤ 1 := by linarith [log_two_lt_d9]
    unfold firstHitFullProfile
    rw [if_neg hu1]
    unfold firstHitProfileError
    change firstHitProfile v * log (p : ℝ) - _ - 3 ≤ _ at hn
    nlinarith only [hn, hdrop, hpert, hl2]

lemma reciprocal_of_additive_profile_three_fifths (g G T K : ℝ) (hg : 3 / 5 ≤ g)
    (hK : 0 < K) (hT : 20000 * K ≤ T) (hG : g * T - K ≤ G) :
    0 < G ∧ 1 / G ≤ (10001 / 10000 : ℝ) * (1 / (g * T)) := by
  have hTp : 0 < T := by linarith
  have hgp : 0 < g := by linarith
  have hmul := mul_le_mul_of_nonneg_right hg hTp.le
  have hprod : 10001 * K ≤ g * T := by linarith
  have hGp : 0 < G := by nlinarith
  refine ⟨hGp, ?_⟩
  apply (div_le_iff₀ hGp).mpr
  apply (mul_le_mul_iff_right₀ (show 0 < g * T by positivity)).mp
  field_simp
  nlinarith only [hG, hprod]

/-- A uniform multiplicative reciprocal estimate on the full medium range,
including the integral cutoff and the explicit threshold for the additive error. -/
theorem firstHitCutoff_reciprocal_upper_three_fifths (L u : ℝ) (p : ℕ) (hp : p.Prime)
    (hLp : 20000 * firstHitProfileError ≤ log (p : ℝ))
    (hu : 3 / 5 ≤ u) (hu3 : u ≤ 3)
    (harg : (L - log (p : ℝ)) / 2 = u * log p) :
    0 < primeNormalizer p.primesBelow (firstHitCutoff L p) ∧
    1 / primeNormalizer p.primesBelow (firstHitCutoff L p) ≤
      (10001 / 10000 : ℝ) * (1 / firstHitFullProfile u) / log p := by
  have hK : 0 < firstHitProfileError := lt_of_lt_of_le (by norm_num) firstHitProfileError_ge_one
  have hLp1 : 1 ≤ log (p : ℝ) := by linarith [firstHitProfileError_ge_one]
  have hh := reciprocal_of_additive_profile_three_fifths (firstHitFullProfile u) _ (log (p : ℝ))
    firstHitProfileError (firstHitFullProfile_ge_three_fifths u hu hu3) hK hLp
    (firstHitCutoff_normalizer_lower_three_fifths L u p hp hLp1 hu hu3 harg)
  convert hh using 1 <;> ring


#print axioms firstHitCutoff_reciprocal_upper_three_fifths
end Erdos970.FiniteSelberg
