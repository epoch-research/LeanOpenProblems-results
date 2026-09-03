import Submission.FirstHitIntegral

/-! Integer cutoffs for the variable-cutoff first-hit construction. Ceilings
preserve the Rankin direction and cost at most a factor four. -/
namespace Erdos970.FiniteSelberg
open Finset Real

noncomputable def firstHitCutoff (L : ℝ) (p : ℕ) : ℕ :=
  ⌈exp ((L - log (p : ℝ)) / 2)⌉₊

lemma firstHitCutoff_pos (L : ℝ) (p : ℕ) : 0 < firstHitCutoff L p :=
  Nat.ceil_pos.mpr (exp_pos _)

lemma firstHitCutoff_log_lower (L : ℝ) (p : ℕ) :
    (L - log (p : ℝ)) / 2 ≤ log (firstHitCutoff L p : ℝ) := by
  have hh := log_le_log (exp_pos ((L - log (p : ℝ)) / 2))
    (Nat.le_ceil (exp ((L - log (p : ℝ)) / 2)))
  simpa only [log_exp] using hh

lemma firstHitCutoff_log_upper (L : ℝ) (p : ℕ) (hL : log (p : ℝ) ≤ L) :
    log (firstHitCutoff L p : ℝ) ≤ (L - log (p : ℝ)) / 2 + log 2 := by
  have he : 1 ≤ exp ((L - log (p : ℝ)) / 2) := one_le_exp (by linarith)
  have hh := Nat.ceil_lt_add_one (exp_pos ((L - log (p : ℝ)) / 2)).le
  have hn : (firstHitCutoff L p : ℝ) ≤ 2 * exp ((L - log (p : ℝ)) / 2) := by
    change (⌈exp ((L - log (p : ℝ)) / 2)⌉₊ : ℝ) ≤ _
    linarith
  have hnp : (0 : ℝ) < firstHitCutoff L p := by exact_mod_cast firstHitCutoff_pos L p
  have hlog := log_le_log hnp hn
  rw [log_mul (by norm_num) (exp_pos _).ne', log_exp] at hlog
  linarith

lemma firstHitCutoff_sq_le (L : ℝ) (p : ℕ) (hp : 0 < p) (hL : log (p : ℝ) ≤ L) :
    (firstHitCutoff L p : ℝ) ^ 2 ≤ 4 * exp L / p := by
  have he : 1 ≤ exp ((L - log (p : ℝ)) / 2) := one_le_exp (by linarith)
  have hh := Nat.ceil_lt_add_one (exp_pos ((L - log (p : ℝ)) / 2)).le
  have hn : (firstHitCutoff L p : ℝ) ≤ 2 * exp ((L - log (p : ℝ)) / 2) := by
    change (⌈exp ((L - log (p : ℝ)) / 2)⌉₊ : ℝ) ≤ _
    linarith
  have hs := pow_le_pow_left₀ (Nat.cast_nonneg (firstHitCutoff L p)) hn 2
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hid : (2 * exp ((L - log (p : ℝ)) / 2)) ^ 2 = 4 * exp L / p := by
    rw [mul_pow, ← exp_nat_mul]
    norm_num only [Nat.cast_ofNat]
    rw [show 2 * ((L - log (p : ℝ)) / 2) = L - log (p : ℝ) by ring,
      exp_sub, exp_log hp0]
    ring
  rwa [hid] at hs

lemma firstHitCutoff_le_power (L : ℝ) (p n : ℕ) (hp : 0 < p)
    (hL : (L - log (p : ℝ)) / 2 ≤ (n : ℝ) * log p) : firstHitCutoff L p ≤ p ^ n := by
  apply Nat.ceil_le.mpr
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  calc
    _ ≤ exp ((n : ℝ) * log p) := exp_le_exp.mpr hL
    _ = (p ^ n : ℕ) := by rw [exp_nat_mul, exp_log hp0, Nat.cast_pow]

lemma firstHitProfile_drop_le (u v : ℝ) (hu : 1 ≤ u) (huv : u ≤ v) (hv : v ≤ 3) :
    firstHitProfile u - (v - u) ≤ firstHitProfile v := by
  have hu0 : 0 < u := by linarith
  have hv0 : 0 < v := by linarith
  have hlv : log v ≤ 2 := by linarith [log_le_sub_one_of_pos hv0]
  have hh := log_le_sub_one_of_pos (div_pos hv0 hu0)
  rw [log_div hv0.ne' hu0.ne'] at hh
  have hmul := mul_le_mul_of_nonneg_left hh hu0.le
  have hdiv : u * (v / u - 1) = v - u := by field_simp
  rw [hdiv] at hmul
  have hmul' := mul_le_mul_of_nonneg_left hlv (sub_nonneg.mpr huv)
  unfold firstHitProfile
  nlinarith only [hmul, hmul']

lemma firstHitProfile_ge_one (u : ℝ) (hu : u ∈ Set.Icc 1 3) : 1 ≤ firstHitProfile u := by
  have hl3 : log (3 : ℝ) ≤ 4 / 3 := by
    have hh := sum_range_sub_log_div_le (x := (1 / 2 : ℝ)) (by norm_num) 3
    norm_num [sum_range_succ] at hh
    linarith only [(abs_le.mp hh).2]
  have hg3 : 1 ≤ firstHitProfile 3 := by unfold firstHitProfile; linarith
  have hg1 : firstHitProfile 1 = 1 := by norm_num [firstHitProfile]
  have ha : 0 ≤ (3 - u) / 2 := by linarith [hu.2]
  have hb : 0 ≤ (u - 1) / 2 := by linarith [hu.1]
  have hh := firstHitProfile_concave.2
    (by norm_num : (1 : ℝ) ∈ Set.Icc 1 3) (by norm_num : (3 : ℝ) ∈ Set.Icc 1 3)
    ha hb (show (3 - u) / 2 + (u - 1) / 2 = 1 by ring)
  simp only [smul_eq_mul, hg1] at hh
  rw [show (3 - u) / 2 * 1 + (u - 1) / 2 * 3 = u by ring] at hh
  have hh' := mul_le_mul_of_nonneg_left hg3 hb
  linarith

noncomputable def firstHitFullProfile (u : ℝ) : ℝ :=
  if u ≤ 1 then u else firstHitProfile u

noncomputable def firstHitProfileError : ℝ := 12 * (WeightedMertens.boundConstant + 1) + 4

lemma firstHitProfileError_ge_one : 1 ≤ firstHitProfileError := by
  unfold firstHitProfileError
  linarith [WeightedMertens.boundConstant_pos]

lemma firstHitFullProfile_ge (u : ℝ) (hu : 7 / 10 ≤ u) (hu3 : u ≤ 3) :
    7 / 10 ≤ firstHitFullProfile u := by
  unfold firstHitFullProfile
  split_ifs with hu1
  · exact hu
  · exact (by norm_num : (7 / 10 : ℝ) ≤ 1).trans (firstHitProfile_ge_one u ⟨by linarith, hu3⟩)

/-- The integer ceiling perturbs the middle-range normalizer only by an
absolute additive error. -/
theorem firstHitCutoff_normalizer_lower (L u : ℝ) (p : ℕ) (hp : p.Prime)
    (hLp : 1 ≤ log (p : ℝ)) (hu : 7 / 10 ≤ u) (hu3 : u ≤ 3)
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

lemma reciprocal_of_additive_profile (g G T K : ℝ) (hg : 7 / 10 ≤ g)
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
theorem firstHitCutoff_reciprocal_upper (L u : ℝ) (p : ℕ) (hp : p.Prime)
    (hLp : 20000 * firstHitProfileError ≤ log (p : ℝ))
    (hu : 7 / 10 ≤ u) (hu3 : u ≤ 3)
    (harg : (L - log (p : ℝ)) / 2 = u * log p) :
    0 < primeNormalizer p.primesBelow (firstHitCutoff L p) ∧
    1 / primeNormalizer p.primesBelow (firstHitCutoff L p) ≤
      (10001 / 10000 : ℝ) * (1 / firstHitFullProfile u) / log p := by
  have hK : 0 < firstHitProfileError := lt_of_lt_of_le (by norm_num) firstHitProfileError_ge_one
  have hLp1 : 1 ≤ log (p : ℝ) := by linarith [firstHitProfileError_ge_one]
  have hh := reciprocal_of_additive_profile (firstHitFullProfile u) _ (log (p : ℝ))
    firstHitProfileError (firstHitFullProfile_ge u hu hu3) hK hLp
    (firstHitCutoff_normalizer_lower L u p hp hLp1 hu hu3 harg)
  convert hh using 1 <;> ring

#print axioms firstHitCutoff_sq_le
#print axioms firstHitCutoff_reciprocal_upper
end Erdos970.FiniteSelberg
