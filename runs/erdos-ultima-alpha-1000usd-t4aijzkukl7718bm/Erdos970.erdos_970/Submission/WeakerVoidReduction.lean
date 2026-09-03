import Submission.ExponentialVoidReduction

/-!
Weaker sufficient void-tail estimates for the quadratic Jacobsthal conjecture.
All tail estimates in this file are explicit hypotheses. No unconditional
quadratic theorem or tail estimate is asserted.
-/
namespace Erdos970.GapAverages
open Finset Real Filter

/-- A budget-uniform polylogarithmic void estimate. The exponent `B` is fixed,
not allowed to depend on the prime budget. -/
def PolylogVoidBound (c : ℝ) (B : ℕ) : Prop :=
  ∀ (P : Finset ℕ), (∀ p ∈ P, p.Prime) → ∀ k : ℕ, P.card ≤ k → ∀ m : ℕ,
    coveredFraction P m ≤ exp (-(c * (m : ℝ) / log ((k : ℝ) + 2) ^ B))

lemma eventually_log_power_entropy_small {c : ℝ} (hc : 0 < c) (B : ℕ) :
    ∀ᶠ k : ℕ in atTop, 12 * log ((k : ℝ) + 2) ^ (B + 1) < c * k := by
  have ht : Tendsto (fun k : ℕ => (k : ℝ) + 2) atTop atTop :=
    tendsto_atTop_mono (fun k => by linarith : ∀ k : ℕ, (k : ℝ) ≤ (k : ℝ) + 2)
      tendsto_natCast_atTop_atTop
  have hl : Tendsto (fun k : ℕ => log ((k : ℝ) + 2) ^ (B + 1) / k) atTop (nhds 0) := by
    convert (tendsto_pow_log_div_mul_add_atTop 1 (-2) (B + 1) (by norm_num)).comp ht using 1 <;>
      simp [Function.comp_def]
  have he := hl.eventually (gt_mem_nhds (show 0 < c / 12 by positivity))
  filter_upwards [he, eventually_ge_atTop 1] with k hk hk1
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hh := (div_lt_iff₀ hk0).mp hk
  linarith

/-- Any fixed polylogarithmic loss in an exponential tail is still sufficient
for the eventual unit-constant quadratic bound. -/
theorem eventually_quadratic_of_polylog_void {c : ℝ} (hc : 0 < c) (B : ℕ)
    (htail : PolylogVoidBound c B) :
    ∀ᶠ k : ℕ in atTop, jacobsthalFunction k ≤ k ^ 2 := by
  filter_upwards [eventually_log_power_entropy_small hc B, eventually_ge_atTop 1]
    with k hsmall hk1
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hy : (1 : ℝ) < (k : ℝ) + 2 := by linarith
  have hlog : 0 < log ((k : ℝ) + 2) := log_pos hy
  have hpow : 0 < log ((k : ℝ) + 2) ^ B := pow_pos hlog _
  apply (jacobsthalFunction_le_iff k (k ^ 2)).mpr
  by_contra hbad
  obtain ⟨P, hP, hPk, r, hcov⟩ := (not_isJacobsthalBound_iff_cover k (k ^ 2)).mp hbad
  obtain ⟨Q, s, hQ, hQk, hcap, hcov'⟩ := BoundedPrimeCover.normalize hP hPk hcov
  have hbudget : (k : ℝ) * log (((k : ℝ) + 2) ^ 12) <
      c * (k : ℝ) ^ 2 / log ((k : ℝ) + 2) ^ B := by
    apply (lt_div_iff₀ hpow).mpr
    rw [log_pow]
    norm_num only [Nat.cast_ofNat]
    have hh := mul_lt_mul_of_pos_left hsmall hk0
    rw [pow_succ] at hh
    nlinarith only [hh]
  have htail' : coveredFraction Q (k ^ 2) ≤
      exp (-(c * (k : ℝ) ^ 2 / log ((k : ℝ) + 2) ^ B)) := by
    have hh := htail Q hQ k hQk (k ^ 2)
    change coveredFraction Q (k ^ 2) ≤
      exp (-(c * ((k ^ 2 : ℕ) : ℝ) / log ((k : ℝ) + 2) ^ B)) at hh
    simpa only [Nat.cast_pow] using hh
  obtain ⟨x, hx, hxa⟩ := survivor_of_exponential_tail_of_cap hQ hQk
    (one_le_pow₀ hy.le) (fun q hq => quadratic_cap (hcap q hq)) htail' hbudget s
  obtain ⟨q, hq, hxq⟩ := hcov' x hx
  exact hxa q hq hxq

/-- Patch finitely many budgets in an eventual polynomial estimate. -/
lemma quadratic_bound_of_eventually_scaled {D : ℕ} (hD : 0 < D)
    (h : ∀ᶠ k : ℕ in atTop, jacobsthalFunction k ≤ D * k ^ 2) :
    ∃ C > (0 : ℝ), ∀ k : ℕ, 0 < k →
      (jacobsthalFunction k : ℝ) ≤ C * k ^ 2 := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp h
  refine ⟨(jacobsthalFunction N : ℝ) + D, by positivity, fun k hk => ?_⟩
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk2 : (1 : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith
  have hn : (0 : ℝ) ≤ jacobsthalFunction N := Nat.cast_nonneg _
  have hd : (0 : ℝ) < D := by exact_mod_cast hD
  by_cases hNk : N ≤ k
  · have hh : (jacobsthalFunction k : ℝ) ≤ D * (k : ℝ) ^ 2 := by exact_mod_cast hN k hNk
    nlinarith
  · have hh : (jacobsthalFunction k : ℝ) ≤ jacobsthalFunction N := by
      exact_mod_cast jacobsthalFunction_strictMono.monotone (show k ≤ N by omega)
    nlinarith

theorem quadratic_bound_of_polylog_void {c : ℝ} (hc : 0 < c) (B : ℕ)
    (htail : PolylogVoidBound c B) :
    ∃ C > (0 : ℝ), ∀ k : ℕ, 0 < k →
      (jacobsthalFunction k : ℝ) ≤ C * k ^ 2 := by
  apply quadratic_bound_of_eventually_scaled (D := 1) (by omega)
  simpa only [one_mul] using eventually_quadratic_of_polylog_void hc B htail

/-- An even weaker candidate, at the critical cardinality rate. Unlike the
polylogarithmic candidate, its rate can be as small as a constant times log k/k. -/
def CriticalVoidBound (c : ℝ) : Prop :=
  ∀ (P : Finset ℕ), (∀ p ∈ P, p.Prime) → ∀ k : ℕ, P.card ≤ k → ∀ m : ℕ,
    coveredFraction P m ≤ exp (-(c * (m : ℝ) * log ((k : ℝ) + 2) / ((k : ℝ) + 1)))

lemma scaled_quadratic_cap {D k q : ℕ} (hDk : D ≤ k)
    (hq : q ≤ 256 * (D * k ^ 2 + k + 1) ^ 2) :
    (q : ℝ) ≤ ((k : ℝ) + 2) ^ 14 := by
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have hDk' : (D : ℝ) ≤ k := by exact_mod_cast hDk
  have h2 : (2 : ℝ) ≤ (k : ℝ) + 2 := by linarith
  have h256 : (256 : ℝ) ≤ ((k : ℝ) + 2) ^ 8 := by
    convert pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) h2 8 using 1 <;> norm_num
  have hm : (D : ℝ) * (k : ℝ) ^ 2 ≤ (k : ℝ) ^ 3 := by
    nlinarith [mul_le_mul_of_nonneg_right hDk' (sq_nonneg (k : ℝ))]
  have hbase : (D : ℝ) * (k : ℝ) ^ 2 + k + 1 ≤ ((k : ℝ) + 2) ^ 3 := by
    nlinarith [sq_nonneg (k : ℝ)]
  have hsq := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (D : ℝ) * (k : ℝ) ^ 2 + k + 1) hbase 2
  calc
    (q : ℝ) ≤ 256 * ((D : ℝ) * (k : ℝ) ^ 2 + k + 1) ^ 2 := by exact_mod_cast hq
    _ ≤ ((k : ℝ) + 2) ^ 8 * (((k : ℝ) + 2) ^ 3) ^ 2 :=
      mul_le_mul h256 hsq (by positivity) (by positivity)
    _ = ((k : ℝ) + 2) ^ 14 := by ring

/-- A critical-rate void estimate would suffice with a constant-factor
quadratic interval, rather than with the unit constant. -/
theorem eventually_scaled_quadratic_of_critical_void {c : ℝ} (hc : 0 < c)
    (htail : CriticalVoidBound c) (D : ℕ) (hD : 28 < c * D) :
    ∀ᶠ k : ℕ in atTop, jacobsthalFunction k ≤ D * k ^ 2 := by
  filter_upwards [eventually_ge_atTop (max D 1)] with k hk
  have hDk : D ≤ k := (le_max_left _ _).trans hk
  have hk1 : 1 ≤ k := (le_max_right _ _).trans hk
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hk0 : (0 : ℝ) < k := by linarith
  have hy : (1 : ℝ) < (k : ℝ) + 2 := by linarith
  have hlog : 0 < log ((k : ℝ) + 2) := log_pos hy
  apply (jacobsthalFunction_le_iff k (D * k ^ 2)).mpr
  by_contra hbad
  obtain ⟨P, hP, hPk, r, hcov⟩ := (not_isJacobsthalBound_iff_cover k (D * k ^ 2)).mp hbad
  obtain ⟨Q, s, hQ, hQk, hcap, hcov'⟩ := BoundedPrimeCover.normalize hP hPk hcov
  have hbudget : (k : ℝ) * log (((k : ℝ) + 2) ^ 14) <
      c * ((D : ℝ) * (k : ℝ) ^ 2) * log ((k : ℝ) + 2) / ((k : ℝ) + 1) := by
    apply (lt_div_iff₀ (show 0 < (k : ℝ) + 1 by positivity)).mpr
    rw [log_pow]
    norm_num only [Nat.cast_ofNat]
    have ha : 14 * ((k : ℝ) + 1) < c * D * k := by
      have hh := mul_lt_mul_of_pos_right hD hk0
      linarith
    have hh := mul_lt_mul_of_pos_right ha (mul_pos hk0 hlog)
    nlinarith only [hh]
  have htail' : coveredFraction Q (D * k ^ 2) ≤
      exp (-(c * ((D : ℝ) * (k : ℝ) ^ 2) * log ((k : ℝ) + 2) / ((k : ℝ) + 1))) := by
    have hh := htail Q hQ k hQk (D * k ^ 2)
    change coveredFraction Q (D * k ^ 2) ≤
      exp (-(c * ((D * k ^ 2 : ℕ) : ℝ) * log ((k : ℝ) + 2) / ((k : ℝ) + 1))) at hh
    simpa only [Nat.cast_pow, Nat.cast_mul] using hh
  obtain ⟨x, hx, hxa⟩ := survivor_of_exponential_tail_of_cap hQ hQk
    (one_le_pow₀ hy.le) (fun q hq => scaled_quadratic_cap hDk (hcap q hq)) htail' hbudget s
  obtain ⟨q, hq, hxq⟩ := hcov' x hx
  exact hxa q hq hxq

/-- The critical-rate estimate is sufficient for exactly the original real
quadratic conclusion, while remaining an explicit unproved hypothesis. -/
theorem quadratic_bound_of_critical_void {c : ℝ} (hc : 0 < c)
    (htail : CriticalVoidBound c) :
    ∃ C > (0 : ℝ), ∀ k : ℕ, 0 < k →
      (jacobsthalFunction k : ℝ) ≤ C * k ^ 2 := by
  obtain ⟨D, hD⟩ := exists_nat_gt (28 / c)
  have hD' : 28 < c * D := by
    have hh := (div_lt_iff₀ hc).mp hD
    linarith
  have hDpos : 0 < D := by
    by_contra hn
    have hz : D = 0 := by omega
    norm_num [hz] at hD'
  exact quadratic_bound_of_eventually_scaled hDpos
    (eventually_scaled_quadratic_of_critical_void hc htail D hD')

#print axioms quadratic_bound_of_polylog_void
#print axioms quadratic_bound_of_critical_void
end Erdos970.GapAverages
