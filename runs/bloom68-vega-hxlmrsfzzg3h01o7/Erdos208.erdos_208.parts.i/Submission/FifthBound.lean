import Submission.FifthInterval
import Submission.Reduction

/-!
# Squarefree gaps for every exponent greater than one fifth

The finite FT interval estimate implies polynomial-scale interval estimates
with exponents `(r + 1) / (5 * r)`. Letting the fixed integer `r` grow proves
the gap bound for every exponent strictly greater than one fifth. No assertion
is made for smaller positive exponents or at the endpoint one fifth.
-/

open Filter Real

namespace FifthInterval

/-- A fixed polynomial is eventually bounded by `16^h`. -/
lemma eventually_pow_le_sixteen (k : ℕ) : ∀ᶠ h : ℕ in atTop, h ^ k ≤ 16 ^ h := by
  have hb := (isLittleO_pow_const_const_pow_of_one_lt (R := ℝ) k
    (by norm_num : (1 : ℝ) < 16)).bound (by norm_num : (0 : ℝ) < 1)
  filter_upwards [hb] with h hh
  simp only [Real.norm_eq_abs, abs_of_nonneg (show (0 : ℝ) ≤ (h : ℝ) ^ k by positivity),
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ 16 ^ h), one_mul] at hh
  exact_mod_cast hh

/-- Polynomial-scale intervals following from the finite FT parameters. -/
theorem exists_squarefree_polynomial_intervals (r : ℕ) :
    ∃ h₀ : ℕ, ∀ h ≥ h₀, ∀ x : ℕ, x ≤ h ^ (5 * r) →
      ∃ n : ℕ, x < n ∧ n ≤ x + 4096 * h ^ (r + 1) ∧ Squarefree n := by
  obtain ⟨H₀, hH₀⟩ := exists_squarefree_in_fifth_interval
  obtain ⟨h₁, hh₁⟩ := eventually_atTop.mp (eventually_pow_le_sixteen (5 * r))
  refine ⟨max 1 (max H₀ h₁), ?_⟩
  intro h hh x hx
  have hhpos : 0 < h := by omega
  have hHpos : 0 < 4096 * h ^ (r + 1) := by positivity
  have hhH : h ≤ 4096 * h ^ (r + 1) :=
    (Nat.le_self_pow (by omega) h).trans (Nat.le_mul_of_pos_left _ (by decide))
  have hlength : 2048 * h ^ r * (h + 1) ≤ 4096 * h ^ (r + 1) := by
    calc
      2048 * h ^ r * (h + 1) ≤ 2048 * h ^ r * (2 * h) := by gcongr; omega
      _ = 4096 * h ^ (r + 1) := by rw [pow_succ]; ring
  have hpow : h ^ (5 * r) ≤ 16 ^ h := hh₁ h (by omega)
  have hterminal : x + 4096 * h ^ (r + 1) <
      FTParameters.A * (4096 * h ^ (r + 1)) * 16 ^ h := by
    have hge : 1 ≤ 16 ^ h := Nat.one_le_pow _ _ (by decide)
    calc
      x + 4096 * h ^ (r + 1) ≤ 16 ^ h + 4096 * h ^ (r + 1) := by omega
      _ ≤ 2 * (4096 * h ^ (r + 1)) * 16 ^ h := by nlinarith
      _ < FTParameters.A * (4096 * h ^ (r + 1)) * 16 ^ h :=
        Nat.mul_lt_mul_of_pos_right
          (Nat.mul_lt_mul_of_pos_right (by norm_num [FTParameters.A]) hHpos) (by positivity)
  apply hH₀ x (4096 * h ^ (r + 1)) (h ^ r) h (by omega) (by positivity) ?_
    hlength hterminal
  simpa only [← pow_mul, Nat.mul_comm r 5] using hx

end FifthInterval

namespace SquarefreeGaps

/-- Transfer a uniform polynomial interval estimate to its exact real exponent. -/
lemma intervalBound_of_polynomial_intervals {a b C : ℕ} (ha : 0 < a) (hC : 0 < C)
    (hinterval : ∃ h₀ : ℕ, ∀ h ≥ h₀, ∀ x : ℕ, x ≤ h ^ a →
      ∃ n : ℕ, x < n ∧ n ≤ x + C * h ^ b ∧ Squarefree n) :
    IntervalBound ((b : ℝ) / a) := by
  obtain ⟨h₀, hh₀⟩ := hinterval
  let f : ℕ → ℝ := fun x => (x : ℝ) ^ (a : ℝ)⁻¹
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hf : Tendsto f atTop atTop :=
    (tendsto_rpow_atTop (inv_pos.mpr haR)).comp tendsto_natCast_atTop_atTop
  have hh : Tendsto (fun x => ⌈f x⌉₊) atTop atTop := tendsto_nat_ceil_atTop.comp hf
  refine ⟨(C : ℝ) * 2 ^ b, by positivity, ?_⟩
  filter_upwards [hh.eventually (eventually_ge_atTop h₀), eventually_ge_atTop (1 : ℕ)]
    with x hxh₀ hx1
  have hxR : (1 : ℝ) ≤ x := by exact_mod_cast hx1
  have hfx : 1 ≤ f x := Real.one_le_rpow hxR (inv_pos.mpr haR).le
  have hceil : f x ≤ (⌈f x⌉₊ : ℝ) := Nat.le_ceil _
  have hceil2 : (⌈f x⌉₊ : ℝ) ≤ 2 * f x := by
    have hh' := Nat.ceil_lt_add_one (show 0 ≤ f x by linarith)
    linarith
  have hroot : (f x) ^ a = (x : ℝ) := by
    exact Real.rpow_inv_natCast_pow (Nat.cast_nonneg x) ha.ne'
  have hxpow : x ≤ ⌈f x⌉₊ ^ a := by
    have hp := pow_le_pow_left₀ (show 0 ≤ f x by linarith) hceil a
    rw [hroot] at hp
    exact_mod_cast hp
  obtain ⟨n, hxn, hn, hsq⟩ := hh₀ ⌈f x⌉₊ hxh₀ x hxpow
  refine ⟨n, hsq, hxn, ?_⟩
  have hnR : (n : ℝ) ≤ (x : ℝ) + (C : ℝ) * (⌈f x⌉₊ : ℝ) ^ b := by
    exact_mod_cast hn
  have hfpow : (f x) ^ b = (x : ℝ) ^ ((b : ℝ) / a) := by
    dsimp only [f]
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg x)]
    congr 1
    ring
  calc
    (n - x : ℝ) ≤ (C : ℝ) * (⌈f x⌉₊ : ℝ) ^ b := by linarith
    _ ≤ (C : ℝ) * (2 * f x) ^ b := by gcongr
    _ = (C : ℝ) * 2 ^ b * (x : ℝ) ^ ((b : ℝ) / a) := by rw [mul_pow, hfpow]; ring

lemma intervalBound_mono {α β : ℝ} (hαβ : α ≤ β) (hα : IntervalBound α) :
    IntervalBound β := by
  obtain ⟨C, hC, hb⟩ := hα
  refine ⟨C, hC, ?_⟩
  filter_upwards [hb, eventually_ge_atTop (1 : ℕ)] with x hx hx1
  obtain ⟨n, hsq, hxn, hn⟩ := hx
  refine ⟨n, hsq, hxn, hn.trans ?_⟩
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hx1) hαβ) hC.le

/-- The rigorously proved partial squarefree-gap bound: every `ε > 1/5`. -/
theorem gapBound_of_fifth_lt {ε : ℝ} (hε : (1 : ℝ) / 5 < ε) : GapBound ε := by
  have hδ : 0 < 5 * ε - 1 := by linarith
  obtain ⟨r, hr⟩ := exists_nat_gt (max 1 ((5 * ε - 1)⁻¹))
  have hr1 : (1 : ℝ) < r := (le_max_left _ _).trans_lt hr
  have hr0 : 0 < r := by exact_mod_cast (zero_lt_one.trans hr1)
  have hrδ : (5 * ε - 1)⁻¹ < (r : ℝ) := (le_max_right _ _).trans_lt hr
  have hmul : 1 < (r : ℝ) * (5 * ε - 1) := (inv_lt_iff_one_lt_mul₀ hδ).mp hrδ
  have hratio : ((r + 1 : ℕ) : ℝ) / ((5 * r : ℕ) : ℝ) ≤ ε := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < ((5 * r : ℕ) : ℝ))).mpr
    push_cast
    nlinarith
  apply gap_of_interval
  apply intervalBound_mono hratio
  exact intervalBound_of_polynomial_intervals (by omega) (by decide)
    (FifthInterval.exists_squarefree_polynomial_intervals r)

#print axioms gapBound_of_fifth_lt

end SquarefreeGaps
