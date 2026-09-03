import Submission.RationalSmoothMultiplicity

/-!
# Quantitative power-series transfer for smooth shifted primes

These implications sharpen the consequences of a hypothetical fixed power
bound for inverse-totient multiplicity. They do not establish such a bound,
or an unconditional contradiction to it.
-/

open Nat Filter
open scoped Classical

namespace Erdos821

set_option maxHeartbeats 2000000

lemma rational_power_nonsummability_supplies_dyadic_family
    (a b k c : ℕ) (ha : 0 < a) (hb : 0 < b) (hk : 0 < k)
    (s : ℝ) (hs : 0 ≤ s) (hc : (c : ℝ) < (a * k : ℕ) * s)
    (H : ¬Summable ((rationalSmoothShiftedPrimes a b).indicator
      (fun p : ℕ => (p : ℝ) ^ (-s)))) (M : ℕ) :
    ∃ L : ℕ, M ≤ L ∧ ∃ P : Finset ℕ,
      (∀ p ∈ P, p.Prime ∧ p ≤ 2 ^ (a * k * L) ∧
        p - 1 ∈ Nat.smoothNumbers (2 ^ (b * k * L))) ∧
      2 ^ (c * L) ≤ P.card := by
  obtain ⟨L, hML, hcount⟩ := exists_large_dyadic_count_of_not_summable
    (rationalSmoothShiftedPrimes a b) (a * k) c s
    (Nat.mul_pos ha hk) hs hc H M
  let P := (Finset.range (2 ^ (a * k * L))).filter
    (fun p => p ∈ rationalSmoothShiftedPrimes a b)
  refine ⟨L, hML, P, ?_, hcount⟩
  intro p hp
  obtain ⟨hpL, hpS⟩ := Finset.mem_filter.mp hp
  have hpbound := Finset.mem_range.mp hpL
  exact ⟨hpS.1, hpbound.le,
    rational_smooth_prime_mem_dyadic_smooth ha hb hpS hpbound⟩

/-- Power-series divergence at exponent s, with relative smoothness b/a,
produces every nonnegative multiplicity exponent strictly below s-b/a. -/
theorem infinite_g_gt_of_rational_smooth_power_nonsummability
    (a b : ℕ) (hb : 0 < b) (hba : b < a)
    (s : ℝ) (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (H : ¬Summable ((rationalSmoothShiftedPrimes a b).indicator
      (fun p : ℕ => (p : ℝ) ^ (-s))))
    (γ : ℝ) (hγ : 0 ≤ γ) (hγs : γ < s - (b : ℝ) / a) :
    {n : ℕ | (g n : ℝ) > (n : ℝ) ^ γ}.Infinite := by
  have ha : 0 < a := hb.trans hba
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hmargin : 0 < (a : ℝ) * s - b - a * γ := by
    have hdiv : γ + (b : ℝ) / a < s := by linarith
    have hmul := (mul_lt_mul_iff_right₀ haR).mpr hdiv
    field_simp at hmul
    nlinarith
  obtain ⟨k, hk⟩ := exists_nat_gt
    (max 8 (8 / ((a : ℝ) * s - b - a * γ)))
  have hk8R : (8 : ℝ) < k := (le_max_left _ _).trans_lt hk
  have hk8 : 8 ≤ k := by exact_mod_cast hk8R.le
  have hk0 : 0 < k := by omega
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk0
  have h8 : 8 < (k : ℝ) * ((a : ℝ) * s - b - a * γ) :=
    (div_lt_iff₀ hmargin).mp ((le_max_right _ _).trans_lt hk)
  let c : ℕ := ⌊(a : ℝ) * k * s⌋₊
  have hfloorlo : (a : ℝ) * k * s < (c : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have hfloorhi : (c : ℝ) ≤ (a : ℝ) * k * s :=
    Nat.floor_le (by positivity)
  have hc_le : c ≤ a * k := by
    apply Nat.floor_le_of_le
    push_cast
    exact mul_le_of_le_one_right (by positivity) hs1
  have hckR : (b : ℝ) * k + 5 < c := by
    have hnonneg : 0 ≤ (k : ℝ) * a * γ := by positivity
    nlinarith
  have hck : b * k + 5 ≤ c := by exact_mod_cast hckR.le
  have hc1 : 1 ≤ c := by omega
  have hc_lt : ((c - 1 : ℕ) : ℝ) < (a * k : ℕ) * s := by
    rw [Nat.cast_sub hc1, Nat.cast_one, Nat.cast_mul]
    linarith
  have hgap : b * k + 4 ≤ a * k := by
    have h := Nat.mul_le_mul_right k (show b + 1 ≤ a by omega)
    nlinarith only [h, hk8]
  have hinf := infinite_g_gt_of_general_dyadic_density
    (a * k) (c - 1) (b * k) hgap (by omega) (by omega)
    (rational_power_nonsummability_supplies_dyadic_family a b k (c - 1)
      ha hb hk0 s hs hc_lt H)
  have hnum : ((c - 1 - b * k - 2 : ℕ) : ℝ) =
      (c : ℝ) - b * k - 3 := by
    rw [Nat.cast_sub (by omega : 2 ≤ c - 1 - b * k),
      Nat.cast_sub (by omega : b * k ≤ c - 1),
      Nat.cast_sub hc1, Nat.cast_mul]
    norm_num
    ring
  have hakR : (0 : ℝ) < (a * k : ℕ) := by exact_mod_cast Nat.mul_pos ha hk0
  have hγk : γ < ((c - 1 - b * k - 2 : ℕ) : ℝ) / (a * k : ℕ) := by
    apply (lt_div_iff₀ hakR).mpr
    rw [hnum, Nat.cast_mul]
    nlinarith
  apply (hinf.diff (Set.finite_singleton 0)).mono
  intro n hn
  have hn0 : n ≠ 0 := by simpa only [Set.mem_singleton_iff] using hn.2
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn0
  exact (Real.rpow_le_rpow_of_exponent_le hn1 hγk.le).trans_lt hn.1

lemma summable_rational_smooth_power_above_one (a b : ℕ) (s : ℝ) (hs : 1 < s) :
    Summable ((rationalSmoothShiftedPrimes a b).indicator
      (fun p : ℕ => (p : ℝ) ^ (-s))) := by
  apply (Real.summable_nat_rpow.mpr (by linarith : -s < -1)).of_nonneg_of_le
    (fun p => Set.indicator_nonneg (fun p _ => Real.rpow_nonneg (Nat.cast_nonneg p) _) p)
  intro p
  by_cases hp : p ∈ rationalSmoothShiftedPrimes a b
  · rw [Set.indicator_of_mem hp]
  · rw [Set.indicator_of_notMem hp]
    exact Real.rpow_nonneg (Nat.cast_nonneg p) _

/-- A hypothetical eventual bound g(n)<=n^theta forces convergence above
exponent theta+b/a for b/a-smooth prime predecessors. -/
theorem summable_rational_smooth_power_of_g_power_bound
    (a b : ℕ) (hb : 0 < b) (hba : b < a)
    (θ : ℝ) (hθ : 0 ≤ θ)
    (H : ∀ᶠ n : ℕ in atTop, (g n : ℝ) ≤ (n : ℝ) ^ θ)
    (s : ℝ) (hs : θ + (b : ℝ) / a < s) :
    Summable ((rationalSmoothShiftedPrimes a b).indicator
      (fun p : ℕ => (p : ℝ) ^ (-s))) := by
  by_cases hs1 : 1 < s
  · exact summable_rational_smooth_power_above_one a b s hs1
  by_contra hsum
  have hratio : 0 ≤ (b : ℝ) / a := by positivity
  have hinf := infinite_g_gt_of_rational_smooth_power_nonsummability a b hb hba
    s (by linarith) (le_of_not_gt hs1) hsum θ hθ (by linarith)
  obtain ⟨N, hN⟩ := eventually_atTop.mp H
  obtain ⟨n, hn, hnN⟩ := hinf.exists_gt N
  exact (not_lt_of_ge (hN n hnN.le)) hn

/-- The equivalent predecessor-indexed version, with the exact loss 1/k. -/
theorem summable_root_smooth_power_of_g_power_bound
    (k : ℕ) (hk : 2 ≤ k) (θ : ℝ) (hθ : 0 ≤ θ)
    (H : ∀ᶠ n : ℕ in atTop, (g n : ℝ) ≤ (n : ℝ) ^ θ)
    (s : ℝ) (hs : θ + 1 / (k : ℝ) < s) :
    Summable ((smoothShiftedPredecessors k).indicator
      (fun d : ℕ => (d : ℝ) ^ (-s))) := by
  have hratio : 0 < 1 / (k : ℝ) := by positivity
  have hs0 : 0 ≤ s := by linarith
  have Hprime := summable_rational_smooth_power_of_g_power_bound k 1
    (by omega) (by omega) θ hθ H s (by simpa using hs)
  have Hshift := (summable_nat_add_iff 1).mpr Hprime
  apply (Hshift.mul_left ((2 : ℝ) ^ s)).of_nonneg_of_le
    (fun d => Set.indicator_nonneg (fun d _ => Real.rpow_nonneg (Nat.cast_nonneg d) _) d)
  intro d
  by_cases hd : d ∈ smoothShiftedPredecessors k
  · have hd0 : 0 < d := by have := hd.1.two_le; omega
    have hdR : (0 : ℝ) < d := by exact_mod_cast hd0
    have hp : d + 1 ∈ rationalSmoothShiftedPrimes k 1 := by
      refine ⟨hd.1, ?_⟩
      simpa only [Nat.add_sub_cancel, pow_one] using hd.2
    rw [Set.indicator_of_mem hd, Set.indicator_of_mem hp]
    have hdp : (0 : ℝ) < (d + 1 : ℕ) := by positivity
    have hdp2 : ((d + 1 : ℕ) : ℝ) ≤ 2 * d := by exact_mod_cast (show d+1 ≤ 2*d by omega)
    calc
      (d : ℝ) ^ (-s) = (2 : ℝ) ^ s * (2 * (d : ℝ)) ^ (-s) := by
        rw [Real.mul_rpow (by norm_num) hdR.le, ← mul_assoc,
          ← Real.rpow_add (by norm_num), add_neg_cancel, Real.rpow_zero, one_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos hdp hdp2 (by linarith)) (by positivity)
  · rw [Set.indicator_of_notMem hd]
    exact mul_nonneg (by positivity) (Set.indicator_nonneg
      (fun p _ => Real.rpow_nonneg (Nat.cast_nonneg p) _) (d+1))

/-- Eliminate the auxiliary rough-part exponent from the upper transfer.
The threshold s>1-1/k is still required. -/
theorem eventually_g_le_of_root_smooth_power
    (k : ℕ) (hk : 1 ≤ k) (s t : ℝ)
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (hks : 1 - 1 / (k : ℝ) < s) (hst : s < t)
    (H : Summable ((smoothShiftedPredecessors k).indicator
      (fun d : ℕ => (d : ℝ) ^ (-s)))) :
    ∀ᶠ n : ℕ in atTop, (g n : ℝ) ≤ (n : ℝ) ^ t := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  let e : ℝ := s - (1 - 1 / (k : ℝ))
  have he : 0 < e := sub_pos.mpr hks
  have heq : (k : ℝ) * e = k * s - k + 1 := by
    dsimp [e]
    field_simp
    ring
  apply eventually_g_le_rpow_of_summable_smooth_shifted k s (1 + e / 2) t
    hs (by linarith) (by linarith) hst _ H
  have hke : 0 < (k : ℝ) * e := mul_pos hkR he
  nlinarith

/-- The exact negation yields one common theta<1 governing every rational
smoothness parameter. This is conditional, not a proof of that negation. -/
theorem negation_forces_quantitative_smooth_series
    (Hneg : ¬ (∀ ε > (0 : ℝ),
      {n : ℕ | (g n : ℝ) > (n : ℝ) ^ (1 - ε)}.Infinite)) :
    ∃ θ : ℝ, 0 ≤ θ ∧ θ < 1 ∧
      (∀ᶠ n : ℕ in atTop, (g n : ℝ) ≤ (n : ℝ) ^ θ) ∧
      ∀ a b : ℕ, 0 < b → b < a → ∀ s : ℝ, θ + (b : ℝ) / a < s →
        Summable ((rationalSmoothShiftedPrimes a b).indicator
          (fun p : ℕ => (p : ℝ) ^ (-s))) := by
  obtain ⟨ε, h⟩ := not_forall.mp Hneg
  obtain ⟨hε, hfin⟩ := _root_.not_imp.mp h
  obtain ⟨B, hB⟩ := (Set.not_infinite.mp hfin).bddAbove
  let θ : ℝ := max 0 (1 - ε)
  have hθ : 0 ≤ θ := le_max_left _ _
  have hθ1 : θ < 1 := max_lt (by norm_num) (by linarith)
  have H : ∀ᶠ n : ℕ in atTop, (g n : ℝ) ≤ (n : ℝ) ^ θ := by
    filter_upwards [eventually_gt_atTop B, eventually_ge_atTop 1] with n hn hn1
    have hg : (g n : ℝ) ≤ (n : ℝ) ^ (1 - ε) :=
      le_of_not_gt (fun hg => (not_le_of_gt hn) (hB hg))
    exact hg.trans (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn1)
      (le_max_right _ _))
  exact ⟨θ, hθ, hθ1, H, fun a b hb hba s hs =>
    summable_rational_smooth_power_of_g_power_bound a b hb hba θ hθ H s hs⟩

/-- Feeding the preceding summability threshold back into the rough-part
upper estimate cannot improve theta: the necessary intermediate exponent
is larger than (1+theta)/2, which itself is larger than theta when theta<1.
This concerns only this pair of estimates, not all possible arguments. -/
lemma quantitative_series_feedback_margin (θ δ s : ℝ)
    (hθ : θ < 1) (h₁ : θ + δ < s) (h₂ : 1 - δ < s) :
    θ < (1 + θ) / 2 ∧ (1 + θ) / 2 < s := by
  constructor <;> linarith

end Erdos821
