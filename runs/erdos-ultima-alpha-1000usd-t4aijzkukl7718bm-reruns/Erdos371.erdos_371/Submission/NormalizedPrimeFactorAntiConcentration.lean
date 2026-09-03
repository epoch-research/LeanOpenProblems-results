import FormalConjecturesUtil
import Submission.SelbergSeparation
import Submission.NormalizedPrimeFactorStability

/-! Near-diagonal nonconcentration for the normalized logarithms of neighboring
largest prime factors. This is unsigned and does not establish their symmetry. -/

namespace Erdos371NormalizedPrimeFactorAntiConcentration

open Finset Filter Erdos371SelbergSeparation Erdos371RectangleSeparation
  Erdos371NormalizedPrimeFactorStability
open scoped Topology
attribute [local instance] Classical.propDecidable

/-- The proportion in a fixed power window can be made arbitrarily small by
choosing its positive exponent sufficiently small. -/
theorem arbitrarily_narrow_window {ε : ℝ} (hε : 0 < ε) :
    ∃ Q : ℕ, 4 ≤ Q ∧ ∀ᶠ t : ℕ in atTop,
      ((closeInputs (t/Q) (2^t)).card : ℝ)/(2:ℝ)^t < ε := by
  obtain ⟨m,hm,hmε⟩ := ((eventually_gt_atTop 0).and
    ((tendsto_const_div_atTop_nhds_zero_nat 648).eventually_lt_const
      (show (0:ℝ)<ε/4 by positivity))).exists
  let B := remainderConstant m
  have hB : 0 ≤ B := by dsimp [B,remainderConstant,sieveConstant]; positivity
  obtain ⟨Q,hQ⟩ := exists_nat_gt (max 4 (4*B/ε))
  have hQ4 : (4:ℝ) < Q := (le_max_left _ _).trans_lt hQ
  have hQ0 : 0 < Q := by exact_mod_cast (lt_trans (by norm_num : (0:ℝ)<4) hQ4)
  have hQ4' : 4 ≤ Q := by exact_mod_cast hQ4.le
  have hBQ : B/(Q:ℝ) < ε/4 := by
    apply (div_lt_iff₀ (Nat.cast_pos.mpr hQ0)).mpr
    have hh := (div_lt_iff₀ hε).mp ((le_max_right _ _).trans_lt hQ)
    nlinarith
  have hpow : Tendsto (fun t : ℕ => (2:ℝ)^t) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hsqrt : Tendsto (fun t : ℕ => 2/Real.sqrt ((2:ℝ)^t)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using (tendsto_inv_atTop_zero.comp
      (Real.tendsto_sqrt_atTop.comp hpow)).const_mul 2
  have hsmall : Tendsto (fun t : ℕ => 2/(2:ℝ)^t) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using (tendsto_inv_atTop_zero.comp hpow).const_mul 2
  have herr : Tendsto (fun t : ℕ => 2/Real.sqrt ((2:ℝ)^t)+2/(2:ℝ)^t+44*B/t)
      atTop (𝓝 0) := by
    simpa using (hsqrt.add hsmall).add (tendsto_const_div_atTop_nhds_zero_nat (44*B))
  refine ⟨Q,hQ4',?_⟩
  filter_upwards [eventually_ge_atTop (2*m), eventually_ge_atTop (2*Q),
    herr.eventually_lt_const (show (0:ℝ)<ε/2 by positivity)] with t htm htQ herr
  have hL : 2 ≤ t/Q := (Nat.le_div_iff_mul_le hQ0).mpr htQ
  have hLt : 2*(t/Q+2) ≤ t := by
    have hmul := Nat.div_mul_le_self t Q
    have hh : 4*(t/Q) ≤ t := by nlinarith
    omega
  have hb := closeInputs_fixed_scale hm htm hLt
  have hr : ((t/Q:ℕ):ℝ)/(t:ℝ) ≤ 1/(Q:ℝ) := (division_parameters hQ0 htQ).2.1
  have he : B*((t/Q+44:ℕ):ℝ)/t ≤ B/(Q:ℝ)+44*B/t := by
    have hh := mul_le_mul_of_nonneg_left hr hB
    push_cast
    simp only [div_eq_mul_inv] at hh ⊢
    nlinarith
  change _ ≤ 2/Real.sqrt ((2:ℝ)^t)+2/(2:ℝ)^t+648/(m:ℝ)+B*(t/Q+44:ℕ)/t at hb
  linarith

lemma log_eq_level_mul {n : ℕ} (hn : 1 < n) :
    Real.log (Nat.maxPrimeFac n : ℝ) = level n * Real.log (n : ℝ) := by
  unfold level
  rw [div_mul_cancel₀ _ (Real.log_pos (Nat.one_lt_cast.mpr hn)).ne']

lemma log_step_bounds {n : ℕ} (hn : 0 < n) :
    0 ≤ Real.log (n+1 : ℕ)-Real.log (n : ℝ) ∧
      Real.log (n+1 : ℕ)-Real.log (n : ℝ) ≤ Real.log 2 := by
  have hn0 : (0:ℝ) < n := Nat.cast_pos.mpr hn
  constructor
  · exact sub_nonneg.mpr (Real.log_le_log hn0 (by exact_mod_cast Nat.le_succ n))
  · have hh : (n+1 : ℕ) ≤ (2:ℝ)*n := by push_cast; exact_mod_cast (show n+1≤2*n by omega)
    have h := Real.log_le_log (by positivity : (0:ℝ)<(n+1 : ℕ)) hh
    rw [Real.log_mul (by norm_num : (2:ℝ)≠0) hn0.ne'] at h
    linarith

lemma logarithmic_gap_bound {n : ℕ} (hn : 1 < n) :
    |Real.log (Nat.maxPrimeFac (n+1) : ℝ)-Real.log (Nat.maxPrimeFac n : ℝ)| ≤
      |level (n+1)-level n| * Real.log (n : ℝ)+Real.log 2 := by
  have hs := log_step_bounds (show 0<n by omega)
  have hb := level_bounds (n+1)
  rw [log_eq_level_mul (show 1<n+1 by omega), log_eq_level_mul hn]
  have he : level (n+1)*Real.log (n+1 : ℕ)-level n*Real.log (n : ℝ) =
      (level (n+1)-level n)*Real.log (n : ℝ)+
        level (n+1)*(Real.log (n+1 : ℕ)-Real.log (n : ℝ)) := by ring
  rw [he]
  apply (abs_add_le _ _).trans
  rw [abs_mul,abs_of_nonneg (Real.log_natCast_nonneg n),
    abs_of_nonneg (mul_nonneg hb.1 hs.1)]
  have hh := mul_le_mul_of_nonneg_right hb.2 hs.1
  linarith

lemma factor_ratio_of_log_gap {p q L : ℕ} (hp : 0 < p) (hq : 0 < q)
    (h : |Real.log (q : ℝ)-Real.log (p : ℝ)| ≤ (L:ℝ)*Real.log 2) :
    max p q ≤ 2^L*min p q := by
  have h2 : (0:ℝ)<((2^L:ℕ):ℝ) := by positivity
  have hlog (a : ℕ) (ha : 0<a) :
      Real.log ((2^L*a : ℕ) : ℝ) = (L:ℝ)*Real.log 2+Real.log (a:ℝ) := by
    rw [Nat.cast_mul,Real.log_mul h2.ne' (Nat.cast_ne_zero.mpr ha.ne'),
      Nat.cast_pow,Nat.cast_ofNat,Real.log_pow]
  rcases le_total p q with hpq | hqp
  · rw [max_eq_right hpq,min_eq_left hpq]
    have hl := (abs_le.mp h).2
    have hh : Real.log (q:ℝ) ≤ Real.log (2^L*p : ℕ) := by rw [hlog p hp]; linarith
    exact_mod_cast (Real.log_le_log_iff (Nat.cast_pos.mpr hq) (by positivity)).mp hh
  · rw [max_eq_left hqp,min_eq_right hqp]
    have hl := (abs_le.mp h).1
    have hh : Real.log (p:ℝ) ≤ Real.log (2^L*q : ℕ) := by rw [hlog q hq]; linarith
    exact_mod_cast (Real.log_le_log_iff (Nat.cast_pos.mpr hp) (by positivity)).mp hh

noncomputable def nearInputs (δ : ℝ) (N : ℕ) : Finset ℕ :=
  (range N).filter fun n => |level (n+1)-level n| ≤ δ

lemma nearInputs_mono (δ : ℝ) : Monotone (nearInputs δ) := by
  intro N M hNM
  exact filter_subset_filter _ (range_mono hNM)

lemma near_implies_close {Q t n : ℕ} (hQ : 0 < Q) (ht : 4*Q ≤ t)
    (hn : 1 < n) (hnN : n < 2^t)
    (h : |level (n+1)-level n| ≤ 1/(4*(Q:ℝ))) :
    n ∈ closeInputs (t/Q) (2^t) := by
  have hQ0 : (0:ℝ) < Q := Nat.cast_pos.mpr hQ
  have hln : Real.log (n:ℝ) ≤ (t:ℝ)*Real.log 2 := by
    have hh := Real.log_le_log (Nat.cast_pos.mpr (by omega : 0<n))
      (Nat.cast_le.mpr hnN.le : (n:ℝ) ≤ (2^t:ℕ))
    simpa [Real.log_pow] using hh
  have hdiv : (t:ℝ) ≤ 2*(Q:ℝ)*(t/Q:ℕ) := by
    have hh := Nat.lt_mul_div_succ t hQ
    have hk : 2 ≤ t/Q := (Nat.le_div_iff_mul_le hQ).mpr (by omega)
    exact_mod_cast (show t ≤ 2*Q*(t/Q) by nlinarith)
  have ht' : 4*(Q:ℝ) ≤ t := by exact_mod_cast ht
  have hcoef : 1/(4*(Q:ℝ))*(t:ℝ)+1 ≤ (t/Q:ℕ) := by
    rw [show 1/(4*(Q:ℝ))*(t:ℝ)+1 = ((t:ℝ)+4*Q)/(4*Q) by field_simp]
    apply (div_le_iff₀ (by positivity : (0:ℝ)<4*Q)).mpr
    nlinarith
  have hg : |Real.log (Nat.maxPrimeFac (n+1):ℝ)-Real.log (Nat.maxPrimeFac n:ℝ)| ≤
      (t/Q:ℕ)*Real.log 2 := by
    calc
      _ ≤ |level (n+1)-level n| * Real.log (n:ℝ)+Real.log 2 := logarithmic_gap_bound hn
      _ ≤ (1/(4*(Q:ℝ))*(t:ℝ)+1)*Real.log 2 := by
        have hh := mul_le_mul h hln (Real.log_natCast_nonneg n) (by positivity)
        nlinarith
      _ ≤ _ := mul_le_mul_of_nonneg_right hcoef (Real.log_nonneg (by norm_num))
  exact mem_filter.mpr ⟨mem_range.mpr hnN,
    factor_ratio_of_log_gap (primeFac_pos (by omega)) (primeFac_pos (by omega)) hg⟩

lemma nearInputs_card_le {Q t : ℕ} (hQ : 0 < Q) (ht : 4*Q ≤ t) :
    (nearInputs (1/(4*(Q:ℝ))) (2^t)).card ≤ (closeInputs (t/Q) (2^t)).card+2 := by
  have hs : nearInputs (1/(4*(Q:ℝ))) (2^t) ⊆ closeInputs (t/Q) (2^t) ∪ range 2 := by
    intro n hn
    obtain ⟨hnN,hnδ⟩ := mem_filter.mp hn
    by_cases hn2 : 1 < n
    · exact mem_union_left _ (near_implies_close hQ ht hn2 (mem_range.mp hnN) hnδ)
    · exact mem_union_right _ (mem_range.mpr (by omega))
  exact (card_le_card hs).trans (by simpa using card_union_le (closeInputs (t/Q) (2^t)) (range 2))

theorem dyadic_nonconcentration {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ t : ℕ in atTop,
      ((nearInputs δ (2^t)).card : ℝ)/(2:ℝ)^t < ε := by
  obtain ⟨Q,hQ,hw⟩ := arbitrarily_narrow_window (show 0<ε/2 by positivity)
  have hQ0 : 0 < Q := by omega
  have hpow : Tendsto (fun t : ℕ => (2:ℝ)^t) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hsmall : Tendsto (fun t : ℕ => 2/(2:ℝ)^t) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hpow
  refine ⟨1/(4*(Q:ℝ)), by positivity, ?_⟩
  filter_upwards [hw, eventually_ge_atTop (4*Q),
    hsmall.eventually_lt_const (show 0<ε/2 by positivity)] with t ht hqt hst
  have hc : ((nearInputs (1/(4*(Q:ℝ))) (2^t)).card:ℝ) ≤
      ((closeInputs (t/Q) (2^t)).card:ℝ)+2 := by exact_mod_cast nearInputs_card_le hQ0 hqt
  have hh := div_le_div_of_nonneg_right hc (show (0:ℝ)≤(2:ℝ)^t by positivity)
  rw [add_div] at hh
  linarith

/-- The upper empirical proportion in a fixed neighborhood of the diagonal
can be made arbitrarily small. The neighborhood is chosen before taking N to
infinity. This is not a signed cancellation theorem. -/
theorem normalized_nonconcentration {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ N : ℕ in atTop,
      ((nearInputs δ N).card : ℝ)/N < ε := by
  obtain ⟨δ,hδ,hdyad⟩ := dyadic_nonconcentration (show 0<ε/2 by positivity)
  obtain ⟨t0,ht0⟩ := eventually_atTop.mp hdyad
  refine ⟨δ,hδ,?_⟩
  filter_upwards [eventually_ge_atTop (2^t0), eventually_gt_atTop 0] with N hN hN0
  let t := Nat.log 2 N+1
  have ht : t0 ≤ t := by
    have hh := Nat.le_log_of_pow_le (by decide : 1<(2:ℕ)) hN
    dsimp [t]
    omega
  have hNt : N ≤ 2^t := (Nat.lt_pow_succ_log_self (by decide : 1<(2:ℕ)) N).le
  have htN : (2:ℝ)^t ≤ 2*(N:ℝ) := by
    have hh := Nat.pow_log_le_self 2 hN0.ne'
    have he : (2:ℕ)^t ≤ 2*N := by dsimp [t]; rw [pow_succ]; omega
    exact_mod_cast he
  have hd := (div_lt_iff₀ (show (0:ℝ)<(2:ℝ)^t by positivity)).mp (ht0 t ht)
  have hc : ((nearInputs δ N).card:ℝ) ≤ (nearInputs δ (2^t)).card :=
    Nat.cast_le.mpr (card_le_card (nearInputs_mono δ hNt))
  apply (div_lt_iff₀ (Nat.cast_pos.mpr hN0)).mpr
  have hh := mul_le_mul_of_nonneg_left htN (show 0≤ε/2 by positivity)
  nlinarith

end Erdos371NormalizedPrimeFactorAntiConcentration

#print axioms Erdos371NormalizedPrimeFactorAntiConcentration.arbitrarily_narrow_window
#print axioms Erdos371NormalizedPrimeFactorAntiConcentration.normalized_nonconcentration
