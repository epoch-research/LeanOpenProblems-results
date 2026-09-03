import Submission.TwoBandLargePrimeLower

/-! Uniform lower bounds for large prime factors in terminal intervals with
length at least a fixed proportion of their endpoint. -/
namespace Erdos371.FiniteSieve
open Finset Filter
open scoped Topology
set_option autoImplicit false

lemma largePrimeDivisorSet_eq_high (B N : ℕ) (hB : 1 ≤ B) :
    largePrimeDivisorSet B N = (range N).filter (fun n => B < Nat.maxPrimeFac (n+1)) := by
  classical
  ext n
  simp only [largePrimeDivisorSet, mem_filter]
  constructor
  · rintro ⟨hn,p,hp,hpd⟩
    have hpp := (Nat.mem_primesBelow.mp (mem_filter.mp hp).1).2
    exact ⟨hn, ((mem_filter.mp hp).2).trans_le
      (Nat.le_maxPrimeFac (by omega : n+1 ≠ 0) hpp hpd)⟩
  · rintro ⟨hn,hp⟩
    have hn1 : 1 < n+1 := (Nat.one_lt_maxPrimeFac_iff (n+1)).mp (hB.trans_lt hp)
    have hpp := Nat.prime_maxPrimeFac_of_one_lt (n+1) hn1
    have hpd := Nat.maxPrimeFac_dvd (n := n+1)
    have hpN := Nat.maxPrimeFac_le (n := n+1)
    refine ⟨hn,Nat.maxPrimeFac (n+1),?_,hpd⟩
    exact mem_filter.mpr ⟨Nat.mem_primesBelow.mpr ⟨by have := mem_range.mp hn; omega,hpp⟩,hp⟩

lemma largePrimeDivisorSet_card_le_band (B L M : ℕ) (hLM : L ≤ M) (hsq : M ≤ B^2) :
    ((largePrimeDivisorSet B L).card : ℝ) ≤
      (L : ℝ) * ∑ p ∈ largePrimeSet B M, (1 : ℝ)/p := by
  classical
  rw [largePrimeDivisorSet_card_eq B L (hLM.trans hsq), Nat.cast_sum]
  calc
    _ ≤ ∑ p ∈ largePrimeSet B L, (L : ℝ)/p := sum_le_sum fun _ _ => Nat.cast_div_le
    _ ≤ ∑ p ∈ largePrimeSet B M, (L : ℝ)/p := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro p hp
        obtain ⟨hp,hBp⟩ := mem_filter.mp hp
        obtain ⟨hpL,hpp⟩ := Nat.mem_primesBelow.mp hp
        exact mem_filter.mpr ⟨Nat.mem_primesBelow.mpr ⟨by omega,hpp⟩,hBp⟩
      · intro p _ _
        positivity
    _ = _ := by rw [mul_sum]; simp only [mul_one_div]

lemma filter_card_range_add_Ico (P : ℕ → Prop) [DecidablePred P]
    (L M : ℕ) (hLM : L ≤ M) :
    ((range L).filter P).card + ((Ico L M).filter P).card = ((range M).filter P).card := by
  simpa only [sum_boole, Nat.cast_id] using
    sum_range_add_sum_Ico (fun n => if P n then (1 : ℕ) else 0) hLM

lemma largePrime_window_ratio_ge_reciprocal (B L M : ℕ) (θ : ℝ)
    (hB : 1 < B) (hM : 0 < M) (hLM : L ≤ M) (hsq : M ≤ B^2)
    (hθ : (L : ℝ) ≤ (1-θ)*(M : ℝ)) :
    θ * (∑ p ∈ largePrimeSet B M, (1 : ℝ)/p) - Real.log 4/Real.log B ≤
      (((Ico L M).filter (fun n => B < Nat.maxPrimeFac (n+1))).card : ℝ)/M := by
  classical
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hrec : 0 ≤ ∑ p ∈ largePrimeSet B M, (1 : ℝ)/p := sum_nonneg fun _ _ => by positivity
  have htotal := largePrimeDivisorSet_ratio_ge_reciprocal B M hB hM hsq
  have hprefix := largePrimeDivisorSet_card_le_band B L M hLM hsq
  have hsplit := filter_card_range_add_Ico (fun n => B < Nat.maxPrimeFac (n+1)) L M hLM
  rw [largePrimeDivisorSet_eq_high B M hB.le] at htotal
  rw [largePrimeDivisorSet_eq_high B L hB.le] at hprefix
  have hsplitR : (((range L).filter (fun n => B < Nat.maxPrimeFac (n+1))).card : ℝ) +
      (((Ico L M).filter (fun n => B < Nat.maxPrimeFac (n+1))).card : ℝ) =
      (((range M).filter (fun n => B < Nat.maxPrimeFac (n+1))).card : ℝ) := by exact_mod_cast hsplit
  have ht := (le_div_iff₀ hMr).mp htotal
  have hp := mul_le_mul_of_nonneg_right hθ hrec
  apply (le_div_iff₀ hMr).mpr
  nlinarith

/-- A uniform lower bound over all terminal intervals whose length is at
least `θ` times the upper endpoint. The density is normalized by that endpoint. -/
theorem largePrime_power_window_eventually_ge (v θ : ℝ)
    (hv : 1/2 < v) (hv1 : v < 1) (hθ : 0 ≤ θ)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ M : ℕ in atTop, ∀ L ≤ M, (L : ℝ) ≤ (1-θ)*(M : ℝ) →
      θ*(1-v)-ε ≤
        (((Ico L M).filter (fun n => (M : ℝ)^v < (Nat.maxPrimeFac (n+1) : ℝ))).card : ℝ)/M := by
  classical
  let K : ℝ := 1+primePowerErrorConstant+Real.log 4
  have hv0 : 0 < v := by linarith
  have hlog : Tendsto (fun M : ℕ => Real.log M) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hratio := ceilPowerCutoff_log_ratio_tendsto v hv0
  have hK : Tendsto (fun M : ℕ => K/Real.log M) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hlog
  have hBtop : Tendsto (fun M : ℕ => Real.log (ceilPowerCutoff v M)) atTop atTop := by
    apply tendsto_atTop.mpr
    intro R
    filter_upwards [(hlog.const_mul_atTop hv0).eventually_ge_atTop R,
      eventually_gt_atTop (1 : ℕ)] with M hR hM
    exact hR.trans (ceilPowerCutoff_log_bounds v hv0 M hM).1
  have herr : Tendsto (fun M : ℕ => Real.log 4/Real.log (ceilPowerCutoff v M)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hBtop
  have ht := ((((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub
    hratio).sub hK).const_mul θ).sub herr
  simp only [sub_zero] at ht
  have he := ht.eventually_const_lt (by linarith : θ*(1-v)-ε < θ*(1-v))
  filter_upwards [he,eventually_gt_atTop (1 : ℕ)] with M hsmall hM
  intro L hLM hL
  obtain ⟨hB,_,hBM,hsq⟩ := ceilPowerCutoff_data v v hv le_rfl hv1.le M hM
  have hr := largePrimeSet_reciprocal_lower (ceilPowerCutoff v M) M (by omega) hM hBM
  have hw := largePrime_window_ratio_ge_reciprocal (ceilPowerCutoff v M) L M θ
    hB (by omega) hLM hsq hL
  have hlogM : Real.log M ≠ 0 := (Real.log_pos (by exact_mod_cast hM : (1 : ℝ) < M)).ne'
  have hid : (Real.log M - Real.log (ceilPowerCutoff v M) - K)/Real.log M =
      1 - Real.log (ceilPowerCutoff v M)/Real.log M - K/Real.log M := by field_simp
  change (Real.log M - Real.log (ceilPowerCutoff v M) - K)/Real.log M ≤ _ at hr
  rw [hid] at hr
  have hlower := mul_le_mul_of_nonneg_left hr hθ
  have hc : ((Ico L M).filter (fun n => ceilPowerCutoff v M < Nat.maxPrimeFac (n+1))).card ≤
      ((Ico L M).filter (fun n => (M : ℝ)^v < (Nat.maxPrimeFac (n+1) : ℝ))).card := by
    apply card_le_card
    intro n hn
    obtain ⟨hn,hp⟩ := mem_filter.mp hn
    exact mem_filter.mpr ⟨hn, (Nat.le_ceil ((M : ℝ)^v)).trans_lt (by exact_mod_cast hp)⟩
  have hcR := div_le_div_of_nonneg_right ((Nat.cast_le (α := ℝ)).mpr hc) (Nat.cast_nonneg (α := ℝ) M)
  change θ*(1-v)-ε < θ*(1-Real.log (ceilPowerCutoff v M)/Real.log M-K/Real.log M)-
    Real.log 4/Real.log (ceilPowerCutoff v M) at hsmall
  linarith

#print axioms largePrime_power_window_eventually_ge
end Erdos371.FiniteSieve
