import Submission.LargePrimeDensityLower

/-! An improved lower bound for large prime factors by splitting the prime
reciprocal sum into two exponent bands. No prime number theorem is used. -/
namespace Erdos371.FiniteSieve
open Finset Filter
open scoped Topology

lemma largePrimeSet_reciprocal_split (B C N : ℕ) (hBC : B ≤ C) (hCN : C ≤ N) :
    (∑ p ∈ largePrimeSet B N, (1 : ℝ)/p) =
      (∑ p ∈ largePrimeSet B C, (1 : ℝ)/p)+(∑ p ∈ largePrimeSet C N, (1 : ℝ)/p) := by
  have he : largePrimeSet B N=largePrimeSet B C ∪ largePrimeSet C N := by
    ext p
    simp only [largePrimeSet,mem_filter,Nat.mem_primesBelow,mem_union]
    constructor
    · rintro ⟨⟨hpN,hp⟩,hpB⟩
      by_cases hpC : p ≤ C
      · exact Or.inl ⟨⟨by omega,hp⟩,hpB⟩
      · exact Or.inr ⟨⟨hpN,hp⟩,by omega⟩
    · rintro (⟨⟨hpC,hp⟩,hpB⟩ | ⟨⟨hpN,hp⟩,hpC⟩)
      · exact ⟨⟨by omega,hp⟩,hpB⟩
      · exact ⟨⟨hpN,hp⟩,by omega⟩
  have hd : Disjoint (largePrimeSet B C) (largePrimeSet C N) := by
    apply disjoint_left.mpr
    intro p hp hq
    have hpC := (Nat.mem_primesBelow.mp (mem_filter.mp hp).1).1
    have hCp := (mem_filter.mp hq).2
    omega
  rw [he,sum_union hd]

lemma largePrimeDivisorSet_ratio_ge_reciprocal (B N : ℕ)
    (hB : 1 < B) (hN : 0 < N) (hsq : N ≤ B^2) :
    (∑ p ∈ largePrimeSet B N, (1 : ℝ)/p)-Real.log 4/Real.log B ≤
      ((largePrimeDivisorSet B N).card : ℝ)/N := by
  have hN0 : (0 : ℝ)<N := by exact_mod_cast hN
  have hlogB : 0 < Real.log B := Real.log_pos (by exact_mod_cast hB)
  have hterm (p : ℕ) (hp : p ∈ largePrimeSet B N) : (N : ℝ)/p-1 ≤ (N/p : ℕ) := by
    have hpp := (Nat.mem_primesBelow.mp (mem_filter.mp hp).1).2
    have hh := Nat.lt_mul_div_succ N hpp.pos
    have hh' : (N : ℝ) ≤ (p : ℝ)*((N/p : ℕ)+1 : ℝ) := by exact_mod_cast hh.le
    have hdiv := (div_le_iff₀ (by exact_mod_cast hpp.pos : (0 : ℝ)<p)).mpr
      (by nlinarith : (N : ℝ) ≤ ((N/p : ℕ)+1 : ℝ)*p)
    linarith
  have hs := sum_le_sum hterm
  rw [sum_sub_distrib] at hs
  simp only [sum_const,nsmul_eq_mul,mul_one] at hs
  rw [← Nat.cast_sum,← largePrimeDivisorSet_card_eq B N hsq] at hs
  have he : (∑ p ∈ largePrimeSet B N, (N : ℝ)/p)=N*(∑ p ∈ largePrimeSet B N, (1 : ℝ)/p) := by
    rw [mul_sum]
    simp only [mul_one_div]
  rw [he] at hs
  have hc := largePrimeSet_card_log_bound B N hB
  have hc' : ((largePrimeSet B N).card : ℝ) ≤ (N : ℝ)*(Real.log 4/Real.log B) := by
    have hh := (le_div_iff₀ hlogB).mpr hc
    convert hh using 1
    ring
  apply (le_div_iff₀ hN0).mpr
  nlinarith

lemma largePrimeDivisorSet_two_band_lower (B C N : ℕ)
    (hB : 1 < B) (hBC : B ≤ C) (hCN : C ≤ N) (hsq : N ≤ B^2) :
    (Real.log C-Real.log B-(1+primePowerErrorConstant+Real.log 4))/Real.log C+
      (Real.log N-Real.log C-(1+primePowerErrorConstant+Real.log 4))/Real.log N-
      Real.log 4/Real.log B ≤ ((largePrimeDivisorSet B N).card : ℝ)/N := by
  have hC : 1<C := hB.trans_le hBC
  have hN : 1<N := hC.trans_le hCN
  have h₁ := largePrimeSet_reciprocal_lower B C (by omega) hC hBC
  have h₂ := largePrimeSet_reciprocal_lower C N (by omega) hN hCN
  have h₃ := largePrimeDivisorSet_ratio_ge_reciprocal B N hB (by omega) hsq
  rw [largePrimeSet_reciprocal_split B C N hBC hCN] at h₃
  linarith

noncomputable def ceilPowerCutoff (v : ℝ) (N : ℕ) : ℕ := ⌈(N : ℝ)^v⌉₊

lemma ceilPowerCutoff_log_bounds (v : ℝ) (hv : 0 < v) (N : ℕ) (hN : 1<N) :
    v*Real.log N ≤ Real.log (ceilPowerCutoff v N) ∧
      Real.log (ceilPowerCutoff v N) ≤ Real.log 2+v*Real.log N := by
  have hN0 : (0 : ℝ)<N := by exact_mod_cast (by omega : 0<N)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN.le
  have hpow := Real.one_le_rpow hN1 hv.le
  have hlow : (N : ℝ)^v ≤ ceilPowerCutoff v N := Nat.le_ceil _
  have hupp : (ceilPowerCutoff v N : ℝ) ≤ 2*(N : ℝ)^v := by
    have hh := Nat.ceil_lt_add_one (Real.rpow_nonneg hN0.le v)
    dsimp [ceilPowerCutoff]
    linarith
  have hBpos : (0 : ℝ)<ceilPowerCutoff v N := by linarith
  constructor
  · have hh := Real.log_le_log (Real.rpow_pos_of_pos hN0 v) hlow
    rwa [Real.log_rpow hN0] at hh
  · have hh := Real.log_le_log hBpos hupp
    rwa [Real.log_mul (by norm_num) (Real.rpow_pos_of_pos hN0 v).ne',Real.log_rpow hN0] at hh

lemma ceilPowerCutoff_log_ratio_tendsto (v : ℝ) (hv : 0<v) :
    Tendsto (fun N : ℕ => Real.log (ceilPowerCutoff v N)/Real.log N) atTop (nhds v) := by
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have ht := (tendsto_const_nhds.div_atTop hlog :
    Tendsto (fun N : ℕ => Real.log 2/Real.log N) atTop (nhds 0)).const_add v
  simp only [add_zero] at ht
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ht
  · filter_upwards [eventually_gt_atTop (1 : ℕ)] with N hN
    have hh := (ceilPowerCutoff_log_bounds v hv N hN).1
    have hlogN : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN)
    exact (le_div_iff₀ hlogN).mpr hh
  · filter_upwards [eventually_gt_atTop (1 : ℕ)] with N hN
    have hh := (ceilPowerCutoff_log_bounds v hv N hN).2
    have hlogN : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN)
    apply (div_le_iff₀ hlogN).mpr
    have he : (v+Real.log 2/Real.log N)*Real.log N=v*Real.log N+Real.log 2 := by field_simp
    rw [he]
    linarith

lemma ceilPowerCutoff_data (v w : ℝ) (hv : 1/2 < v) (hvw : v ≤ w) (hw : w ≤ 1)
    (N : ℕ) (hN : 1<N) :
    1 < ceilPowerCutoff v N ∧ ceilPowerCutoff v N ≤ ceilPowerCutoff w N ∧
      ceilPowerCutoff w N ≤ N ∧ N ≤ (ceilPowerCutoff v N)^2 := by
  have hv0 : 0<v := by linarith
  have hN0 : (0 : ℝ)<N := by exact_mod_cast (by omega : 0<N)
  have hN1 : (1 : ℝ)<N := by exact_mod_cast hN
  have hB : 1<ceilPowerCutoff v N := by
    exact_mod_cast (Real.one_lt_rpow hN1 hv0).trans_le (Nat.le_ceil ((N : ℝ)^v))
  have hBC : ceilPowerCutoff v N ≤ ceilPowerCutoff w N :=
    Nat.ceil_mono (Real.rpow_le_rpow_of_exponent_le hN1.le hvw)
  have hCN : ceilPowerCutoff w N ≤ N := Nat.ceil_le.mpr (by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hN1.le hw)
  have hBpow : (N : ℝ) ≤ ((ceilPowerCutoff v N : ℕ) : ℝ)^2 := by
    calc
      _ = (N : ℝ)^(1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (N : ℝ)^(v*2) := Real.rpow_le_rpow_of_exponent_le hN1.le (by linarith)
      _ = ((N : ℝ)^v)^2 := by rw [Real.rpow_mul hN0.le,Real.rpow_two]
      _ ≤ _ := pow_le_pow_left₀ (Real.rpow_nonneg hN0.le v) (Nat.le_ceil _) 2
  exact ⟨hB,hBC,hCN,by exact_mod_cast hBpow⟩

/-- The two-band lower proportion `(w-v)/w+(1-w)` improves the one-band
bound `1-v`. Parameters are fixed; every finite estimate used is uniform. -/
theorem largePrimeDivisorSet_two_power_bands_eventually_ge (v w : ℝ)
    (hv : 1/2<v) (hvw : v ≤ w) (hw : w ≤ 1) (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ N : ℕ in atTop, (w-v)/w+(1-w)-ε ≤
      ((largePrimeDivisorSet (ceilPowerCutoff v N) N).card : ℝ)/N := by
  let K : ℝ := 1+primePowerErrorConstant+Real.log 4
  have hv0 : 0<v := by linarith
  have hw0 : 0<w := by linarith
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hvlim := ceilPowerCutoff_log_ratio_tendsto v hv0
  have hwlim := ceilPowerCutoff_log_ratio_tendsto w hw0
  have hKlim : Tendsto (fun N : ℕ => K/Real.log N) atTop (nhds 0) := tendsto_const_nhds.div_atTop hlog
  have htop : Tendsto (fun N : ℕ => Real.log (ceilPowerCutoff v N)) atTop atTop := by
    apply tendsto_atTop.mpr
    intro R
    filter_upwards [(hlog.const_mul_atTop hv0).eventually_ge_atTop R,eventually_gt_atTop (1 : ℕ)] with N hR hN
    exact hR.trans (ceilPowerCutoff_log_bounds v hv0 N hN).1
  have herr : Tendsto (fun N : ℕ => Real.log 4/Real.log (ceilPowerCutoff v N)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop htop
  have ht := ((((hwlim.sub hvlim).sub hKlim).div hwlim hw0.ne').add
    (((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1)).sub hwlim).sub hKlim)).sub herr
  simp only [sub_zero] at ht
  have hev := ht.eventually_const_lt (by linarith : (w-v)/w+(1-w)-ε < (w-v)/w+(1-w))
  filter_upwards [hev,eventually_gt_atTop (1 : ℕ)] with N hlow hN
  obtain ⟨hB,hBC,hCN,hsq⟩ := ceilPowerCutoff_data v w hv hvw hw N hN
  have hlogN : Real.log N ≠ 0 := (Real.log_pos (by exact_mod_cast hN)).ne'
  have hlogC : Real.log (ceilPowerCutoff w N) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hB.trans_le hBC)).ne'
  have he :
      (Real.log (ceilPowerCutoff w N)/Real.log N-Real.log (ceilPowerCutoff v N)/Real.log N-K/Real.log N)/
          (Real.log (ceilPowerCutoff w N)/Real.log N)+
        (1-Real.log (ceilPowerCutoff w N)/Real.log N-K/Real.log N)-
          Real.log 4/Real.log (ceilPowerCutoff v N) =
      (Real.log (ceilPowerCutoff w N)-Real.log (ceilPowerCutoff v N)-K)/Real.log (ceilPowerCutoff w N)+
        (Real.log N-Real.log (ceilPowerCutoff w N)-K)/Real.log N-
          Real.log 4/Real.log (ceilPowerCutoff v N) := by field_simp
  simp only [Pi.div_apply] at hlow
  rw [he] at hlow
  exact hlow.le.trans (largePrimeDivisorSet_two_band_lower _ _ N hB hBC hCN hsq)

#print axioms largePrimeDivisorSet_two_power_bands_eventually_ge
end Erdos371.FiniteSieve
