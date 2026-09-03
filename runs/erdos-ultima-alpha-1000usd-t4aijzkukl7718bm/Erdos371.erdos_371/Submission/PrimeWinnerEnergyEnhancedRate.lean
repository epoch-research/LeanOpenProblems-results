import Submission.PrimeCurrentEnhancedRate
import Submission.PrimeWinnerEnergyIncrement
import Submission.PrimeWinnerBulkUpper
import Submission.RawHarmonicTauberian

/-! Quantitative transfer from harmonic-current convergence to the ordinary
prime-winner energy. The saving is subpower; the near-linear energy estimate
sufficient for the density conjecture is not proved here. -/
namespace Erdos371
open Finset Filter
open scoped Topology
set_option autoImplicit false
set_option maxHeartbeats 1000000

lemma primeWinnerEnergy_le_sq (N : ℕ) : primeWinnerEnergy N≤(N : ℝ)^2 := by
  have hs := sum_sq_le_sq_sum_of_nonneg (s := primeWinnerLabels N)
    (fun p _ => norm_nonneg (primeWinnerSum p N))
  simp only [Real.norm_eq_abs,sq_abs] at hs
  exact hs.trans (pow_le_pow_left₀ (by positivity) (primeWinnerSum_norm_sum_le N) 2)

lemma primeWinnerSum_abel_prefix (p N : ℕ) (hN : 0<N) :
    primeWinnerSum p N = (if primeWinner 0=p then factorSign 0 else 0)+
      ((N : ℝ)-1)*rawPrimeWinnerHarmonic p N-
        ∑ k ∈ range N, rawPrimeWinnerHarmonic p k := by
  have h := sum_from_rawHarmonicSum
    (fun n => if primeWinner n=p then factorSign n else 0) (N-1)
  have he (k : ℕ) : rawHarmonicSum
      (fun n => if primeWinner n=p then factorSign n else 0) k = rawPrimeWinnerHarmonic p k := by
    simp only [rawHarmonicSum,rawPrimeWinnerHarmonic,primeWinnerHarmonicTerm,ite_div,zero_div]
  simp_rw [he] at h
  rw [Nat.sub_add_cancel hN,Nat.cast_sub hN] at h
  simpa only [Nat.cast_one,primeWinnerSum,sum_filter] using h

/-- Subtracting two Abel identities removes the fixed limiting current. -/
lemma primeWinnerSum_abel_interval (p M N : ℕ) (hM : 0<M) (hMN : M≤N) :
    primeWinnerSum p N = primeWinnerSum p M+
      ((N : ℝ)-1)*(rawPrimeWinnerHarmonic p N-primeWinnerHarmonicLimit p)-
      ((M : ℝ)-1)*(rawPrimeWinnerHarmonic p M-primeWinnerHarmonicLimit p)-
      ∑ k ∈ Ico M N, (rawPrimeWinnerHarmonic p k-primeWinnerHarmonicLimit p) := by
  rw [sum_sub_distrib,sum_const,nsmul_eq_mul,Nat.card_Ico,Nat.cast_sub hMN,
    sum_Ico_eq_sub _ hMN,primeWinnerSum_abel_prefix p M hM,
    primeWinnerSum_abel_prefix p N (hM.trans_le hMN)]
  ring

private lemma four_terms_sq (a b c d : ℝ) :
    (a+b-c-d)^2≤4*(a^2+b^2+c^2+d^2) := by
  nlinarith [sq_nonneg (a-b),sq_nonneg (c-d),sq_nonneg (a+b+c+d)]

lemma primeWinnerSum_abel_square (p M N : ℕ) (hM : 0<M) (hMN : M≤N) :
    (primeWinnerSum p N)^2≤
      4*(primeWinnerSum p M)^2+
      4*(N : ℝ)^2*(rawPrimeWinnerHarmonic p N-primeWinnerHarmonicLimit p)^2+
      4*(N : ℝ)^2*(rawPrimeWinnerHarmonic p M-primeWinnerHarmonicLimit p)^2+
      4*(N : ℝ)*∑ k ∈ Ico M N, (rawPrimeWinnerHarmonic p k-primeWinnerHarmonicLimit p)^2 := by
  let e := fun k => rawPrimeWinnerHarmonic p k-primeWinnerHarmonicLimit p
  have hs : (∑ k ∈ Ico M N, e k)^2≤(N : ℝ)*∑ k ∈ Ico M N, (e k)^2 := by
    have hh := sum_mul_sq_le_sq_mul_sq (Ico M N) (fun _ => (1 : ℝ)) e
    simp only [one_mul,one_pow,sum_const,nsmul_eq_mul,mul_one,Nat.card_Ico] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le N M) (by positivity))
  have hMr : (1 : ℝ)≤M := by exact_mod_cast hM
  have hNr : (M : ℝ)≤N := by exact_mod_cast hMN
  have hNpow : ((N : ℝ)-1)^2≤(N : ℝ)^2 := by nlinarith
  have hMpow : ((M : ℝ)-1)^2≤(N : ℝ)^2 := by nlinarith
  have hne := mul_le_mul_of_nonneg_right hNpow (sq_nonneg (e N))
  have hme := mul_le_mul_of_nonneg_right hMpow (sq_nonneg (e M))
  have hh := four_terms_sq (primeWinnerSum p M) (((N : ℝ)-1)*e N)
    (((M : ℝ)-1)*e M) (∑ k ∈ Ico M N, e k)
  rw [primeWinnerSum_abel_interval p M N hM hMN]
  change (primeWinnerSum p M+((N : ℝ)-1)*e N-((M : ℝ)-1)*e M-
    ∑ k ∈ Ico M N, e k)^2≤_
  dsimp only [e] at hne hme hs hh
  nlinarith

lemma finite_primeCurrent_error_le (S : Finset ℕ) (N : ℕ) :
    (∑ p ∈ S, (rawPrimeWinnerHarmonic p N-primeWinnerHarmonicLimit p)^2)≤
      primeCurrentSquaredError N :=
  (summable_primeCurrentSquaredError N).sum_le_tsum S (fun _ _ => sq_nonneg _)

/-- A finite quantitative vector-valued Abel bound. A uniform harmonic L2
error R on [M,N] gives normalized ordinary energy at most 4(M/N)^2+12R. -/
theorem primeWinnerEnergy_of_uniform_harmonic_error (M N : ℕ) (hM : 0<M) (hMN : M≤N)
    (R : ℝ) (hR : 0≤R)
    (herr : ∀ k ∈ Icc M N, primeCurrentSquaredError k≤R) :
    primeWinnerEnergy N≤4*(M : ℝ)^2+12*(N : ℝ)^2*R := by
  let S := primeWinnerLabels N
  have hsum := sum_le_sum (fun p (_ : p∈S) => primeWinnerSum_abel_square p M N hM hMN)
  simp only [sum_add_distrib,← mul_sum] at hsum
  have hMsum : (∑ p ∈ S, (primeWinnerSum p M)^2)≤(M : ℝ)^2 := by
    rw [← primeWinnerEnergy_enlarge_labels hMN]
    exact primeWinnerEnergy_le_sq M
  have hNerr := (finite_primeCurrent_error_le S N).trans (herr N (mem_Icc.mpr ⟨hMN,le_rfl⟩))
  have hMerr := (finite_primeCurrent_error_le S M).trans (herr M (mem_Icc.mpr ⟨le_rfl,hMN⟩))
  have hinter : (∑ p ∈ S, ∑ k ∈ Ico M N,
      (rawPrimeWinnerHarmonic p k-primeWinnerHarmonicLimit p)^2)≤(N : ℝ)*R := by
    rw [sum_comm]
    calc
      _ ≤ ∑ k ∈ Ico M N, R := by
        apply sum_le_sum
        intro k hk
        exact (finite_primeCurrent_error_le S k).trans
          (herr k (mem_Icc.mpr ⟨(mem_Ico.mp hk).1,(mem_Ico.mp hk).2.le⟩))
      _ = ((N-M : ℕ) : ℝ)*R := by simp only [sum_const,nsmul_eq_mul,Nat.card_Ico]
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le N M) hR
  change primeWinnerEnergy N≤_ at hsum
  have hm := mul_le_mul_of_nonneg_left hMsum (by norm_num : (0 : ℝ)≤4)
  have hn := mul_le_mul_of_nonneg_left hNerr (show 0≤4*(N : ℝ)^2 by positivity)
  have he := mul_le_mul_of_nonneg_left hMerr (show 0≤4*(N : ℝ)^2 by positivity)
  have hi := mul_le_mul_of_nonneg_left hinter (show 0≤4*(N : ℝ) by positivity)
  nlinarith

lemma enhancedCurrentScale_half_log_comparison (N K : ℕ)
    (hN : 4≤Real.log N) (hK : Real.log N/2≤Real.log K) :
    enhancedCurrentScale N≤2*enhancedCurrentScale K := by
  have hL : 0<Real.log N := by linarith
  have hKL : 1≤Real.log K := by linarith
  have hK0 : 0<Real.log K := by linarith
  have hLL : 0≤Real.log (Real.log N) := Real.log_nonneg (by linarith)
  have hKLL : 0≤Real.log (Real.log K) := Real.log_nonneg hKL
  have hlog4 : Real.log 4=2*Real.log 2 := by
    rw [show (4 : ℝ)=(2 : ℝ)^2 by norm_num,Real.log_pow]
    norm_num
  have hLLbig : 2*Real.log 2≤Real.log (Real.log N) := by
    rw [← hlog4]
    exact Real.log_le_log (by norm_num) hN
  have hlogK : Real.log (Real.log N)/2≤Real.log (Real.log K) := by
    have hh := Real.log_le_log (half_pos hL) hK
    rw [Real.log_div hL.ne' (by norm_num)] at hh
    linarith
  have hm := mul_le_mul hK hlogK (div_nonneg hLL (by norm_num)) hK0.le
  have hn := Real.sq_sqrt (mul_nonneg hL.le hLL)
  have hk := Real.sq_sqrt (mul_nonneg hK0.le hKLL)
  have hn0 := Real.sqrt_nonneg (Real.log N*Real.log (Real.log N))
  have hk0 := Real.sqrt_nonneg (Real.log K*Real.log (Real.log K))
  unfold enhancedCurrentScale
  nlinarith

noncomputable def enhancedWinnerEnergyConstant : ℝ :=
  16+12*enhancedCurrentRateConstant

lemma enhancedWinnerEnergyConstant_pos : 0<enhancedWinnerEnergyConstant := by
  unfold enhancedWinnerEnergyConstant
  have h := enhancedCurrentRateConstant_pos
  positivity

/-- An unconditional natural-prefix energy bound with a stretched-exponential
saving from N^2. It is not the near-linear bound required by the density
criterion. -/
theorem primeWinnerEnergy_enhanced_bound :
    ∀ᶠ N : ℕ in atTop, primeWinnerEnergy N≤
      enhancedWinnerEnergyConstant*(N : ℝ)^2*Real.exp (-enhancedCurrentScale N/256) := by
  obtain ⟨T,hT⟩ := eventually_atTop.mp primeCurrentSquaredError_enhanced_bound
  have hcut : Tendsto (fun N : ℕ => ⌈Real.sqrt (N : ℝ)⌉₊) atTop atTop :=
    tendsto_nat_ceil_atTop.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hcut.eventually_ge_atTop T,hlog.eventually_ge_atTop 4,
    eventually_ge_atTop (1 : ℕ),
    enhancedCurrentScale_div_log_tendsto_zero.eventually_le_const
      (by norm_num : (0 : ℝ)<256)] with N hNT hL hN hsub
  let M : ℕ := ⌈Real.sqrt (N : ℝ)⌉₊
  let R : ℝ := enhancedCurrentRateConstant*Real.exp (-enhancedCurrentScale N/256)
  have hNr : (1 : ℝ)≤N := by exact_mod_cast hN
  have hN0 : (0 : ℝ)<N := by linarith
  have hL0 : 0<Real.log N := by linarith
  have hroot : (Real.sqrt (N : ℝ))^2=N := Real.sq_sqrt hN0.le
  have hroot0 : 0≤Real.sqrt (N : ℝ) := Real.sqrt_nonneg _
  have hroot1 : 1≤Real.sqrt (N : ℝ) := Real.one_le_sqrt.mpr hNr
  have hM : 0<M := Nat.ceil_pos.mpr (Real.sqrt_pos.mpr hN0)
  have hMN : M≤N := Nat.ceil_le.mpr (by nlinarith)
  have hfloor : Real.sqrt (N : ℝ)≤(M : ℝ) := Nat.le_ceil _
  have hMupper : (M : ℝ)≤2*Real.sqrt (N : ℝ) := by
    have hh := Nat.ceil_lt_add_one hroot0
    change (M : ℝ)<Real.sqrt (N : ℝ)+1 at hh
    linarith
  have hMsq : (M : ℝ)^2≤4*(N : ℝ) := by
    have hh := pow_le_pow_left₀ (Nat.cast_nonneg M) hMupper 2
    rw [mul_pow,hroot] at hh
    norm_num at hh
    exact hh
  have hR : 0≤R := mul_nonneg enhancedCurrentRateConstant_pos.le (Real.exp_nonneg _)
  have herr (k : ℕ) (hk : k∈Icc M N) : primeCurrentSquaredError k≤R := by
    have hMk := (mem_Icc.mp hk).1
    have hkt : T≤k := hNT.trans hMk
    have hlogk : Real.log N/2≤Real.log k := by
      have hcast : Real.sqrt (N : ℝ)≤(k : ℝ) :=
        hfloor.trans (by exact_mod_cast hMk)
      simpa only [Real.log_sqrt hN0.le] using
        Real.log_le_log (Real.sqrt_pos.mpr hN0) hcast
    have hs := enhancedCurrentScale_half_log_comparison N k hL hlogk
    exact (hT k hkt).trans (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (by linarith)) enhancedCurrentRateConstant_pos.le)
  have hb := primeWinnerEnergy_of_uniform_harmonic_error M N hM hMN R hR herr
  have hone : 1/(N : ℝ)≤Real.exp (-enhancedCurrentScale N/256) := by
    have hh := (div_le_iff₀ hL0).mp hsub
    calc
      _ = Real.exp (-Real.log N) := by rw [Real.exp_neg,Real.exp_log hN0,one_div]
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  have hmul : (N : ℝ)≤(N : ℝ)^2*Real.exp (-enhancedCurrentScale N/256) := by
    have hh := mul_le_mul_of_nonneg_left hone (sq_nonneg (N : ℝ))
    convert hh using 1
    field_simp
  have hh := mul_le_mul_of_nonneg_left hMsq (by norm_num : (0 : ℝ)≤4)
  have hi := mul_le_mul_of_nonneg_left hmul (by norm_num : (0 : ℝ)≤16)
  dsimp only [R] at hb
  unfold enhancedWinnerEnergyConstant
  nlinarith

/-- The majorant above is larger than every N^(1+eta) with eta<1,
asymptotically. This is not a lower bound on primeWinnerEnergy itself. -/
theorem enhancedWinnerEnergy_majorant_not_near_linear (η : ℝ) (hη : η<1) :
    Tendsto (fun N : ℕ =>
      (enhancedWinnerEnergyConstant*(N : ℝ)^2*Real.exp (-enhancedCurrentScale N/256))/
        (N : ℝ)^(1+η)) atTop atTop := by
  have hh := (enhancedCurrentScale_still_subpower (1/256) (1-η) (by linarith)).const_mul_atTop
    enhancedWinnerEnergyConstant_pos
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
  have hNr : (0 : ℝ)<N := by exact_mod_cast hN
  have hp : (N : ℝ)^2/(N : ℝ)^(1+η)=(N : ℝ)^(1-η) := by
    rw [← Real.rpow_two,← Real.rpow_sub hNr]
    congr 1
    ring
  rw [show -(1/256 : ℝ)*enhancedCurrentScale N = -enhancedCurrentScale N/256 by ring]
  rw [← hp]
  ring

#print axioms primeWinnerSum_abel_interval
#print axioms primeWinnerEnergy_of_uniform_harmonic_error
#print axioms primeWinnerEnergy_enhanced_bound
#print axioms enhancedWinnerEnergy_majorant_not_near_linear

end Erdos371
