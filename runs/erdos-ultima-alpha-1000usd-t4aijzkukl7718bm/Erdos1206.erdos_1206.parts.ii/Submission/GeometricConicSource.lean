import Submission.ConicPrimeBlockEstimates

/-! A geometric schedule of conic prime blocks. The source threshold is
asymptotically negligible relative to the block's log-log scale. -/
namespace Erdos1206.GeometricConicSource
open Finset Filter ConicPrimeBlockEstimates ProportionalConicBandSource
open SquarefreeConicFamily SquarefreeConicCharacterScore ConicPrimeCharacterScore
open ConicCharacterBandSource SharpPrimeBlockVariance
open scoped Topology Classical

noncomputable def primeCutoff (j : ℕ) : ℝ := Real.exp (Real.exp ((3/2:ℝ)^j))
noncomputable def P (j : ℕ) : Finset ℕ := block (primeCutoff j)

lemma primeCutoff_tendsto : Tendsto primeCutoff atTop atTop := by
  exact Real.tendsto_exp_atTop.comp (Real.tendsto_exp_atTop.comp
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ) < 3/2)))

lemma log_log_primeCutoff (j : ℕ) : Real.log (Real.log (primeCutoff j))=(3/2:ℝ)^j := by
  simp only [primeCutoff,Real.log_exp]

lemma P_regular (j p : ℕ) (hp : p ∈ P j) : p.Prime ∧ 1000000000 < p :=
  ⟨(mem_block hp).1,(mem_block hp).2.1⟩

lemma eventually_energy_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ j : ℕ in atTop, mass (P j) weight ≤ C*(3/2:ℝ)^j := by
  obtain ⟨_,_,_,hbound⟩ := eventually_block_bounds
  let C : ℝ := Real.exp 1*(1+Real.log 2)
  have hl : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  refine ⟨C,by dsimp only [C]; positivity,?_⟩
  filter_upwards [primeCutoff_tendsto.eventually hbound] with j hj
  rw [←block_energy,log_log_primeCutoff] at hj
  have hp : (1:ℝ) ≤ (3/2:ℝ)^j := one_le_pow₀ (by norm_num)
  have hm := mul_le_mul_of_nonneg_left (show (3/2:ℝ)^j+Real.log 2 ≤ (1+Real.log 2)*(3/2:ℝ)^j by
    nlinarith) (Real.exp_pos 1).le
  exact hj.2.1.trans (by simpa only [C,mul_assoc] using hm)

lemma band_le_geometric {K C S : ℝ} (hK : 0 < K) (hC : 0 < C)
    (j : ℕ) (hbound : S ≤ C*(3/2:ℝ)^j) :
    4*Real.sqrt (K*(4/3:ℝ)^j*S)+2*Real.sqrt (2000000*S) ≤
      (4*Real.sqrt (K*C)+2*Real.sqrt (2000000*C))*(17/12:ℝ)^j := by
  have hr0 : 0 ≤ (17/12:ℝ)^j := pow_nonneg (by norm_num) _
  have hsqrt1 : Real.sqrt (K*(4/3:ℝ)^j*S) ≤ Real.sqrt (K*C)*(17/12:ℝ)^j := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨mul_nonneg (Real.sqrt_nonneg _) hr0,?_⟩
    rw [mul_pow,Real.sq_sqrt (mul_pos hK hC).le,←pow_mul, mul_comm j 2,pow_mul]
    have hh := mul_le_mul_of_nonneg_left hbound (show 0 ≤ K*(4/3:ℝ)^j by positivity)
    have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2)
      (by norm_num : (2:ℝ) ≤ (17/12:ℝ)^2) j
    have he : K*(4/3:ℝ)^j*(C*(3/2:ℝ)^j)=K*C*(2:ℝ)^j := by
      rw [show K*(4/3:ℝ)^j*(C*(3/2:ℝ)^j)=K*C*((4/3:ℝ)^j*(3/2:ℝ)^j) by ring,
        ←mul_pow,show (4/3:ℝ)*(3/2)=2 by norm_num]
    rw [he] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left hp (mul_pos hK hC).le)
  have hsqrt2 : Real.sqrt (2000000*S) ≤ Real.sqrt (2000000*C)*(17/12:ℝ)^j := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨mul_nonneg (Real.sqrt_nonneg _) hr0,?_⟩
    rw [mul_pow,Real.sq_sqrt (show 0 ≤ 2000000*C by positivity),←pow_mul,mul_comm j 2,pow_mul]
    have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 3/2)
      (by norm_num : (3/2:ℝ) ≤ (17/12:ℝ)^2) j
    have hh := mul_le_mul_of_nonneg_left hbound (by norm_num : (0:ℝ) ≤ 2000000)
    have hm := mul_le_mul_of_nonneg_left hp (show 0 ≤ 2000000*C by positivity)
    nlinarith only [hh,hm]
  nlinarith only [hsqrt1,hsqrt2]

lemma ceil_band_ratio_tendsto {K : ℝ} (hK : 0 < K) (S : ℕ → ℝ)
    (hbound : ∃ C : ℝ, 0 < C ∧ ∀ᶠ j : ℕ in atTop, S j ≤ C*(3/2:ℝ)^j) :
    Tendsto (fun j : ℕ =>
      ((⌈4*Real.sqrt (K*(4/3:ℝ)^j*S j)+2*Real.sqrt (2000000*S j)⌉₊:ℕ):ℝ)/(3/2:ℝ)^j)
      atTop (𝓝 0) := by
  obtain ⟨C,hC,hbound⟩ := hbound
  let R : ℝ := 4*Real.sqrt (K*C)+2*Real.sqrt (2000000*C)
  have hlim : Tendsto (fun j : ℕ => R*(17/18:ℝ)^j+(2/3:ℝ)^j) atTop (𝓝 0) := by
    have h₁ := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 17/18)
      (by norm_num : (17/18:ℝ) < 1)).const_mul R
    have h₂ := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 2/3)
      (by norm_num : (2/3:ℝ) < 1)
    simpa only [mul_zero,add_zero] using h₁.add h₂
  apply squeeze_zero' (Eventually.of_forall (fun j => by positivity)) _ hlim
  filter_upwards [hbound] with j hj
  have hh := band_le_geometric hK hC j hj
  have hnonneg : 0 ≤ 4*Real.sqrt (K*(4/3:ℝ)^j*S j)+2*Real.sqrt (2000000*S j) := by positivity
  have hceil := Nat.ceil_lt_add_one hnonneg
  have hpp : 0 < (3/2:ℝ)^j := by positivity
  apply (div_le_iff₀ hpp).mpr
  have he : (R*(17/18:ℝ)^j+(2/3:ℝ)^j)*(3/2:ℝ)^j=R*(17/12:ℝ)^j+1 := by
    rw [add_mul,mul_assoc,←mul_pow,←mul_pow]
    norm_num
  rw [he]
  dsimp only [R] at *
  linarith

/-- The source covers every positive rational scaling of the conic. The
integer threshold is o((3/2)^j), the key saving in the sieve schedule. -/
theorem exists_source_threshold :
    ∃ (A : Set ℕ) (k : ℕ → ℕ),
      (∀ n ∈ A, Squarefree n) ∧ 0 < A.lowerDensity ∧
      Tendsto (fun j : ℕ => (k j:ℝ)/(3/2:ℝ)^j) atTop (𝓝 0) ∧
      ∀ (j t u : ℕ) (x : Fin 4 → ℕ), Nat.Coprime t u → 0 < u → 0 < x 0 →
        (∀ i, x i*F 0 t u=x 0*F i t u) → (∀ i, x i ∈ A) →
        mixedMass (P j) χ ψ (F 0 t u) (F 1 t u) (F 2 t u) (F 3 t u) ≤ k j := by
  obtain ⟨K,hK,hsource⟩ := ProportionalConicBandSource.exists_source (4/3:ℝ) (by norm_num)
  obtain ⟨A,hAS,hAd,hA⟩ := hsource P P_regular
  let k : ℕ → ℕ := fun j =>
    ⌈4*Real.sqrt (K*(4/3:ℝ)^j*mass (P j) weight)+2*Real.sqrt (2000000*mass (P j) weight)⌉₊
  refine ⟨A,k,hAS,hAd,ceil_band_ratio_tendsto hK (fun j => mass (P j) weight)
    eventually_energy_bound,?_⟩
  intro j t u x hcop hu hx hprop hmem
  have hh := hA j t u x hcop hu hx hprop hmem
  have hm := hh.trans (Nat.le_ceil _)
  exact_mod_cast hm

#print axioms eventually_energy_bound
#print axioms ceil_band_ratio_tendsto
#print axioms exists_source_threshold
end Erdos1206.GeometricConicSource
