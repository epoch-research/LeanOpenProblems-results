import Submission.IteratedPrimeBlocks

/-! A uniformly occupied family of consecutive power prime blocks. Its total
reciprocal-mass budget is fixed before the power exponent is chosen. -/
namespace Erdos371.FiniteSieve
open Finset Filter
open scoped Topology

/-- Each of K consecutive blocks has reciprocal mass at least J/4, while
all K blocks together have twice-reciprocal mass at most 16*2^(J*K).
The latter bound is independent of alpha. -/
theorem exists_occupied_power_prime_blocks (J K : ℕ) (hJ : 0<J)
    (α ε : ℝ) (hα : 0<α) (hα1 : α<1) (hε : 0<ε) :
    ∃ u : ℝ, 0<u ∧ u≤α ∧ ∃ t : ℕ → ℕ, ∀ᶠ N : ℕ in atTop,
      1<t N ∧ (N : ℝ)^u≤t N ∧ (blockCutoff (t N) J K : ℝ)≤(N : ℝ)^α ∧
      2*primeReciprocalMass (largePrimeSet (t N) (blockCutoff (t N) J K))≤16*(2^(J*K) : ℕ) ∧
      ∀ i<K, (emptyPrimeBlockCount (iteratedPrimeBlock (t N) J i) N : ℝ)/N≤16/(J : ℝ)+ε := by
  let Q : ℕ := 2^(J*K)
  let e : ℝ := α/Q
  let u : ℝ := e/2
  let t : ℕ → ℕ := fun N => ⌊(N : ℝ)^e⌋₊
  have hQ : 0<Q := Nat.pow_pos (by norm_num)
  have hQ1 : (1 : ℝ)≤Q := by exact_mod_cast hQ
  have he : 0<e := by dsimp [e]; positivity
  have hu : 0<u := by dsimp [u]; positivity
  have huα : u≤α := by
    have heα : e≤α := div_le_self hα.le hQ1
    dsimp [u]
    linarith
  have htt : Tendsto t atTop atTop := tendsto_nat_floor_atTop.comp
    ((tendsto_rpow_atTop he).comp tendsto_natCast_atTop_atTop)
  have htlog : Tendsto (fun N => Real.log (t N)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp htt)
  have htlog2 := htlog.atTop_div_const (Real.log_pos (by norm_num : (1 : ℝ)<2))
  have htu := (tendsto_rpow_atTop hu).comp tendsto_natCast_atTop_atTop
  have hpow : Tendsto (fun N : ℕ => (N : ℝ)^α/N) atTop (𝓝 0) := by
    have h := (tendsto_rpow_neg_atTop (show 0<1-α by linarith)).comp tendsto_natCast_atTop_atTop
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
    dsimp only [Function.comp_apply]
    rw [show -(1-α)=α-1 by ring,Real.rpow_sub (by exact_mod_cast hN),Real.rpow_one]
  have htail : Tendsto (fun N : ℕ => 32*((N : ℝ)^α+1)/((N : ℝ)*J)) atTop (𝓝 0) := by
    have h := (hpow.add tendsto_one_div_atTop_nhds_zero_nat).const_mul (32/(J : ℝ))
    simp only [add_zero,mul_zero] at h
    convert h using 1
    funext N
    ring
  refine ⟨u,hu,huα,t,?_⟩
  filter_upwards [htt.eventually_gt_atTop 1,
    htlog.eventually_ge_atTop (2*(1+primePowerErrorConstant+Real.log 4)),
    htlog2.eventually_ge_atTop 2,htu.eventually_ge_atTop 2,
    htail.eventually_lt_const hε,eventually_gt_atTop (0 : ℕ)] with N ht hlog hlog2 huN htailN hN
  have hNr : (0 : ℝ)<N := by exact_mod_cast hN
  have hpower : (N : ℝ)^e=((N : ℝ)^u)^2 := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hNr.le]
    congr 1
    dsimp only [u]
    norm_num
  have hlo : (N : ℝ)^u≤t N := by
    have hf := Nat.lt_floor_add_one ((N : ℝ)^e)
    change (N : ℝ)^e<(t N : ℝ)+1 at hf
    rw [hpower] at hf
    dsimp only [Function.comp_apply] at huN
    nlinarith
  have hupper : (blockCutoff (t N) J K : ℝ)≤(N : ℝ)^α := by
    have htupper : (t N : ℝ)≤(N : ℝ)^e := Nat.floor_le (Real.rpow_nonneg hNr.le e)
    have hp := pow_le_pow_left₀ (Nat.cast_nonneg (t N)) htupper Q
    have heq : ((N : ℝ)^e)^Q=(N : ℝ)^α := by
      rw [← Real.rpow_natCast,← Real.rpow_mul hNr.le]
      congr 1
      dsimp only [e]
      field_simp
    rw [heq] at hp
    simpa only [blockCutoff,Nat.cast_pow] using hp
  refine ⟨ht,hlo,hupper,iteratedPrimeBlocks_total_mass (t N) J K ht hlog2,?_⟩
  intro i hi
  have hb := iteratedPrimeBlock_empty_bound (t N) J K i N ht hJ hN hi hlog
  have hrem : 32*(blockCutoff (t N) J K+1 : ℝ)/((N : ℝ)*J)≤
      32*((N : ℝ)^α+1)/((N : ℝ)*J) := by gcongr
  linarith

#print axioms exists_occupied_power_prime_blocks
end Erdos371.FiniteSieve
