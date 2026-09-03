import Submission.PrimeLoserSignedCollisions
import Submission.PrimeWinnerBulkUpper

/-! Prime-weighted energy. A subquadratic bound for this weighted energy is
a sufficient signed criterion; its vanishing hypothesis is not asserted. -/
namespace Erdos371
open Finset Filter FiniteSieve
open scoped Topology

noncomputable def primeWinnerPrimeWeightedEnergy (N : ℕ) : ℝ :=
  ∑ p ∈ primeWinnerLabels N, (p : ℝ)*(primeWinnerSum p N)^2

noncomputable def primeWinnerL1 (N : ℕ) : ℝ :=
  ∑ p ∈ primeWinnerLabels N, ‖primeWinnerSum p N‖

lemma primeWinnerLabel_pos (N p : ℕ) (hp : p ∈ primeWinnerLabels N) : 0<p := by
  obtain rfl | hp := mem_insert.mp hp
  · omega
  · exact (Nat.mem_primesBelow.mp hp).2.pos

lemma primeWinnerLabel_le (N p : ℕ) (hN : 0<N) (hp : p ∈ primeWinnerLabels N) : p≤N := by
  obtain rfl | hp := mem_insert.mp hp
  · omega
  · have := (Nat.mem_primesBelow.mp hp).1
    omega

lemma primeWinnerPrimeWeightedEnergy_nonneg (N : ℕ) : 0≤primeWinnerPrimeWeightedEnergy N := by
  unfold primeWinnerPrimeWeightedEnergy
  exact sum_nonneg fun _ _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)

lemma primeWinnerPrimeWeightedEnergy_le_l1 (N : ℕ) (hN : 0<N) :
    primeWinnerPrimeWeightedEnergy N ≤ 3*(N : ℝ)*primeWinnerL1 N := by
  rw [primeWinnerPrimeWeightedEnergy,primeWinnerL1,mul_sum]
  apply sum_le_sum
  intro p hp
  have hpN : (p : ℝ)≤N := by exact_mod_cast primeWinnerLabel_le N p hN hp
  have hbound := primeWinnerSum_norm_le_multiples p N
  have hdiv : (p : ℝ)*((N/p : ℕ) : ℝ) ≤ N := by
    exact_mod_cast Nat.mul_div_le N p
  have hprod : (p : ℝ)*‖primeWinnerSum p N‖ ≤ 3*N := by
    have hh := mul_le_mul_of_nonneg_left hbound (Nat.cast_nonneg (α := ℝ) p)
    nlinarith
  have hh := mul_le_mul_of_nonneg_right hprod (norm_nonneg (primeWinnerSum p N))
  simpa only [mul_assoc,← pow_two,Real.norm_eq_abs,sq_abs] using hh

lemma primeWinnerL1Above_sq_le_primeWeightedEnergy (B N : ℕ) :
    (primeWinnerL1Above B N)^2 ≤
      (∑ p ∈ (primeWinnerLabels N).filter (B < ·), (1 : ℝ)/p)*
        primeWinnerPrimeWeightedEnergy N := by
  let S := (primeWinnerLabels N).filter (B < ·)
  have hcs := sum_sq_le_sum_mul_sum_of_sq_eq_mul S
    (r := fun p => ‖primeWinnerSum p N‖) (f := fun p => (1 : ℝ)/p)
    (g := fun p => (p : ℝ)*(primeWinnerSum p N)^2)
    (by intros; positivity) (by intros; positivity) (fun p hp => by
      have hp0 : (p : ℝ)≠0 := by
        exact_mod_cast (primeWinnerLabel_pos N p (mem_filter.mp hp).1).ne'
      dsimp only
      rw [Real.norm_eq_abs,sq_abs]
      field_simp)
  have hs : (∑ p ∈ S, (p : ℝ)*(primeWinnerSum p N)^2) ≤ primeWinnerPrimeWeightedEnergy N :=
    sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (by intros; positivity)
  exact hcs.trans (mul_le_mul_of_nonneg_left hs (by positivity))

lemma high_primeWinnerLabels_reciprocal_bound (u : ℝ) (hu : 0<u)
    (N : ℕ) (hN : 4≤N) :
    (∑ p ∈ (primeWinnerLabels N).filter (ceilPowerCutoff u N < ·), (1 : ℝ)/p) ≤ 2/u := by
  let S := (primeWinnerLabels N).filter (ceilPowerCutoff u N < ·)
  have hN0 : (0 : ℝ)<N := by exact_mod_cast (by omega : 0<N)
  have hN1 : (1 : ℝ)<N := by exact_mod_cast (by omega : 1<N)
  have hlogN : 0<Real.log N := Real.log_pos hN1
  have hcut : (N : ℝ)^u ≤ ceilPowerCutoff u N := Nat.le_ceil _
  have hpow1 : (1 : ℝ)≤(N : ℝ)^u := Real.one_le_rpow hN1.le hu.le
  have hs : S ⊆ (N+1).primesBelow := by
    intro p hp
    obtain ⟨hp,hBp⟩ := mem_filter.mp hp
    obtain rfl | hp := mem_insert.mp hp
    · have hb : 1≤ceilPowerCutoff u N := by exact_mod_cast hpow1.trans hcut
      omega
    · exact hp
  have hterm (p : ℕ) (hp : p ∈ S) :
      (u*Real.log N)*((1 : ℝ)/p) ≤ Real.log p/p := by
    have hpp := (Nat.mem_primesBelow.mp (hs hp)).2
    have hpl : (N : ℝ)^u ≤ p := hcut.trans (by exact_mod_cast (mem_filter.mp hp).2.le)
    have hlog : u*Real.log N ≤ Real.log p := by
      simpa only [Real.log_rpow hN0] using Real.log_le_log (Real.rpow_pos_of_pos hN0 u) hpl
    simpa only [mul_one_div] using div_le_div_of_nonneg_right hlog (Nat.cast_nonneg p)
  have hm := sum_le_sum hterm
  rw [← mul_sum] at hm
  have htot : (∑ p ∈ S, Real.log p/(p : ℝ)) ≤ primeLogHarmonic N :=
    sum_le_sum_of_subset_of_nonneg hs (fun p _ _ =>
      div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p))
  have hp := primeLogHarmonic_upper N (by omega)
  have hl4 : Real.log 4≤Real.log N := Real.log_le_log (by norm_num) (by exact_mod_cast hN)
  change (∑ p ∈ S, (1 : ℝ)/p) ≤ _
  apply (le_div_iff₀ hu).mpr
  nlinarith

lemma primeWinnerL1Above_power_tendsto_of_primeWeightedEnergy (u : ℝ) (hu : 0<u)
    (hW : Tendsto (fun N : ℕ => primeWinnerPrimeWeightedEnergy N/(N : ℝ)^2)
      atTop (nhds 0)) :
    Tendsto (fun N : ℕ => primeWinnerL1Above (ceilPowerCutoff u N) N/N) atTop (nhds 0) := by
  have ht := (hW.const_mul (2/u)).sqrt
  simp only [mul_zero,Real.sqrt_zero] at ht
  apply squeeze_zero_norm' _ ht
  filter_upwards [eventually_ge_atTop (4 : ℕ)] with N hN
  have hs := (primeWinnerL1Above_sq_le_primeWeightedEnergy (ceilPowerCutoff u N) N).trans
    (mul_le_mul_of_nonneg_right (high_primeWinnerLabels_reciprocal_bound u hu N hN)
      (primeWinnerPrimeWeightedEnergy_nonneg N))
  apply Real.le_sqrt_of_sq_le
  rw [norm_div,Real.norm_natCast,div_pow,Real.norm_eq_abs,sq_abs,← mul_div_assoc]
  exact div_le_div_of_nonneg_right hs (sq_nonneg (N : ℝ))

lemma primeWinnerL1_split_bound (B N : ℕ) :
    primeWinnerL1 N ≤ (((range N).filter fun n => Nat.maxPrimeFac n≤B).card : ℝ)+
      primeWinnerL1Above B N := by
  have he : primeWinnerL1 N =
      (∑ p ∈ (primeWinnerLabels N).filter (·≤B), ‖primeWinnerSum p N‖)+primeWinnerL1Above B N := by
    unfold primeWinnerL1 primeWinnerL1Above
    simpa only [not_le] using (sum_filter_add_sum_filter_not (primeWinnerLabels N)
      (fun p => p≤B) (fun p => ‖primeWinnerSum p N‖)).symm
  rw [he]
  exact add_le_add (primeWinnerSum_low_norm_sum_le B N) le_rfl

lemma ceilPowerCutoff_succ_log_bound (u : ℝ) (hu : 0≤u) (N : ℕ) (hN : 1≤N) :
    Real.log (ceilPowerCutoff u N+1 : ℝ) ≤ Real.log 3+u*Real.log N := by
  have hN0 : (0 : ℝ)<N := by exact_mod_cast (by omega : 0<N)
  have hpow1 : (1 : ℝ)≤(N : ℝ)^u := Real.one_le_rpow (by exact_mod_cast hN) hu
  have hceil := Nat.ceil_lt_add_one (Real.rpow_nonneg hN0.le u)
  change (ceilPowerCutoff u N : ℝ)<(N : ℝ)^u+1 at hceil
  calc
    _ ≤ Real.log (3*(N : ℝ)^u) := Real.log_le_log (by positivity) (by linarith)
    _ = _ := by rw [Real.log_mul (by norm_num) (Real.rpow_pos_of_pos hN0 u).ne',Real.log_rpow hN0]

/-- Prime-weighted subquadratic energy is enough for the total absolute
prime-group imbalance to be o(N). This hypothesis is weaker than a full
near-linear unweighted energy bound. -/
theorem primeWinnerL1_tendsto_of_primeWeightedEnergy
    (hW : Tendsto (fun N : ℕ => primeWinnerPrimeWeightedEnergy N/(N : ℝ)^2)
      atTop (nhds 0)) :
    Tendsto (fun N : ℕ => primeWinnerL1 N/N) atTop (nhds 0) := by
  apply tendsto_order.mpr
  constructor
  · intro ε hε
    exact Eventually.of_forall fun N => hε.trans_le (by unfold primeWinnerL1; positivity)
  · intro ε hε
    let u : ℝ := ε/32
    have hu : 0<u := by dsimp [u]; positivity
    have hhigh := primeWinnerL1Above_power_tendsto_of_primeWeightedEnergy u hu hW
    have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    have herror := (nat_sqrt_add_one_div_tendsto_zero.add
      ((tendsto_const_nhds (x := (8*Real.log 3 : ℝ))).div_atTop hlog)).add hhigh
    simp only [add_zero] at herror
    have hpos : 0<ε-8*u := by dsimp [u]; linarith
    filter_upwards [herror.eventually_lt_const hpos,eventually_gt_atTop (1 : ℕ)] with N he hN
    have hN0 : (0 : ℝ)<N := by exact_mod_cast (by omega : 0<N)
    have hlogN : 0<Real.log N := Real.log_pos (by exact_mod_cast hN)
    have hl := div_le_div_of_nonneg_right (ceilPowerCutoff_succ_log_bound u hu.le N (by omega)) hlogN.le
    have hs := smooth_count_ratio_log_bound (ceilPowerCutoff u N) N hN
    have hsplit := div_le_div_of_nonneg_right (primeWinnerL1_split_bound (ceilPowerCutoff u N) N) hN0.le
    have hrewrite : (Real.log 3+u*Real.log N)/Real.log N = Real.log 3/Real.log N+u := by field_simp
    rw [hrewrite] at hl
    rw [add_div] at hsplit
    have he' : ((N.sqrt+1 : ℝ)/N+8*(Real.log 3/Real.log N))+
        primeWinnerL1Above (ceilPowerCutoff u N) N/N < ε-8*u := by
      simpa only [mul_div_assoc] using he
    linarith

/-- This is an equivalence with absolute group balance, not an unconditional
assertion of either limit. -/
theorem primeWeightedEnergy_tendsto_iff_primeWinnerL1 :
    Tendsto (fun N : ℕ => primeWinnerPrimeWeightedEnergy N/(N : ℝ)^2) atTop (nhds 0) ↔
      Tendsto (fun N : ℕ => primeWinnerL1 N/N) atTop (nhds 0) := by
  constructor
  · exact primeWinnerL1_tendsto_of_primeWeightedEnergy
  · intro hL
    have ht := hL.const_mul 3
    simp only [mul_zero] at ht
    apply squeeze_zero' (Eventually.of_forall fun N => div_nonneg
      (primeWinnerPrimeWeightedEnergy_nonneg N) (sq_nonneg _)) _ ht
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
    have hN0 : (N : ℝ)≠0 := by exact_mod_cast hN.ne'
    have h := div_le_div_of_nonneg_right (primeWinnerPrimeWeightedEnergy_le_l1 N hN) (sq_nonneg (N : ℝ))
    convert h using 1
    field_simp

/-- A weaker sufficient weighted-energy criterion for the ORIGINAL conjecture.
The necessary arithmetic cancellation has not been proved here. -/
theorem density_of_primeWeightedEnergy
    (hW : Tendsto (fun N : ℕ => primeWinnerPrimeWeightedEnergy N/(N : ℝ)^2)
      atTop (nhds 0)) :
    {n | Nat.maxPrimeFac (n+1)>Nat.maxPrimeFac n}.HasDensity (1/2) := by
  rw [density_iff_signed_count]
  apply squeeze_zero_norm (fun N => ?_) (primeWinnerL1_tendsto_of_primeWeightedEnergy hW)
  rw [norm_div,Real.norm_natCast,← primeWinnerSum_total]
  exact div_le_div_of_nonneg_right (norm_sum_le _ _) (Nat.cast_nonneg N)

#print axioms primeWeightedEnergy_tendsto_iff_primeWinnerL1
#print axioms density_of_primeWeightedEnergy
end Erdos371
