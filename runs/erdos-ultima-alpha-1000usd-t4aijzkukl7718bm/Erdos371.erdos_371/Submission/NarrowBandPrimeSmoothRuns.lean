import Submission.NarrowPrimeLoserSieve
import Submission.CriticalPrimeSmoothNeighborRuns

/-! Retaining the smaller-prime band improves the smooth-neighbor run
range from log-log exponent r>2 to r>1. This remains a boundary theorem. -/
namespace Erdos371
open Finset Filter FiniteSieve DilationSpectrum
open scoped Topology

lemma narrowBand_criticalPrimeRun_eventual_bound (r : ℝ) (hr : 0 ≤ r) :
    ∀ᶠ X : ℕ in atTop,
      ((roughNeighborPrimes (criticalPrimeRunCutoff r X) X).card : ℝ)*Real.log X/X ≤
        (4*narrowLoserSieveConstant*(2*Real.log 2+1))/(1+Real.log (Real.log X))^(r-1) +
          (16*(2 : ℝ)^65)*(Real.log X)^3/(X : ℝ)^(1/2 : ℝ) := by
  have hsmall : Tendsto (fun X : ℕ => 4*Real.log X/(X : ℝ)) atTop (𝓝 0) := by
    simpa only [Real.rpow_one,mul_div_assoc,mul_zero] using
      (log_nat_rpow_div_rpow_tendsto_zero 1 1 (by norm_num)).const_mul 4
  filter_upwards [criticalPrimeRun_data r hr,hsmall.eventually_le_const
    (by norm_num : (0 : ℝ) < 1),eventually_ge_atTop (2 : ℕ)] with X hd hsmall hX
  obtain ⟨hLN,hW1,hWL,_,hKX⟩ := hd
  let K := criticalPrimeRunCutoff r X
  let H := 2*K+1
  let W := criticalPrimeRunWeight r X
  let B : ℝ := 1+Real.log (Real.log X)
  let D : ℝ := 2*Real.log 2+1
  have hX0 : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hL0 : 0 < Real.log X := by linarith
  have hH : 0 < H := by dsimp [H]; omega
  have hH0 : (0 : ℝ) < H := by exact_mod_cast hH
  have h2 : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  have hLL : 0 ≤ Real.log (Real.log X) := Real.log_nonneg hLN
  have hB0 : 0 < B := by dsimp [B]; positivity
  have hD0 : 0 ≤ D := by dsimp [D]; positivity
  have hKW : (K : ℝ) ≤ W := Nat.floor_le (by linarith)
  have hHW : (H : ℝ) ≤ 4*W := by dsimp [H]; push_cast; linarith
  have hHL : (H : ℝ) ≤ 4*Real.log X := hHW.trans (by linarith)
  have hHX : H ≤ X := by
    have h := (div_le_iff₀ hX0).mp hsmall
    have hh : (H : ℝ) ≤ X := by linarith
    exact_mod_cast hh
  have hlog4 : Real.log (4 : ℝ) = 2*Real.log 2 := by
    rw [show (4 : ℝ) = 2^2 by norm_num,Real.log_pow]
    norm_num
  have hlogH : 1+Real.log H ≤ D*B := by
    have hh := Real.log_le_log hH0 hHL
    rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hL0.ne',hlog4] at hh
    dsimp [D,B]
    nlinarith [mul_nonneg h2 hLL]
  have hC : 0 ≤ narrowLoserSieveConstant := by unfold narrowLoserSieveConstant; positivity
  have hmain : narrowLoserSieveConstant*H*(1+Real.log H)/Real.log X ≤
      4*narrowLoserSieveConstant*D/B^(r-1) := by
    have hprod := mul_le_mul hHW hlogH
      (by have := Real.log_natCast_nonneg H; positivity : 0 ≤ 1+Real.log H)
      (by linarith : 0 ≤ 4*W)
    have hh := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hprod hC) hL0.le
    apply (show narrowLoserSieveConstant*H*(1+Real.log H)/Real.log X ≤
      narrowLoserSieveConstant*(4*W)*(D*B)/Real.log X by
        simpa only [mul_assoc] using hh).trans_eq
    rw [Real.rpow_sub hB0,Real.rpow_one]
    dsimp only [W,criticalPrimeRunWeight,B]
    field_simp
  have herr : (2 : ℝ)^65*(H : ℝ)^2*Real.log X/(X : ℝ)^(1/2 : ℝ) ≤
      (16*(2 : ℝ)^65)*(Real.log X)^3/(X : ℝ)^(1/2 : ℝ) := by
    have hs := pow_le_pow_left₀ (Nat.cast_nonneg H) hHL 2
    have hh := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hs (show 0 ≤ (2 : ℝ)^65 by positivity)) hL0.le)
      (Real.rpow_nonneg hX0.le (1/2 : ℝ))
    apply hh.trans_eq
    ring
  have hcard := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
    ((Nat.cast_le (α := ℝ)).mpr (roughNeighborPrimes_card_le_narrowLoser K X (by omega) hKX))
    hL0.le) hX0.le
  exact (hcard.trans (narrowLoserSet_scaled_log_bound X H (by omega) hHX)).trans
    (add_le_add hmain herr)

/-- The loss in the logarithm of the cofactor bound is now only first
order, allowing every log-log exponent r>1. -/
theorem narrowBand_criticalPrimeRun_scaled_count_tendsto (r : ℝ) (hr : 1 < r) :
    Tendsto (fun X : ℕ =>
      ((roughNeighborPrimes (criticalPrimeRunCutoff r X) X).card : ℝ)*Real.log X/X)
      atTop (𝓝 0) := by
  have hL : Tendsto (fun X : ℕ => Real.log X) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hB : Tendsto (fun X : ℕ => 1+Real.log (Real.log X)) atTop atTop :=
    tendsto_const_nhds.add_atTop (Real.tendsto_log_atTop.comp hL)
  have hmain : Tendsto (fun X : ℕ =>
      (4*narrowLoserSieveConstant*(2*Real.log 2+1))/(1+Real.log (Real.log X))^(r-1))
      atTop (𝓝 0) := tendsto_const_nhds.div_atTop
        ((tendsto_rpow_atTop (by linarith : 0 < r-1)).comp hB)
  have herr := (log_nat_pow_div_rpow_tendsto_zero 3 (1/2)
    (by norm_num)).const_mul (16*(2 : ℝ)^65)
  have ht := hmain.add herr
  simp only [mul_zero,add_zero] at ht
  apply squeeze_zero' (Eventually.of_forall (fun X => by
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg X))
      (Nat.cast_nonneg X))) _ ht
  simpa only [mul_div_assoc] using narrowBand_criticalPrimeRun_eventual_bound r (by linarith)

theorem narrowBand_criticalPrimeRun_proportion_tendsto (r : ℝ) (hr : 1 < r) :
    Tendsto (fun X : ℕ => ((roughNeighborPrimes (criticalPrimeRunCutoff r X) X).card : ℝ)/
      (narrowPrimeBand 1 2 X).card) atTop (𝓝 0) := by
  have hden := narrowPrimeBand_card_scaled_limit 1 2 (by norm_num) (by norm_num)
  norm_num only at hden
  have ht := (narrowBand_criticalPrimeRun_scaled_count_tendsto r hr).div hden one_ne_zero
  simp only [zero_div] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with X hX
  have hx : (X : ℝ) ≠ 0 := by exact_mod_cast (show X ≠ 0 by omega)
  have hl : Real.log X ≠ 0 := (Real.log_pos (by exact_mod_cast hX)).ne'
  simp only [Pi.div_apply]
  field_simp

/-- Almost all primes in the dyadic band have the full smooth-neighbor
run of length floor(log p/(1+log log p)^r), for every r>1. -/
theorem narrowBand_criticalOwnScale_proportion_tendsto (r : ℝ) (hr : 1 < r) :
    Tendsto (fun X : ℕ => ((criticalRoughNeighborPrimesAtOwnScale r X).card : ℝ)/
      (narrowPrimeBand 1 2 X).card) atTop (𝓝 0) := by
  let s : ℝ := (r+1)/2
  have hs : 1 < s := by dsimp [s]; linarith
  have hsr : s < r := by dsimp [s]; linarith
  apply squeeze_zero' (Eventually.of_forall (fun _ => by positivity)) _
    (narrowBand_criticalPrimeRun_proportion_tendsto s hs)
  filter_upwards [criticalPrimeRunCutoff_dyadic_domination r s (by linarith) hsr] with X hdom
  have hsub : criticalRoughNeighborPrimesAtOwnScale r X ⊆
      roughNeighborPrimes (criticalPrimeRunCutoff s X) X := by
    intro p hp
    obtain ⟨hpband,k,hk,hk1,hrough⟩ := mem_filter.mp hp
    obtain ⟨_,hpX,hp2X⟩ := dyadicPrimeBand_nat_data hpband
    exact mem_filter.mpr ⟨hpband,k,hk.trans (hdom p hpX hp2X),hk1,hrough⟩
  exact div_le_div_of_nonneg_right ((Nat.cast_le (α := ℝ)).mpr (card_le_card hsub))
    (Nat.cast_nonneg _)

theorem infinitely_many_narrowBand_prime_smooth_neighbor_runs (r : ℝ) (hr : 1 < r) :
    {p : ℕ | p.Prime ∧ ∀ k ∈ Icc 1 (criticalPrimeRunCutoff r p),
      Nat.maxPrimeFac (k*p-1) < p ∧ Nat.maxPrimeFac (k*p+1) < p}.Infinite := by
  let s : ℝ := (r+1)/2
  have hs : 1 < s := by dsimp [s]; linarith
  have hsr : s < r := by dsimp [s]; linarith
  have hden := narrowPrimeBand_card_scaled_limit 1 2 (by norm_num) (by norm_num)
  norm_num only at hden
  apply Set.infinite_of_forall_exists_gt
  intro M
  obtain ⟨X,hd,hdom,hbad,hband,hM⟩ := ((criticalPrimeRun_data s (by linarith)).and
    ((criticalPrimeRunCutoff_dyadic_domination r s (by linarith) hsr).and
    (((narrowBand_criticalPrimeRun_scaled_count_tendsto s hs).eventually_lt_const
      (by norm_num : (0 : ℝ) < 1/4)).and
    ((hden.eventually_const_lt (by norm_num : (1/2 : ℝ) < 1)).and
      (eventually_ge_atTop M))))).exists
  have hlt : (roughNeighborPrimes (criticalPrimeRunCutoff s X) X).card <
      (narrowPrimeBand 1 2 X).card := by
    by_contra h
    have hle : ((narrowPrimeBand 1 2 X).card : ℝ) ≤
        (roughNeighborPrimes (criticalPrimeRunCutoff s X) X).card := by exact_mod_cast (not_lt.mp h)
    have hle' := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hle (Real.log_natCast_nonneg X)) (Nat.cast_nonneg (α := ℝ) X)
    linarith
  have hnot : ¬narrowPrimeBand 1 2 X ⊆ roughNeighborPrimes (criticalPrimeRunCutoff s X) X := by
    intro h
    exact (not_le_of_gt hlt) (card_le_card h)
  obtain ⟨p,hp⟩ := sdiff_nonempty.mpr hnot
  obtain ⟨hpband,hpnot⟩ := mem_sdiff.mp hp
  obtain ⟨hprime,hpX,hp2X⟩ := dyadicPrimeBand_nat_data hpband
  refine ⟨p,⟨hprime,?_⟩,by omega⟩
  intro k hk
  have hrun := smooth_neighbors_of_not_mem_roughNeighborPrimes
    (criticalPrimeRunCutoff s X) X p hd.2.2.2.2 hpband hpnot
  obtain ⟨hk1,hkK⟩ := mem_Icc.mp hk
  exact hrun k (mem_Icc.mpr ⟨hk1,hkK.trans (hdom p hpX hp2X)⟩)

#print axioms narrowBand_criticalPrimeRun_eventual_bound
#print axioms narrowBand_criticalPrimeRun_scaled_count_tendsto
#print axioms narrowBand_criticalOwnScale_proportion_tendsto
#print axioms infinitely_many_narrowBand_prime_smooth_neighbor_runs
end Erdos371
