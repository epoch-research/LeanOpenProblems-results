import Submission.SubpowerOccupiedBand
import Submission.ExponentialPrimePatternTail

/-! Density-zero thin-band and exceptional-set bounds for short factors of
mixed complementary indices. No independence of the exceptions is assumed. -/
namespace Erdos371
open Finset Filter FiniteSieve
open scoped Topology

lemma thinPrimeBlockCount_antitone (P Q : Finset ℕ) (hPQ : P ⊆ Q) (k N : ℕ) :
    thinPrimeBlockCount Q k N ≤ thinPrimeBlockCount P k N := by
  apply card_le_card
  intro n hn
  obtain ⟨hn,hQ⟩ := mem_filter.mp hn
  refine mem_filter.mpr ⟨hn,?_⟩
  have hloc := activeBlockPrimes_congr P (activePrimeAtoms P n) (activePrimeAtoms Q n)
    (activePrimeAtoms_locality P Q hPQ n)
  rw [hloc]
  exact (card_le_card (activeBlockPrimes_mono P Q hPQ (activePrimeAtoms Q n))).trans hQ

lemma thin_subpower_band_zero (B W : ℕ → ℕ) (k : ℕ)
    (hBt : Tendsto B atTop atTop)
    (hB : Tendsto (fun N => Real.log (B N+1 : ℝ)/Real.log N) atTop (𝓝 0))
    (hW : ∀ k : ℕ, ∀ᶠ N in atTop, (B N)^k ≤ W N) :
    Tendsto (fun N : ℕ => (thinPrimeBlockCount (largePrimeSet (B N) (W N)) k N : ℝ)/N)
      atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨J,hJ,hJk,hJs⟩ := ((eventually_gt_atTop (0 : ℕ)).and
    ((eventually_ge_atTop (8*k)).and
      ((tendsto_const_div_atTop_nhds_zero_nat (16 : ℝ)).eventually_lt_const
        (show (0 : ℝ) < ε/2 by positivity)))).exists
  have hlog := (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hBt)).eventually_ge_atTop
    (2*(1+primePowerErrorConstant+Real.log 4))
  have htail : Tendsto (fun N : ℕ => 32*((B N : ℝ)^(2^J)+1)/(N*J)) atTop (𝓝 0) := by
    have hb : Tendsto (fun N : ℕ => (B N : ℝ)^(2^J)/N) atTop (𝓝 0) := by
      apply squeeze_zero (fun N => by positivity) _ (subpower_pow_div_tendsto_zero B hB (2^J))
      intro N
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
      exact pow_le_pow_left₀ (Nat.cast_nonneg _) (by linarith) _
    have hh := (hb.add tendsto_one_div_atTop_nhds_zero_nat).const_mul (32/(J : ℝ))
    simp only [add_zero,mul_zero] at hh
    convert hh using 1
    funext N
    ring
  filter_upwards [hBt.eventually_gt_atTop 1,hlog,hW (2^J),
    htail.eventually_lt_const (show (0 : ℝ) < ε/2 by positivity),
    eventually_gt_atTop (0 : ℕ)] with N hb hl hw ht hN
  have hs := iteratedPrimeBlock_thin_bound (B N) J 1 0 k N hb hJ hJk hN (by omega) hl
  have hsub : iteratedPrimeBlock (B N) J 0 ⊆ largePrimeSet (B N) (W N) := by
    intro p hp
    obtain ⟨hpp,hpl,hpu⟩ := (mem_largePrimeSet_iff p _ _).mp hp
    simp only [blockCutoff,Nat.zero_add,Nat.mul_zero,pow_zero,pow_one,Nat.mul_one] at hpl hpu
    exact (mem_largePrimeSet_iff p _ _).mpr ⟨hpp,hpl,hpu.trans hw⟩
  have hc : (thinPrimeBlockCount (largePrimeSet (B N) (W N)) k N : ℝ)/N ≤
      (thinPrimeBlockCount (iteratedPrimeBlock (B N) J 0) k N : ℝ)/N := by
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
    exact_mod_cast thinPrimeBlockCount_antitone _ _ hsub k N
  simp only [blockCutoff,Nat.mul_one,Nat.cast_pow] at hs
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg N))]
  exact hc.trans_lt (hs.trans_lt (by linarith))

lemma shifted_indicator_mean_zero (Q : ℕ → ℕ → Prop) [∀ N n, Decidable (Q N n)]
    (h : Tendsto (fun N : ℕ => (∑ n ∈ range N, if Q N n then (1 : ℝ) else 0)/N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => (∑ n ∈ range N, if Q N (n+1) then (1 : ℝ) else 0)/N) atTop (𝓝 0) := by
  classical
  have ht := h.add tendsto_one_div_atTop_nhds_zero_nat
  simp only [add_zero] at ht
  apply squeeze_zero (fun N => div_nonneg (sum_nonneg fun n _ => by split_ifs <;> norm_num) (Nat.cast_nonneg N)) _ ht
  intro N
  rw [← add_div]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
  let f : ℕ → ℝ := fun n => if Q N n then 1 else 0
  have hs := sum_range_succ' f N
  rw [sum_range_succ] at hs
  have h0 : 0 ≤ f 0 := by dsimp [f]; split_ifs <;> norm_num
  have hN : f N ≤ 1 := by dsimp [f]; split_ifs <;> norm_num
  change (∑ n ∈ range N, f (n+1)) ≤ (∑ n ∈ range N, f n)+1
  linarith

lemma short_band_exp_exception_zero (B : ℕ → ℕ) (k : ℕ) (Q : ℕ → ℕ → Prop) [∀ N n, Decidable (Q N n)]
    (hBt : Tendsto B atTop atTop)
    (hQ : Tendsto (fun N : ℕ => (∑ n ∈ range N, if Q N n then (1 : ℝ) else 0)/N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => (∑ n ∈ range N, if Q N n then
      (2 : ℝ)^(activeBlockPrimes (largePrimeSet (B N) ((B N)^k))
        (activePrimeAtoms (largePrimeSet (B N) ((B N)^k)) (n+1))).card else 0)/N) atTop (𝓝 0) := by
  classical
  let P : ℕ → Finset ℕ := fun N => largePrimeSet (B N) ((B N)^k)
  let E : ℕ → Finset ℕ := fun N => (range N).filter (Q N)
  have he : Tendsto (fun N : ℕ => ((E N).card : ℝ)/N) atTop (𝓝 0) := by
    simpa only [sum_boole,E] using hQ
  have hlog := (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hBt)).atTop_div_const
    (Real.log_pos (by norm_num : (1 : ℝ) < 2))
  have hd : ∀ᶠ N in atTop, (∀ p ∈ P N, p.Prime) ∧
      primeReciprocalMass (P N) ≤ 16*(k+1 : ℝ) ∧ E N ⊆ range N := by
    filter_upwards [hBt.eventually_gt_atTop 1,hlog.eventually_ge_atTop 2] with N hb hl
    refine ⟨fun p hp => ((mem_largePrimeSet_iff p _ _).mp hp).1,?_,filter_subset _ _⟩
    have hh := short_power_band_mass_upper (B N) k hb hl
    have hn := primeReciprocalMass_nonneg (P N)
    change 2*primeReciprocalMass (P N) ≤ 16*(k+1 : ℝ) at hh
    linarith
  have hh := prime_pattern_exponential_exception_zero P E (16*(k+1 : ℝ)) hd he
  simpa only [E,P,sum_filter] using hh

#print axioms thin_subpower_band_zero
#print axioms short_band_exp_exception_zero
end Erdos371
