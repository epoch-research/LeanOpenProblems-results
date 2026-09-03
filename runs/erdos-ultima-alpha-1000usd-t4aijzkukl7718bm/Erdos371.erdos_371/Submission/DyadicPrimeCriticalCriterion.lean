import Submission.PrimeWindowWeightedCompactness
import Submission.PrimeWinnerPrimeWeightedEnergy
import Submission.SingleDyadicWindowCriterion

/-! A conditional critical-energy criterion on the fixed dyadic window.
The energy in this file is NOT divided by a growing harmonic mass.
Its decay is not proved here. -/
namespace Erdos371
open Finset Filter FiniteSieve
open scoped Topology
set_option autoImplicit false

noncomputable def dyadicPrimeCriticalEnergy (N : ℕ) : ℝ :=
  primeWindowWeightedEnergy (fun _ => 1) 2 N

noncomputable def dyadicPrimeCurrentL1 (N : ℕ) : ℝ :=
  ∑ p ∈ primeWinnerLabels (2*N), |primeWindowCurrent 2 N p|

noncomputable def dyadicPrimeCurrentL1Above (B N : ℕ) : ℝ :=
  ∑ p ∈ (primeWinnerLabels (2*N)).filter (B < ·), |primeWindowCurrent 2 N p|

lemma dyadicPrimeCriticalEnergy_nonneg (N : ℕ) : 0≤dyadicPrimeCriticalEnergy N := by
  unfold dyadicPrimeCriticalEnergy primeWindowWeightedEnergy
  positivity

lemma primeWindowCurrent_eq_sum_filter (a N p : ℕ) (ha : 1≤a) :
    primeWindowCurrent a N p =
      ∑ n ∈ (Ico N (a*N)).filter (fun n => primeWinner n=p), factorSign n/n := by
  unfold primeWindowCurrent rawPrimeWinnerHarmonic
  rw [← sum_Ico_eq_sub _ (show N≤a*N by nlinarith),sum_filter]
  rfl

lemma dyadicPrimeCurrent_total (N : ℕ) :
    (∑ p ∈ primeWinnerLabels (2*N), primeWindowCurrent 2 N p) =
      rawHarmonicSum factorSign (2*N)-rawHarmonicSum factorSign N := by
  simp only [primeWindowCurrent_eq_sum_filter 2 N _ (by omega)]
  rw [sum_fiberwise_of_maps_to (fun n hn =>
    primeWinner_mem_labels (2*N) n (mem_range.mpr (mem_Ico.mp hn).2))]
  exact sum_Ico_eq_sub _ (by omega)

lemma dyadicPrimeCurrent_low_bound (B N : ℕ) (hN : 0<N) :
    (∑ p ∈ (primeWinnerLabels (2*N)).filter (·≤B), |primeWindowCurrent 2 N p|) ≤
      (((range (2*N)).filter fun n => Nat.maxPrimeFac n≤B).card : ℝ)/N := by
  let P := (primeWinnerLabels (2*N)).filter (·≤B)
  let S := (Ico N (2*N)).filter fun n => primeWinner n∈P
  have hNr : (0 : ℝ)<N := by exact_mod_cast hN
  calc
    _ ≤ ∑ p ∈ P, primeWindowMass 2 N p :=
      sum_le_sum (fun p _ => primeWindowCurrent_abs_le_mass 2 N p (by omega))
    _ = ∑ n ∈ S, (1 : ℝ)/n := sum_fiberwise_eq_sum_filter _ _ _ _
    _ ≤ ∑ _n ∈ S, (1 : ℝ)/N := by
      apply sum_le_sum
      intro n hn
      apply one_div_le_one_div_of_le hNr
      exact_mod_cast (mem_Ico.mp (mem_filter.mp hn).1).1
    _ = (S.card : ℝ)/N := by simp only [sum_const,nsmul_eq_mul,mul_one_div]
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ hNr.le
      apply Nat.cast_le.mpr
      apply card_le_card
      intro n hn
      obtain ⟨hn,hp⟩ := mem_filter.mp hn
      apply mem_filter.mpr
      exact ⟨mem_range.mpr (mem_Ico.mp hn).2,
        (le_max_left (Nat.maxPrimeFac n) _).trans (mem_filter.mp hp).2⟩

lemma dyadicPrimeCurrent_split_bound (B N : ℕ) (hN : 0<N) :
    dyadicPrimeCurrentL1 N ≤
      (((range (2*N)).filter fun n => Nat.maxPrimeFac n≤B).card : ℝ)/N+
        dyadicPrimeCurrentL1Above B N := by
  have he : dyadicPrimeCurrentL1 N =
      (∑ p ∈ (primeWinnerLabels (2*N)).filter (·≤B), |primeWindowCurrent 2 N p|)+
        dyadicPrimeCurrentL1Above B N := by
    unfold dyadicPrimeCurrentL1 dyadicPrimeCurrentL1Above
    simpa only [not_le] using (sum_filter_add_sum_filter_not (primeWinnerLabels (2*N))
      (fun p => p≤B) (fun p => |primeWindowCurrent 2 N p|)).symm
  rw [he]
  exact add_le_add (dyadicPrimeCurrent_low_bound B N hN) le_rfl

lemma dyadicPrimeCurrent_high_sq_bound (B N : ℕ) (hN : 0<N) :
    (dyadicPrimeCurrentL1Above B N)^2 ≤
      (∑ p ∈ (primeWinnerLabels (2*N)).filter (B < ·), (1 : ℝ)/p)*
        dyadicPrimeCriticalEnergy N := by
  let S := (primeWinnerLabels (2*N)).filter (B < ·)
  have hcs := sum_sq_le_sum_mul_sum_of_sq_eq_mul S
    (r := fun p => |primeWindowCurrent 2 N p|) (f := fun p => (1 : ℝ)/p)
    (g := fun p => (p : ℝ)*(primeWindowCurrent 2 N p)^2)
    (by intros; positivity) (by intros; positivity) (fun p hp => by
      have hp0 : (p : ℝ)≠0 := by
        exact_mod_cast (primeWinnerLabel_pos (2*N) p (mem_filter.mp hp).1).ne'
      dsimp only
      rw [sq_abs]
      field_simp)
  have hs : (∑ p ∈ S, (p : ℝ)*(primeWindowCurrent 2 N p)^2) ≤
      dyadicPrimeCriticalEnergy N := by
    unfold dyadicPrimeCriticalEnergy primeWindowWeightedEnergy
    simp only [one_mul]
    apply sum_le_sum_of_subset_of_nonneg _ (by intros; positivity)
    intro p hp
    exact mem_range.mpr (by
      have := primeWinnerLabel_le (2*N) p (by omega) (mem_filter.mp hp).1
      omega)
  exact hcs.trans (mul_le_mul_of_nonneg_left hs (by positivity))

lemma dyadicPrimeCurrent_high_zero_of_criticalEnergy (u : ℝ) (hu : 0<u)
    (hE : Tendsto dyadicPrimeCriticalEnergy atTop (𝓝 0)) :
    Tendsto (fun N => dyadicPrimeCurrentL1Above (ceilPowerCutoff u (2*N)) N)
      atTop (𝓝 0) := by
  have ht := (hE.const_mul (2/u)).sqrt
  simp only [mul_zero,Real.sqrt_zero] at ht
  apply squeeze_zero_norm' _ ht
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
  have hs := (dyadicPrimeCurrent_high_sq_bound (ceilPowerCutoff u (2*N)) N (by omega)).trans
    (mul_le_mul_of_nonneg_right (high_primeWinnerLabels_reciprocal_bound u hu (2*N) (by omega))
      (dyadicPrimeCriticalEnergy_nonneg N))
  apply Real.le_sqrt_of_sq_le
  simpa only [Real.norm_eq_abs,sq_abs] using hs

/-- Decay at the critical weight controls absolute prime-current imbalance
on [N,2N). No such decay is asserted without the hypothesis. -/
theorem dyadicPrimeCurrentL1_zero_of_criticalEnergy
    (hE : Tendsto dyadicPrimeCriticalEnergy atTop (𝓝 0)) :
    Tendsto dyadicPrimeCurrentL1 atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro ε hε
    exact Eventually.of_forall fun N => hε.trans_le (by unfold dyadicPrimeCurrentL1; positivity)
  · intro ε hε
    let u : ℝ := ε/64
    have hu : 0<u := by dsimp [u]; positivity
    have hhigh := dyadicPrimeCurrent_high_zero_of_criticalEnergy u hu hE
    have hdouble : Tendsto (fun N : ℕ => 2*N) atTop atTop :=
      tendsto_atTop_mono (fun N => by dsimp; omega) tendsto_id
    have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    have hsmall := (nat_sqrt_add_one_div_tendsto_zero.add
      ((tendsto_const_nhds (x := (8*Real.log 3 : ℝ))).div_atTop hlog)).comp hdouble
    have herror := (hsmall.const_mul 2).add hhigh
    simp only [add_zero,mul_zero] at herror
    have hpos : 0<ε-16*u := by dsimp [u]; linarith
    filter_upwards [herror.eventually_lt_const hpos,eventually_gt_atTop (1 : ℕ)] with N he hN
    have hN0 : (0 : ℝ)<N := by exact_mod_cast (by omega : 0<N)
    have hlogN : 0<Real.log (2*N : ℕ) := Real.log_pos (by exact_mod_cast (show 1<2*N by omega))
    have hl := div_le_div_of_nonneg_right
      (ceilPowerCutoff_succ_log_bound u hu.le (2*N) (by omega)) hlogN.le
    have hs := smooth_count_ratio_log_bound (ceilPowerCutoff u (2*N)) (2*N) (by omega)
    have hsplit := dyadicPrimeCurrent_split_bound (ceilPowerCutoff u (2*N)) N (by omega)
    have hrewrite : (Real.log 3+u*Real.log (2*N : ℕ))/Real.log (2*N : ℕ) =
        Real.log 3/Real.log (2*N : ℕ)+u := by field_simp
    rw [hrewrite] at hl
    have hratio : (((range (2*N)).filter fun n => Nat.maxPrimeFac n≤ceilPowerCutoff u (2*N)).card : ℝ)/N =
        2*((((range (2*N)).filter fun n => Nat.maxPrimeFac n≤ceilPowerCutoff u (2*N)).card : ℝ)/(2*N : ℕ)) := by
      push_cast
      ring
    rw [hratio] at hsplit
    have he' : 2*(((2*N).sqrt+1 : ℝ)/(2*N : ℕ)+8*(Real.log 3/Real.log (2*N : ℕ)))+
        dyadicPrimeCurrentL1Above (ceilPowerCutoff u (2*N)) N < ε-16*u := by
      simpa only [Function.comp_apply,mul_div_assoc] using he
    linarith

lemma dyadicPrimeCurrent_zero_off_labels (N p : ℕ)
    (hp : p∉primeWinnerLabels (2*N)) : primeWindowCurrent 2 N p=0 := by
  rw [primeWindowCurrent_eq_sum_filter 2 N p (by omega)]
  apply sum_eq_zero
  intro n hn
  obtain ⟨hn,he⟩ := mem_filter.mp hn
  exact False.elim (hp (he ▸ primeWinner_mem_labels (2*N) n
    (mem_range.mpr (mem_Ico.mp hn).2)))

lemma dyadicPrimeCurrentL1_eq_range (N : ℕ) :
    dyadicPrimeCurrentL1 N = ∑ p ∈ range (2*N+1), |primeWindowCurrent 2 N p| := by
  by_cases hN : N=0
  · subst N
    simp [dyadicPrimeCurrentL1,primeWindowCurrent]
  unfold dyadicPrimeCurrentL1
  apply sum_subset
  · intro p hp
    have := primeWinnerLabel_le (2*N) p (by omega) hp
    exact mem_range.mpr (by omega)
  · intro p _ hp
    rw [dyadicPrimeCurrent_zero_off_labels N p hp,abs_zero]

lemma dyadicPrimeCriticalEnergy_le_l1 (N : ℕ) :
    dyadicPrimeCriticalEnergy N≤4*dyadicPrimeCurrentL1 N := by
  by_cases hN : N=0
  · subst N
    simp [dyadicPrimeCriticalEnergy,primeWindowWeightedEnergy,primeWindowCurrent,
      dyadicPrimeCurrentL1]
  rw [dyadicPrimeCurrentL1_eq_range,mul_sum]
  unfold dyadicPrimeCriticalEnergy primeWindowWeightedEnergy
  simp only [one_mul]
  apply sum_le_sum
  intro p _
  have hm := mul_le_mul_of_nonneg_left (primeWindowCurrent_abs_le_mass 2 N p (by omega))
    (Nat.cast_nonneg (α := ℝ) p)
  have hb := primeWindowMass_mul_label_bound 2 N p (by omega)
  have hh := mul_le_mul_of_nonneg_right (hm.trans hb) (abs_nonneg (primeWindowCurrent 2 N p))
  norm_num only [Nat.cast_ofNat] at hh
  simpa only [mul_assoc,← pow_two,sq_abs] using hh

/-- Equivalence with absolute current balance, not with the conjecture itself.
Both equivalent limits are still unproved. -/
theorem dyadicPrimeCriticalEnergy_zero_iff_l1 :
    Tendsto dyadicPrimeCriticalEnergy atTop (𝓝 0) ↔
      Tendsto dyadicPrimeCurrentL1 atTop (𝓝 0) := by
  constructor
  · exact dyadicPrimeCurrentL1_zero_of_criticalEnergy
  · intro h
    have ht := h.const_mul 4
    simp only [mul_zero] at ht
    exact squeeze_zero dyadicPrimeCriticalEnergy_nonneg dyadicPrimeCriticalEnergy_le_l1 ht

lemma dyadicPrimeCriticalEnergy_eq_tsum (N : ℕ) :
    dyadicPrimeCriticalEnergy N = ∑' p : ℕ, (p : ℝ)*(primeWindowCurrent 2 N p)^2 := by
  simpa only [dyadicPrimeCriticalEnergy,one_mul] using
    primeWindowWeightedEnergy_eq_tsum (fun _ => 1) 2 N (by omega)

/-- The dyadic critical energy condition is sufficient for the ORIGINAL
natural-density conjecture. Its arithmetic hypothesis remains unproved. -/
theorem density_of_dyadicPrimeCriticalEnergy
    (hE : Tendsto dyadicPrimeCriticalEnergy atTop (𝓝 0)) :
    {n | Nat.maxPrimeFac (n+1)>Nat.maxPrimeFac n}.HasDensity (1/2) := by
  apply density_iff_single_dyadic_harmonic_window.mpr
  apply squeeze_zero_norm (fun N => ?_) (dyadicPrimeCurrentL1_zero_of_criticalEnergy hE)
  rw [← dyadicPrimeCurrent_total]
  simpa only [dyadicPrimeCurrentL1,Real.norm_eq_abs] using
    norm_sum_le (primeWinnerLabels (2*N)) (primeWindowCurrent 2 N)

#print axioms dyadicPrimeCurrentL1_zero_of_criticalEnergy
#print axioms dyadicPrimeCriticalEnergy_zero_iff_l1
#print axioms density_of_dyadicPrimeCriticalEnergy
end Erdos371
