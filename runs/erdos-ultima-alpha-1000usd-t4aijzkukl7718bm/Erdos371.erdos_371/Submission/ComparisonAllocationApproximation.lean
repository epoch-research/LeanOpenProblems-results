import Submission.PrimeAllocationRetention
import Submission.TwoSidedFactorPacking
import Submission.QuadraticSmoothBound
import Submission.SmoothedComparison

/-! Approximation of actual comparison counts by bounded-box prime allocations
with separable weights. No cancellation for the resulting signed sum is
assumed except in the explicitly conditional final theorem. -/
namespace Erdos371
open Finset Filter RandomBins
open scoped Topology
attribute [local instance] Classical.propDecidable

noncomputable def comparisonAllocationWeight (K N : ℕ) (δ : ℝ) (n : ℕ) : ℝ :=
  primeAllocationRetention K ((primeWinner n : ℝ)*(N : ℝ)^δ) (losingNumber n) *
    primeAllocationRetention K ((primeWinner n : ℝ)*(N : ℝ)^δ)
      (winningNumber n / primeWinner n)

lemma comparisonAllocationWeight_mem_unit (K N : ℕ) (hK : 0 < K) (δ : ℝ) (n : ℕ) :
    0 ≤ comparisonAllocationWeight K N δ n ∧ comparisonAllocationWeight K N δ n ≤ 1 := by
  have hl := primeAllocationRetention_mem_unit K hK
    ((primeWinner n : ℝ)*(N : ℝ)^δ) (losingNumber n)
  have hw := primeAllocationRetention_mem_unit K hK
    ((primeWinner n : ℝ)*(N : ℝ)^δ) (winningNumber n / primeWinner n)
  unfold comparisonAllocationWeight
  constructor
  · exact mul_nonneg hl.1 hw.1
  · nlinarith

lemma comparisonAllocationWeight_loss (K N n : ℕ) (hK : 0 < K) (hN : 1 < N)
    (hn : 1 < n) (hnN : n < N) (v δ : ℝ) (hv : 0 < v) (hδ : 0 < δ)
    (hpN : (N : ℝ)^v ≤ primeWinner n)
    (hno : ¬primePowerOvershoot n) (hno' : ¬primePowerOvershoot (n+1)) :
    1 - comparisonAllocationWeight K N δ n ≤ 2/((K : ℝ)*v*δ) := by
  obtain ⟨hl,hw,hlN,hwN⟩ := comparison_numbers_bounds n hn
  obtain ⟨hp,hlp,hwp⟩ := comparison_numbers_prime_factors n hn
  have hln : ¬primePowerOvershoot (losingNumber n) := by
    unfold losingNumber
    split_ifs <;> assumption
  have hwn : ¬primePowerOvershoot (winningNumber n) := by
    unfold winningNumber
    split_ifs <;> assumption
  have hd : primeWinner n ∣ winningNumber n := by rw [← hwp]; exact Nat.maxPrimeFac_dvd
  have hq : 0 < winningNumber n / primeWinner n := Nat.div_pos
    (Nat.le_of_dvd (by omega) hd) hp.pos
  have hqN : winningNumber n / primeWinner n ≤ N :=
    (Nat.div_le_self _ _).trans (by omega)
  have hla : ∀ i : PrimeAtomIndex (losingNumber n), primePowerAtom (losingNumber n) i ≤ primeWinner n :=
    divisor_primePowerAtom_le _ _ _ (by omega) (by omega) (dvd_refl _) hln hlp.le
  have hqa : ∀ i : PrimeAtomIndex (winningNumber n / primeWinner n),
      primePowerAtom (winningNumber n / primeWinner n) i ≤ primeWinner n :=
    divisor_primePowerAtom_le _ _ _ hq (by omega) (Nat.div_dvd_of_dvd hd) hwn hwp.le
  have h₁ := primeAllocationRetention_inflated_bound K N (losingNumber n) (primeWinner n)
    hK hN (by omega) (by omega) hp.pos v δ hv hδ hpN hla
  have h₂ := primeAllocationRetention_inflated_bound K N (winningNumber n / primeWinner n) (primeWinner n)
    hK hN hq hqN hp.pos v δ hv hδ hpN hqa
  have hl' := primeAllocationRetention_mem_unit K hK
    ((primeWinner n : ℝ)*(N : ℝ)^δ) (losingNumber n)
  have hq' := primeAllocationRetention_mem_unit K hK
    ((primeWinner n : ℝ)*(N : ℝ)^δ) (winningNumber n / primeWinner n)
  have hmul := mul_nonneg (sub_nonneg.mpr hl'.2) (sub_nonneg.mpr hq'.2)
  unfold comparisonAllocationWeight
  have he : 2/((K : ℝ)*v*δ) = 1/((K : ℝ)*v*δ)+1/((K : ℝ)*v*δ) := by ring
  rw [he]
  nlinarith

lemma comparisonAllocationWeight_point_bound (K N n : ℕ) (hK : 0 < K) (hN : 1 < N)
    (hnN : n < N) (v δ : ℝ) (hv : 0 < v) (hδ : 0 < δ) :
    1 - comparisonAllocationWeight K N δ n ≤
      (if n < 2 then (1 : ℝ) else 0) +
      (if primePowerOvershoot n then 1 else 0) +
      (if primePowerOvershoot (n+1) then 1 else 0) +
      (if (primeWinner n : ℝ) ≤ (N : ℝ)^v then 1 else 0) + 2/((K : ℝ)*v*δ) := by
  classical
  have hW := comparisonAllocationWeight_mem_unit K N hK δ n
  have hC : 0 ≤ 2/((K : ℝ)*v*δ) := by positivity
  by_cases hbad : n < 2 ∨ primePowerOvershoot n ∨ primePowerOvershoot (n+1) ∨
      (primeWinner n : ℝ) ≤ (N : ℝ)^v
  · have hI : (1 : ℝ) ≤ (if n < 2 then 1 else 0) +
        (if primePowerOvershoot n then 1 else 0) +
        (if primePowerOvershoot (n+1) then 1 else 0) +
        (if (primeWinner n : ℝ) ≤ (N : ℝ)^v then 1 else 0) := by
      split_ifs <;> norm_num <;> tauto
    linarith
  · push_neg at hbad
    obtain ⟨hn,hno,hno',hlarge⟩ := hbad
    have h := comparisonAllocationWeight_loss K N n hK hN (by omega) hnN v δ hv hδ hlarge.le hno hno'
    simpa only [if_neg (by omega : ¬n < 2),if_neg hno,if_neg hno',if_neg (not_le_of_gt hlarge),
      zero_add] using h

/-- Finite mean-loss bound. Every error term remains explicit. -/
lemma comparisonAllocationWeight_mean_loss_bound (K N : ℕ) (hK : 0 < K) (hN : 1 < N)
    (v δ : ℝ) (hv : 0 < v) (hδ : 0 < δ) :
    (∑ n ∈ range N, (1-comparisonAllocationWeight K N δ n))/N ≤
      2/N + (((range N).filter primePowerOvershoot).card : ℝ)/N +
      (primePowerOvershootCount N : ℝ)/N +
      (((range N).filter fun n => (Nat.maxPrimeFac (n+1) : ℝ) ≤ (N : ℝ)^v).card : ℝ)/N +
      2/((K : ℝ)*v*δ) := by
  classical
  have hs := sum_le_sum (s := range N) (fun n hn =>
    comparisonAllocationWeight_point_bound K N n hK hN (mem_range.mp hn) v δ hv hδ)
  simp only [sum_add_distrib,sum_const,card_range,nsmul_eq_mul] at hs
  have hsmall : (∑ n ∈ range N, if n < 2 then (1 : ℝ) else 0) ≤ 2 := by
    have hc : ((range N).filter fun n => n < 2).card ≤ 2 := by
      apply (card_le_card _).trans_eq (card_range 2)
      intro n hn
      exact mem_range.mpr (mem_filter.mp hn).2
    simpa using (Nat.cast_le (α := ℝ)).mpr hc
  have hlow : (∑ n ∈ range N, if (primeWinner n : ℝ) ≤ (N : ℝ)^v then (1 : ℝ) else 0) ≤
      (((range N).filter fun n => (Nat.maxPrimeFac (n+1) : ℝ) ≤ (N : ℝ)^v).card : ℝ) := by
    have hc : ((range N).filter fun n => (primeWinner n : ℝ) ≤ (N : ℝ)^v) ⊆
        ((range N).filter fun n => (Nat.maxPrimeFac (n+1) : ℝ) ≤ (N : ℝ)^v) := by
      intro n hn
      obtain ⟨hn,hp⟩ := mem_filter.mp hn
      have hle : Nat.maxPrimeFac (n+1) ≤ primeWinner n := le_max_right _ _
      exact mem_filter.mpr ⟨hn,(show (Nat.maxPrimeFac (n+1) : ℝ) ≤ primeWinner n by exact_mod_cast hle).trans hp⟩
    simpa using (Nat.cast_le (α := ℝ)).mpr (card_le_card hc)
  have he₁ : (∑ n ∈ range N, if primePowerOvershoot n then (1 : ℝ) else 0) =
      (((range N).filter primePowerOvershoot).card : ℝ) := by simp
  have he₂ : (∑ n ∈ range N, if primePowerOvershoot (n+1) then (1 : ℝ) else 0) =
      primePowerOvershootCount N := by simp [primePowerOvershootCount]
  rw [he₁,he₂] at hs
  have hb : (∑ n ∈ range N, (1-comparisonAllocationWeight K N δ n)) ≤
      2 + (((range N).filter primePowerOvershoot).card : ℝ) + primePowerOvershootCount N +
      (((range N).filter fun n => (Nat.maxPrimeFac (n+1) : ℝ) ≤ (N : ℝ)^v).card : ℝ) +
      (N : ℝ)*(2/((K : ℝ)*v*δ)) := by linarith
  have hd := div_le_div_of_nonneg_right hb (Nat.cast_nonneg (α := ℝ) N)
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  convert hd using 1
  field_simp

/-- For any fixed positive inflation, a fixed number of boxes gives arbitrarily
small mean loss as N grows. This is approximation, not signed cancellation. -/
theorem comparisonAllocationWeight_uniform_approximation (δ : ℝ) (hδ : 0 < δ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℕ, 0 < K ∧ ∀ᶠ N : ℕ in atTop,
      (∑ n ∈ range N, (1-comparisonAllocationWeight K N δ n))/N < ε := by
  classical
  let v : ℝ := min 1 (ε/640)
  have hv : 0 < v := lt_min (by norm_num) (by positivity)
  have hv1 : v ≤ 1 := min_le_left _ _
  have hve : v ≤ ε/640 := min_le_right _ _
  have hvsmall : 80*v^2 ≤ ε/8 := by
    have hh := (le_div_iff₀ (by norm_num : (0 : ℝ) < 640)).mp hve
    nlinarith
  obtain ⟨K,hK⟩ := exists_nat_gt (max (1 : ℝ) (8/(ε*(v*δ))))
  have hKpos : 0 < K := by exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
    ((le_max_left _ _).trans hK.le))
  have hKr : (0 : ℝ) < K := by exact_mod_cast hKpos
  have hlarge : 8 < (K : ℝ)*(ε*(v*δ)) :=
    (div_lt_iff₀ (by positivity)).mp ((le_max_right _ _).trans_lt hK)
  have hC : 2/((K : ℝ)*v*δ) < ε/4 := by
    apply (div_lt_iff₀ (by positivity)).mpr
    nlinarith
  have ht := ((tendsto_const_div_atTop_nhds_zero_nat (2 : ℝ)).add
    ((density_iff_count primePowerOvershoot 0).mp primePowerOvershoot_hasDensity_zero)).add
      primePowerOvershootCount_tendsto_zero
  simp only [add_zero] at ht
  have hs := FiniteSieve.smooth_power_count_eventually_le v hv.le (ε/8) (by positivity)
  refine ⟨K,hKpos,?_⟩
  filter_upwards [ht.eventually_lt_const (show (0 : ℝ) < ε/4 by positivity),hs,
    eventually_gt_atTop (1 : ℕ)] with N ht hs hN
  have hb := comparisonAllocationWeight_mean_loss_bound K N hKpos hN v δ hv hδ
  linarith

lemma comparisonAllocationWeight_signed_error_bound (K N : ℕ) (hK : 0 < K) (δ : ℝ) :
    |(∑ n ∈ range N, factorSign n)/N -
      (∑ n ∈ range N, factorSign n*comparisonAllocationWeight K N δ n)/N| ≤
        (∑ n ∈ range N, (1-comparisonAllocationWeight K N δ n))/N := by
  rw [← sub_div,← sum_sub_distrib,abs_div,abs_of_nonneg (Nat.cast_nonneg (α := ℝ) N)]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg (α := ℝ) N)
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro n hn
  have hW := (comparisonAllocationWeight_mem_unit K N hK δ n).2
  have hsign : |factorSign n| = 1 := by simpa only [Real.norm_eq_abs] using factorSign_norm n
  rw [show factorSign n-factorSign n*comparisonAllocationWeight K N δ n =
      factorSign n*(1-comparisonAllocationWeight K N δ n) by ring,
    abs_mul,hsign,one_mul,abs_of_nonneg (sub_nonneg.mpr hW)]

/-- A new sufficient signed criterion with separable allocation weights.
The convergence hypothesis is the unproved arithmetic estimate. -/
theorem density_of_comparisonAllocation_cancellation (δ : ℝ) (hδ : 0 < δ)
    (hcancel : ∀ K : ℕ, 0 < K → Tendsto (fun N : ℕ =>
      (∑ n ∈ range N, factorSign n*comparisonAllocationWeight K N δ n)/N) atTop (nhds 0)) :
    {n | Nat.maxPrimeFac (n+1) > Nat.maxPrimeFac n}.HasDensity (1/2) := by
  rw [density_iff_signed_count]
  simp_rw [← factorSign_sum_eq_count_difference]
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨K,hK,ha⟩ := comparisonAllocationWeight_uniform_approximation δ hδ (ε/2) (by positivity)
  have hc := Metric.tendsto_nhds.mp (hcancel K hK) (ε/2) (by positivity)
  filter_upwards [ha,hc] with N ha hc
  rw [Real.dist_eq,sub_zero] at hc ⊢
  have hb := comparisonAllocationWeight_signed_error_bound K N hK δ
  have ht := abs_sub_le ((∑ n ∈ range N, factorSign n)/N)
    ((∑ n ∈ range N, factorSign n*comparisonAllocationWeight K N δ n)/N) 0
  simp only [sub_zero] at ht
  linarith

#print axioms comparisonAllocationWeight_loss
#print axioms comparisonAllocationWeight_uniform_approximation
#print axioms density_of_comparisonAllocation_cancellation
end Erdos371
