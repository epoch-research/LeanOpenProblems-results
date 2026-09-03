import Submission.PolylogMultiplicitySpectrum

/-!
# The interval of polylogarithmic input exponents supplied by the sieve

For each 1<kappa<=2000001/963433 the restricted multiplicity has critical
exponent 1-1/kappa. The interval is bounded; this is not the unbounded-kappa
statement that would imply the original conjecture.
-/

open Nat Filter
open scoped Classical BigOperators
namespace Erdos821
open AnalyticSieve HigherDivisors
set_option maxHeartbeats 3000000

lemma exists_polylog_density_parameters (t b : ℕ) (ht : 0<t)
    (κ γ : ℝ) (hκ : 1<κ) (hcut : (b : ℝ)*κ ≤ t)
    (hγ : γ<1-1/κ) :
    ∃ k c : ℕ, 1≤k ∧ b*k+1≤c ∧ c+4≤t*k ∧
      γ < ((t*k-1-c-2 : ℕ) : ℝ)/(t*k : ℕ) ∧
      ((t*k : ℕ) : ℝ)/((c : ℝ)+1) ≤ κ := by
  have htR : (0 : ℝ)<t := by exact_mod_cast ht
  have hκ0 : 0<κ := by linarith
  have hinv : 1/κ<1 := (div_lt_one hκ0).mpr hκ
  have hδ0 : 0<(t : ℝ)*(1-1/κ) := mul_pos htR (by linarith)
  have hδγ : 0<(t : ℝ)*(1-1/κ-γ) := mul_pos htR (by linarith)
  obtain ⟨k,hk⟩ := exists_nat_gt
    (max 1 (max (6/((t : ℝ)*(1-1/κ))) (6/((t : ℝ)*(1-1/κ-γ)))))
  have hk1R : (1 : ℝ)<k := (le_max_left _ _).trans_lt hk
  have hk1 : 1≤k := by exact_mod_cast hk1R.le
  have hk0 : (0 : ℝ)<k := by linarith
  have h6₀ : 6 < (k : ℝ)*((t : ℝ)*(1-1/κ)) :=
    (div_lt_iff₀ hδ0).mp ((le_max_left _ _).trans_lt ((le_max_right _ _).trans_lt hk))
  have h6γ : 6 < (k : ℝ)*((t : ℝ)*(1-1/κ-γ)) :=
    (div_lt_iff₀ hδγ).mp ((le_max_right _ _).trans_lt ((le_max_right _ _).trans_lt hk))
  let z : ℝ := (t : ℝ)*k/κ
  let c : ℕ := ⌊z⌋₊+1
  have hz : 0≤z := by dsimp [z]; positivity
  have hcle : (c : ℝ) ≤ z+1 := by
    dsimp [c]
    push_cast
    linarith [Nat.floor_le hz]
  have hclt : z<(c : ℝ) := by
    simpa only [c,Nat.cast_add,Nat.cast_one] using Nat.lt_floor_add_one z
  have hzc : z*κ=(t : ℝ)*k := by dsimp [z]; exact div_mul_cancel₀ _ hκ0.ne'
  have hcutk := mul_le_mul_of_nonneg_right hcut hk0.le
  have hbk : ((b*k : ℕ) : ℝ) ≤ z := by
    rw [Nat.cast_mul]
    apply (le_div_iff₀ hκ0).mpr
    nlinarith only [hcutk]
  have hbkc : b*k+1≤c := Nat.succ_le_succ (Nat.le_floor hbk)
  have he₀ : (k : ℝ)*((t : ℝ)*(1-1/κ)) = (t : ℝ)*k-z := by
    dsimp [z]
    ring
  have heγ : (k : ℝ)*((t : ℝ)*(1-1/κ-γ)) = (t : ℝ)*k-z-(t : ℝ)*k*γ := by
    dsimp [z]
    ring
  rw [he₀] at h6₀
  rw [heγ] at h6γ
  have hgapR : (c : ℝ)+4≤(t : ℝ)*k := by linarith
  have hgap : c+4≤t*k := by exact_mod_cast hgapR
  have hnum : ((t*k-1-c-2 : ℕ) : ℝ) = (t : ℝ)*k-c-3 := by
    rw [Nat.cast_sub (by omega : 2≤t*k-1-c),Nat.cast_sub (by omega : c≤t*k-1),
      Nat.cast_sub (by omega : 1≤t*k)]
    push_cast
    ring
  have htk : (0 : ℝ)<(t*k : ℕ) := by exact_mod_cast Nat.mul_pos ht hk1
  refine ⟨k,c,hk1,hbkc,hgap,?_,?_⟩
  · apply (lt_div_iff₀ htk).mpr
    rw [hnum,Nat.cast_mul]
    linarith
  · apply (div_le_iff₀ (by positivity : 0<(c : ℝ)+1)).mpr
    rw [Nat.cast_mul]
    have h := mul_lt_mul_of_pos_right hclt hκ0
    rw [hzc] at h
    nlinarith only [h,hκ0]

lemma infinite_gPolylog_gt_of_polynomial_count (t b K C d : ℕ)
    (ht : 0<t)
    (H : ∀ᶠ m : ℕ in atTop, ∃ P : Finset ℕ,
      (∀ p ∈ P, p.Prime ∧ p ≤ 2^(t*m) ∧
        p-1 ∈ Nat.smoothNumbers (K*2^(b*m))) ∧
      2^(t*m) ≤ C*(m+1)^d*P.card)
    (κ γ : ℝ) (hκ : 1<κ) (hcut : (b : ℝ)*κ ≤ t)
    (hγ : γ<1-1/κ) :
    {n : ℕ | (gPolylog κ n : ℝ) > (n : ℝ)^γ}.Infinite := by
  obtain ⟨k,c,hk,hbc,hct,hγk,hκk⟩ := exists_polylog_density_parameters t b ht κ γ hκ hcut hγ
  have HD : ∀ M : ℕ, ∃ L : ℕ, M≤L ∧ ∃ P : Finset ℕ,
      (∀ p ∈ P, p.Prime ∧ p≤2^((t*k)*L) ∧
        p-1 ∈ Nat.smoothNumbers (2^(c*L))) ∧ 2^((t*k-1)*L)≤P.card := by
    intro M
    obtain ⟨L,hL,P,hP,hcard⟩ := dyadic_family_of_eventual_polynomial_count t b K C d k ht hk H M
    refine ⟨L,hL,P,?_,hcard⟩
    intro p hp
    refine ⟨(hP p hp).1,(hP p hp).2.1,?_⟩
    exact Nat.smoothNumbers_mono
      (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right L hbc)) (hP p hp).2.2
  apply Set.infinite_of_forall_exists_gt
  intro N
  obtain ⟨n,F,hn,hcard,hF⟩ := polylog_input_fibers_of_general_density (t*k) (t*k-1) c
    hct (by omega) (by omega) HD (max N 1)
  have hn1 : 1<n := (le_max_right _ _).trans_lt hn
  have hnR : (1 : ℝ)≤n := by exact_mod_cast hn1.le
  have hbase : 1≤4*Real.log (n : ℝ) := by
    have hlog := Real.log_le_log (by norm_num : (0 : ℝ)<2)
      (show (2 : ℝ)≤n by exact_mod_cast hn1)
    linarith [Real.log_two_gt_d9]
  have hFκ : ∀ m ∈ F, totient m=n ∧ ∀ p ∈ m.primeFactors,
      (p : ℝ) ≤ (4*Real.log (n : ℝ))^κ := by
    intro m hm
    refine ⟨(hF m hm).2.1,?_⟩
    intro p hp
    exact ((hF m hm).2.2 p hp).trans (Real.rpow_le_rpow_of_exponent_le hbase hκk)
  refine ⟨n,?_,(le_max_left _ _).trans_lt hn⟩
  exact ((Real.rpow_le_rpow_of_exponent_le hnR hγk.le).trans_lt hcard).trans_le
    (by exact_mod_cast finite_fiber_card_le_gPolylog κ n F hFκ)

lemma finite_gPolylog_exceedance (κ γ : ℝ) (hκ : 1<κ) (hγ : 1-1/κ<γ) :
    {n : ℕ | (gPolylog κ n : ℝ) > (n : ℝ)^γ}.Finite := by
  obtain ⟨N,hN⟩ := eventually_atTop.mp (eventually_gPolylog_le κ γ hκ hγ)
  apply (Set.finite_Iio N).subset
  intro n hn
  by_contra h
  exact hn.not_ge (hN n (le_of_not_gt h))

/-- A generic sharp restricted exponent from any polynomial-loss
smooth-predecessor prime count. -/
theorem polylog_critical_exponent_of_polynomial_count (t b K C d : ℕ)
    (ht : 0<t)
    (H : ∀ᶠ m : ℕ in atTop, ∃ P : Finset ℕ,
      (∀ p ∈ P, p.Prime ∧ p ≤ 2^(t*m) ∧
        p-1 ∈ Nat.smoothNumbers (K*2^(b*m))) ∧
      2^(t*m) ≤ C*(m+1)^d*P.card)
    (κ : ℝ) (hκ : 1<κ) (hcut : (b : ℝ)*κ ≤ t) :
    sSup {γ : ℝ | {n : ℕ | (gPolylog κ n : ℝ) > (n : ℝ)^γ}.Infinite} = 1-1/κ := by
  have hκ0 : 0<κ := by linarith
  have hα0 : 0<1-1/κ := by
    have h := (div_lt_one hκ0).mpr hκ
    linarith
  apply csSup_eq_of_forall_le_of_forall_lt_exists_gt
    ⟨0,infinite_gPolylog_gt_of_polynomial_count t b K C d ht H κ 0 hκ hcut hα0⟩
  · intro γ hγ
    by_contra h
    exact (finite_gPolylog_exceedance κ γ hκ (lt_of_not_ge h)).not_infinite hγ
  · intro γ hγ
    obtain ⟨δ,hγδ,hδ⟩ := exists_between hγ
    exact ⟨δ,infinite_gPolylog_gt_of_polynomial_count t b K C d ht H κ δ hκ hcut hδ,hγδ⟩

lemma wide_block_eventual_polynomial_count :
    ∃ C : ℕ, ∀ᶠ m : ℕ in atTop, ∃ P : Finset ℕ,
      (∀ p ∈ P, p.Prime ∧ p ≤ 2^((64*40000020)*m) ∧
        p-1 ∈ Nat.smoothNumbers (1*2^((64*19268660)*m))) ∧
      2^((64*40000020)*m) ≤ C*(m+1)^1*P.card := by
  obtain ⟨C,_hC,H⟩ := exists_wide_block_smooth_prime_count
  refine ⟨C,?_⟩
  filter_upwards [H] with m hm
  refine ⟨smoothPrimePool (independentN 40000020 m) (independentN 19268660 m),?_,?_⟩
  · intro p hp
    obtain ⟨hp,hs⟩ := Finset.mem_filter.mp hp
    obtain ⟨hN,hpr⟩ := Nat.mem_primesBelow.mp hp
    refine ⟨hpr,?_,?_⟩
    · change p ≤ independentN 40000020 m
      omega
    · simpa only [one_mul] using hs
  · have hh : independentN 40000020 m ≤
        C*m*(smoothPrimePool (independentN 40000020 m) (independentN 19268660 m)).card := by
      exact_mod_cast hm
    exact hh.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left C (by simp)))

/-- The whole proved interval is bounded above; increasing kappa beyond
this interval is not licensed by the theorem. -/
theorem polylog_critical_exponent_wide_interval (κ : ℝ) (hκ : 1<κ)
    (hκb : κ≤2000001/963433) :
    sSup {γ : ℝ | {n : ℕ | (gPolylog κ n : ℝ) > (n : ℝ)^γ}.Infinite} = 1-1/κ := by
  obtain ⟨C,H⟩ := wide_block_eventual_polynomial_count
  apply polylog_critical_exponent_of_polynomial_count (64*40000020) (64*19268660)
    1 C 1 (by omega) H κ hκ
  norm_num
  nlinarith only [hκb]

/-- Below the critical exponent, infinitude holds throughout the proved
interval of logarithmic input-prime bounds. -/
theorem infinite_gPolylog_gt_wide_interval (κ γ : ℝ) (hκ : 1<κ)
    (hκb : κ≤2000001/963433) (hγ : γ<1-1/κ) :
    {n : ℕ | (gPolylog κ n : ℝ) > (n : ℝ)^γ}.Infinite := by
  obtain ⟨C,H⟩ := wide_block_eventual_polynomial_count
  apply infinite_gPolylog_gt_of_polynomial_count (64*40000020) (64*19268660)
    1 C 1 (by omega) H κ γ hκ ?_ hγ
  norm_num
  nlinarith only [hκb]

end Erdos821
