import Submission.DyadicSeriesTools
import Submission.RawHarmonicTauberian

/-! Convergence of the unnormalized harmonic signed contribution from moving
near-linear winning primes. The interior contribution is not estimated. -/
namespace Erdos371
open Finset Filter FiniteInformation
open scoped Topology
set_option autoImplicit false

noncomputable def dyadicPrimeThreshold (u : ℕ → ℝ) (n : ℕ) : ℝ :=
  ((2 : ℝ)^(Nat.log 2 n+1))^(1-u (Nat.log 2 n))

noncomputable def dyadicHighWinnerSign (u : ℕ → ℝ) (n : ℕ) : ℝ :=
  if dyadicPrimeThreshold u n<(primeWinner n : ℝ) then factorSign n else 0

lemma primeWinnerLoser_weight_flux (g : ℕ → ℝ) (n : ℕ) :
    g (primeWinner n)*factorSign n-g (primeLoser n)*factorSign n =
      g (Nat.maxPrimeFac (n+1))-g (Nat.maxPrimeFac n) := by
  unfold primeWinner primeLoser factorSign predicateSign
  by_cases h : Nat.maxPrimeFac n<Nat.maxPrimeFac (n+1)
  · simp [h,max_eq_right h.le,min_eq_left h.le]
  · simp [h,max_eq_left (not_lt.mp h),min_eq_right (not_lt.mp h)]
    ring

lemma dyadicHighWinner_harmonic_prefix_bound (u : ℕ → ℝ) (k M : ℕ)
    (hlo : 2^k≤M) (hhi : M≤2^(k+1)) :
    |∑ n ∈ Ico (2^k) M, dyadicHighWinnerSign u n/(n : ℝ)|≤
      (∑ n ∈ Ico (2^k) (2^(k+1)), dyadicTopPrimeReciprocal u n)+1/(2 : ℝ)^k := by
  classical
  let c : ℝ := ((2 : ℝ)^(k+1))^(1-u k)
  let g (p : ℕ) : ℝ := if c<(p : ℝ) then 1 else 0
  let a (n : ℕ) := g (Nat.maxPrimeFac n)
  let L (n : ℕ) := g (primeLoser n)*factorSign n/(n : ℝ)
  have ha (n : ℕ) : 0≤a n ∧ a n≤1 := by unfold a g; split_ifs <;> norm_num
  have hlog (n : ℕ) (hn : n ∈ Ico (2^k) (2^(k+1))) : Nat.log 2 n=k :=
    Nat.log_eq_of_pow_le_of_lt_pow (mem_Ico.mp hn).1 (mem_Ico.mp hn).2
  have hsub : Ico (2^k) M ⊆ Ico (2^k) (2^(k+1)) := Ico_subset_Ico le_rfl hhi
  have he (n : ℕ) (hn : n ∈ Ico (2^k) M) :
      dyadicHighWinnerSign u n/(n : ℝ)=(a (n+1)-a n)/(n : ℝ)+L n := by
    have hf := primeWinnerLoser_weight_flux g n
    have hw : dyadicHighWinnerSign u n=g (primeWinner n)*factorSign n := by
      unfold dyadicHighWinnerSign dyadicPrimeThreshold g
      rw [hlog n (hsub hn)]
      dsimp [c]
      split_ifs <;> simp
    rw [hw]
    dsimp [L,a]
    rw [← hf]
    ring
  have hL (n : ℕ) (hn : n ∈ Ico (2^k) (2^(k+1))) : |L n|=dyadicTopPrimeReciprocal u n := by
    have hh : c<(primeLoser n : ℝ) ↔ dyadicTopPrimePair u n := by
      simp only [primeLoser,Nat.cast_min,lt_min_iff,dyadicTopPrimePair,hlog n hn,c]
    have hF : |factorSign n|=1 := by simpa only [Real.norm_eq_abs] using factorSign_norm n
    unfold L g dyadicTopPrimeReciprocal
    by_cases hc : c<(primeLoser n : ℝ)
    · rw [if_pos hc,if_pos (hh.mp hc),one_mul,abs_div,hF,abs_of_nonneg (Nat.cast_nonneg n)]
    · rw [if_neg hc,if_neg (not_iff_not.mpr hh |>.mp hc),zero_mul,zero_div,abs_zero]
  have hsum : (∑ n ∈ Ico (2^k) M, dyadicHighWinnerSign u n/(n : ℝ)) =
      (∑ n ∈ Ico (2^k) M, (a (n+1)-a n)/(n : ℝ))+
        ∑ n ∈ Ico (2^k) M, L n := by
    rw [← sum_add_distrib]
    exact sum_congr rfl he
  have hd := reciprocal_derivative_Ico_bound a ha (2^k) M (pow_pos (by norm_num) _) hlo
  have hl : |∑ n ∈ Ico (2^k) M, L n|≤∑ n ∈ Ico (2^k) (2^(k+1)), dyadicTopPrimeReciprocal u n := by
    calc
      _ ≤ ∑ n ∈ Ico (2^k) M, |L n| := abs_sum_le_sum_abs _ _
      _ = ∑ n ∈ Ico (2^k) M, dyadicTopPrimeReciprocal u n := sum_congr rfl (fun n hn => hL n (hsub hn))
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => dyadicTopPrimeReciprocal_nonneg u n)
  rw [hsum]
  push_cast at hd
  exact (abs_add_le _ _).trans (by linarith)

/-- Moving top-band cancellation in the UNNORMALIZED, ordinarily ordered
harmonic series. Unlike the fixed-prime limits, this is uniform over all
winning primes in the boundary band. -/
theorem dyadicHighWinner_rawHarmonic_converges (u : ℕ → ℝ)
    (hu0 : ∀ k, 0≤u k) (hu : ∀ k, u k≤1/8)
    (hs : Summable (fun k => (u k)^2)) :
    ∃ L : ℝ, Tendsto (rawHarmonicSum (dyadicHighWinnerSign u)) atTop (𝓝 L) := by
  have hb := summable_dyadic_blocks_of_nonneg (dyadicTopPrimeReciprocal u)
    (dyadicTopPrimeReciprocal_nonneg u) (summable_dyadicTopPrimeReciprocal u hu0 hu hs)
  have he : Summable (fun k : ℕ => (1 : ℝ)/(2 : ℝ)^k) := by
    simpa only [one_div,inv_pow] using summable_geometric_of_lt_one
      (by norm_num : (0 : ℝ)≤(2 : ℝ)⁻¹) (by norm_num : (2 : ℝ)⁻¹<1)
  exact partialSums_converge_of_dyadic_prefix_bound
    (fun n => dyadicHighWinnerSign u n/(n : ℝ)) _ (hb.add he)
      (dyadicHighWinner_harmonic_prefix_bound u)

theorem threeQuarterHighWinner_rawHarmonic_converges :
    ∃ L : ℝ, Tendsto (rawHarmonicSum (dyadicHighWinnerSign threeQuarterBandWidth)) atTop (𝓝 L) :=
  dyadicHighWinner_rawHarmonic_converges threeQuarterBandWidth
    threeQuarterBandWidth_nonneg threeQuarterBandWidth_le summable_threeQuarterBandWidth_sq

theorem threeQuarterHighWinner_natural_mean_zero :
    Tendsto (fun N => prefixMean N (dyadicHighWinnerSign threeQuarterBandWidth)) atTop (𝓝 0) := by
  obtain ⟨L,hL⟩ := threeQuarterHighWinner_rawHarmonic_converges
  exact prefixMean_zero_of_rawHarmonicSum_tendsto _ L hL

#print axioms dyadicHighWinner_rawHarmonic_converges
#print axioms threeQuarterHighWinner_rawHarmonic_converges
#print axioms threeQuarterHighWinner_natural_mean_zero
end Erdos371
