import Submission.RoughMobiusHarmonic

/-! With a fixed power-sized roughness cutoff, every rough modulus up to
N has bounded factor length. Its entire small-modulus contribution is o(N).
This does not estimate the complementary large-divisor tail. -/
namespace Erdos371
open Finset Filter
open scoped Topology Pointwise

private lemma list_prime_divisors_card_le (l : List ℕ) (hl : ∀ p ∈ l, p.Prime) :
    l.prod.divisors.card ≤ 2^l.length := by
  induction l with
  | nil => simp
  | cons p l ih =>
    have hp := hl p (by simp)
    have h := ih (fun q hq => hl q (by simp [hq]))
    rw [List.prod_cons,Nat.divisors_mul]
    apply card_mul_le.trans
    rw [hp.divisors]
    have hpcard : ({1,p} : Finset ℕ).card=2 := by simp [hp.ne_one.symm]
    rw [hpcard,List.length_cons,pow_succ]
    nlinarith

lemma divisors_card_le_two_pow_factor_length (n : ℕ) (hn : n≠0) :
    n.divisors.card ≤ 2^n.primeFactorsList.length := by
  have h := list_prime_divisors_card_le n.primeFactorsList (fun p hp => Nat.prime_of_mem_primeFactorsList hp)
  rwa [Nat.prod_primeFactorsList hn] at h

private lemma list_pow_length_le_prod (B : ℕ) (l : List ℕ) (hl : ∀ p ∈ l, B≤p) :
    B^l.length ≤ l.prod := by
  induction l with
  | nil => simp
  | cons p l ih =>
    have hp := hl p (by simp)
    have h := ih (fun q hq => hl q (by simp [hq]))
    rw [List.length_cons,pow_succ',List.prod_cons]
    exact Nat.mul_le_mul hp h

lemma rough_factor_length_le (B K n : ℕ) (hB : 1 ≤ B) (hn : 0 < n)
    (hrough : B<n.minFac) (hsize : n≤(B+1)^K) :
    n.primeFactorsList.length ≤ K := by
  have hprod : (B+1)^n.primeFactorsList.length ≤ n := by
    have h := list_pow_length_le_prod (B+1) n.primeFactorsList (fun p hp => by
      have hpp := Nat.prime_of_mem_primeFactorsList hp
      have hd := (Nat.mem_primeFactorsList hn.ne').mp hp
      have hmin := Nat.minFac_le_of_dvd hpp.two_le hd.2
      omega)
    rwa [Nat.prod_primeFactorsList hn.ne'] at h
  exact (Nat.pow_le_pow_iff_right (by omega : 1<B+1)).mp (hprod.trans hsize)

lemma rough_divisors_card_le (B K n : ℕ) (hB : 1 ≤ B) (hn : 0 < n)
    (hrough : B<n.minFac) (hsize : n≤(B+1)^K) :
    n.divisors.card ≤ 2^K :=
  (divisors_card_le_two_pow_factor_length n hn.ne').trans
    (Nat.pow_le_pow_right (by norm_num) (rough_factor_length_le B K n hB hn hrough hsize))

/-- The error is paid only for rough moduli, with a bounded number of roots
per modulus. Both the modulus cutoff D and the sampling endpoint N are explicit. -/
theorem roughSmallDivisorSum_bounded_factor_length (B K D N : ℕ) (hB : 1 ≤ B)
    (hsize : D≤(B+1)^K) :
    ‖∑ n ∈ range N, roughSmallDivisorSum B D (n+1)‖ ≤
      ((2 : ℝ)^K+1)*roughNumberCount B (D+1) := by
  unfold roughSmallDivisorSum
  rw [sum_comm]
  calc
    _ ≤ ∑ d ∈ (range (D+1)).filter (fun d => B<d.minFac),
        ‖∑ n ∈ range N, orientedDivisorTerm d (n+1)‖ := norm_sum_le _ _
    _ ≤ ∑ d ∈ (range (D+1)).filter (fun d => B<d.minFac),
        if 1<d then (2 : ℝ)^K+1 else 0 := by
      apply sum_le_sum
      intro d hd
      obtain ⟨hdD,hdB⟩ := mem_filter.mp hd
      have hdD' : d≤D := by have := mem_range.mp hdD; omega
      by_cases hd : 1<d
      · rw [if_pos hd]
        apply (orientedDivisorTerm_sparse_shifted_bound d N).trans
        have hc := rough_divisors_card_le B K d hB (by omega) hdB (hdD'.trans hsize)
        have hc' : (d.divisors.card : ℝ)≤(2 : ℝ)^K := by exact_mod_cast hc
        linarith
      · simp only [if_neg hd]
        have hz (n : ℕ) := orientedDivisorTerm_eq_zero_of_le_one d (n+1) (by omega)
        simp only [hz,sum_const_zero,norm_zero,le_refl]
    _ = _ := by
      rw [← sum_filter,sum_const,nsmul_eq_mul]
      have he : ((range (D+1)).filter (fun d => B<d.minFac)).filter (fun d => 1<d) =
          (range (D+1)).filter (fun d => 1<d ∧ B<d.minFac) := by ext d; simp; tauto
      rw [he]
      unfold roughNumberCount
      ring

/-- For any fixed factor-length bound, all rough moduli up to the FULL
sampling length N have negligible total discrepancy. -/
theorem roughSmallDivisorSum_full_linear_tendsto (B : ℕ → ℕ) (K : ℕ)
    (hB : Tendsto B atTop atTop) (hsize : ∀ᶠ N in atTop, N≤(B N+1)^K) :
    Tendsto (fun N : ℕ => (∑ n ∈ range N, roughSmallDivisorSum (B N) N (n+1))/N)
      atTop (𝓝 0) := by
  have ht := (growing_roughNumberCount_succ_tendsto B hB).const_mul ((2 : ℝ)^K+1)
  simp only [mul_zero] at ht
  apply squeeze_zero_norm' _ ht
  filter_upwards [hsize,hB.eventually (eventually_ge_atTop 1)] with N hs hB'
  rw [norm_div,Real.norm_natCast]
  have h := div_le_div_of_nonneg_right
    (roughSmallDivisorSum_bounded_factor_length (B N) K N N hB' hs) (Nat.cast_nonneg (α := ℝ) N)
  exact h.trans_eq (by ring)

#print axioms rough_factor_length_le
#print axioms roughSmallDivisorSum_bounded_factor_length
#print axioms roughSmallDivisorSum_full_linear_tendsto
end Erdos371
