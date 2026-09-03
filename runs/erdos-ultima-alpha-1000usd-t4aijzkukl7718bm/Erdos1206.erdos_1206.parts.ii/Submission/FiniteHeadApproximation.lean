import Submission.FinitePrimePeriodVariance

/-! Full centered prime scores are uniformly approximated in mean square by
finite-head periodic scores, apart from a finite initial interval. -/
namespace Erdos1206.FiniteHeadApproximation
open Finset PrimeBlockVariance SharpPrimeBlockVariance FullPrimeScoreVariance
  PowerWindowMeanOscillation QuadraticPrimeMoments ConicContrastMoments
  PrimeBlockMeanOscillation FinitePrimePeriodVariance
open scoped Classical

noncomputable def primes (H : ℕ) := Nat.primesBelow (H+1)
noncomputable def period (H : ℕ) := ∏p∈primes H,p
noncomputable def score (w : ℕ → ℝ) (H n : ℕ) := primeSum (primes H) w n-mean (primes H) w

lemma prime_mem {H p : ℕ} (hp : p ∈ primes H) : p.Prime := (Nat.mem_primesBelow.mp hp).2
lemma period_pos (H : ℕ) : 0 < period H := prod_pos (fun _ hp => (prime_mem hp).pos)
lemma dvd_period {H p : ℕ} (hp : p ∈ primes H) : p ∣ period H := dvd_prod_of_mem id hp

lemma head_primeScore (w : ℕ → ℝ) (H : ℕ) {n : ℕ} (hn : 0 < n) :
    primeScore (headWeight w H) n=primeSum (primes H) w n := by
  have he : n.primeFactors.filter (fun p => p ≤ H)=(primes H).filter (fun p => p ∣ n) := by
    ext p
    simp only [mem_filter,Nat.mem_primeFactors,primes,Nat.mem_primesBelow]
    constructor
    · rintro ⟨⟨hp,hpn,_⟩,hpH⟩
      exact ⟨⟨by omega,hp⟩,hpn⟩
    · rintro ⟨⟨hpH,hp⟩,hpn⟩
      exact ⟨⟨hp,hpn,hn.ne'⟩,by omega⟩
  simp only [primeScore,headWeight,primeSum,indicator,mul_ite,mul_one,mul_zero,←sum_filter,he]

lemma head_center (w : ℕ → ℝ) {H n : ℕ} (hH : H ≤ cutoff n) :
    center (headWeight w H) n=mean (primes H) w := by
  have he : (Nat.primesBelow (cutoff n+1)).filter (fun p => p ≤ H)=primes H := by
    ext p
    by_cases hp : p.Prime <;> simp [primes,Nat.mem_primesBelow,hp]
    omega
  simp only [center,prefixMean,headWeight,ite_div,zero_div,←sum_filter,he,mean]

lemma head_stable (w : ℕ → ℝ) {H n : ℕ} (hn : 0 < n) (hH : H^2 ≤ n) :
    deviation (headWeight w H) n=score w H n := by
  have hcut : H ≤ cutoff n := by
    apply (Nat.pow_le_pow_iff_left (by decide : 2 ≠ 0)).mp
    exact hH.trans (cutoff_lower n).le
  rw [deviation,head_primeScore w H hn,head_center w hcut]
  rfl

lemma score_mod (w : ℕ → ℝ) (H n : ℕ) : score w H (n%period H)=score w H n := by
  simp only [score,primeSum_mod (primes H) w (period H) n (fun _ hp => dvd_period hp)]

lemma score_zero_eq (w : ℕ → ℝ) (H : ℕ) : score w H 0=score w H (period H) := by
  simpa using score_mod w H (period H)

lemma range_variance (w : ℕ → ℝ) (H : ℕ) :
    (∑n∈range (period H),score w H n^2)=variance (period H) (primes H) w := by
  have he : Icc 1 (period H)=Ico 1 (period H+1) := by ext n; simp
  rw [variance,he,sum_Ico_eq_sub _ (by omega),sum_range_succ,sum_range_one]
  change _=(∑n∈range (period H),score w H n^2)+score w H (period H)^2-score w H 0^2
  rw [score_zero_eq]
  ring

lemma range_moment_le (w : ℕ → ℝ)
    (hs : Summable (fun p : ℕ => if p.Prime then w p^2/p else 0)) (H : ℕ) :
    (∑n∈range (period H),score w H n^2) ≤ energy w*(period H:ℝ) := by
  rw [range_variance]
  have hh := variance_le_period (period H) (primes H) w (fun _ hp => prime_mem hp) (fun _ hp => dvd_period hp)
  have hmass := finite_mass_le w hs (primes H) (fun _ hp => prime_mem hp)
  have hm := mul_le_mul_of_nonneg_left hmass (Nat.cast_nonneg (period H))
  nlinarith

lemma difference_eq_tail (w : ℕ → ℝ) {H n : ℕ} (hn : 0 < n) (hH : H^2 ≤ n) :
    deviation w n-score w H n=deviation (tailWeight w H) n := by
  rw [FullPrimeScoreVariance.split w H n,head_stable w hn hH]
  ring

#print axioms range_moment_le
#print axioms difference_eq_tail
end Erdos1206.FiniteHeadApproximation
