import Submission.PowerWindowMeanOscillation
import Submission.ConicContrastMoments

/-! The finite-prime uniform variance estimate extends to the full strongly
additive score. This is an analytic lemma, not a separating-score construction. -/
namespace Erdos1206.FullPrimeScoreVariance
open Finset Filter PrimeBlockVariance SharpPrimeBlockVariance
  QuadraticPrimeMoments PowerWindowMeanOscillation ConicContrastMoments
  PrimeBlockMeanOscillation
open scoped Classical Topology

noncomputable def deviation (w : ℕ → ℝ) (n : ℕ) : ℝ := primeScore w n-center w n
noncomputable def headWeight (w : ℕ → ℝ) (H : ℕ) (p : ℕ) : ℝ := if p ≤ H then w p else 0
noncomputable def tailWeight (w : ℕ → ℝ) (H : ℕ) (p : ℕ) : ℝ := if H < p then w p else 0

lemma primeSum_prefix (w : ℕ → ℝ) {n M : ℕ} (hn : 0 < n) (hnM : n ≤ M) :
    primeSum (Nat.primesBelow (M+1)) w n=primeScore w n := by
  have he : (Nat.primesBelow (M+1)).filter (fun p => p ∣ n)=n.primeFactors := by
    ext p
    simp only [mem_filter,Nat.mem_primesBelow,Nat.mem_primeFactors]
    constructor
    · rintro ⟨⟨_,hp⟩,hpn⟩
      exact ⟨hp,hpn,hn.ne'⟩
    · rintro ⟨hp,hpn,_⟩
      exact ⟨⟨by have := (Nat.le_of_dvd hn hpn).trans hnM; omega,hp⟩,hpn⟩
  simp only [primeSum,indicator,mul_ite,mul_one,mul_zero,←sum_filter,he,primeScore]

lemma movingMean_prefix (w : ℕ → ℝ) {n M : ℕ} (hnM : cutoff n ≤ M) :
    MovingPrimeBlockVariance.movingMean (Nat.primesBelow (M+1)) w n=center w n := by
  have he : (Nat.primesBelow (M+1)).filter (fun p => p ≤ cutoff n)=
      Nat.primesBelow (cutoff n+1) := by
    ext p
    by_cases hp : p.Prime <;> simp [mem_filter,Nat.mem_primesBelow,hp]
    omega
  change mean ((Nat.primesBelow (M+1)).filter (fun p => p ≤ cutoff n)) w=prefixMean w (cutoff n)
  rw [he]
  rfl

lemma finite_mass_le (w : ℕ → ℝ)
    (hs : Summable (fun p : ℕ => if p.Prime then w p^2/p else 0))
    (P : Finset ℕ) (hP : ∀ p ∈ P,p.Prime) : mass P w ≤ energy w := by
  have hh := hs.sum_le_tsum P (fun p _ => show 0 ≤
      (if p.Prime then w p^2/p else 0) by split_ifs <;> positivity)
  have he (p : ℕ) (hp : p ∈ P) : (if p.Prime then w p^2/p else 0)=w p^2/p :=
    if_pos (hP p hp)
  simpa only [sum_congr rfl he,mass,energy] using hh

/-- There is no limiting exchange: in a fixed prefix, both scores and centers
agree exactly with a sufficiently large finite prime block. -/
theorem variance_le (w : ℕ → ℝ)
    (hs : Summable (fun p : ℕ => if p.Prime then w p^2/p else 0)) (N : ℕ) :
    (∑n∈Icc 1 N,deviation w n^2) ≤ 48*(N:ℝ)*energy w := by
  let M := max N (cutoff N)
  let P := Nat.primesBelow (M+1)
  have hP : ∀ p ∈ P,p.Prime := fun p hp => (Nat.mem_primesBelow.mp hp).2
  have he (n : ℕ) (hn : n ∈ Icc 1 N) :
      primeSum P w n-MovingPrimeBlockVariance.movingMean P w n=deviation w n := by
    rw [primeSum_prefix w (mem_Icc.mp hn).1 ((mem_Icc.mp hn).2.trans (le_max_left _ _)),
      movingMean_prefix w ((cutoff_mono (mem_Icc.mp hn).2).trans (le_max_right _ _))]
    rfl
  have hh := SharpPrimeBlockVariance.moving_variance_le N P w hP
  rw [sum_congr rfl (fun n hn => congrArg (fun x : ℝ => x^2) (he n hn))] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left (finite_mass_le w hs P hP) (by positivity))

lemma deviation_add (u v : ℕ → ℝ) (n : ℕ) :
    deviation (fun p => u p+v p) n=deviation u n+deviation v n := by
  simp only [deviation,primeScore,center,prefixMean,add_div,sum_add_distrib]
  ring

lemma split (w : ℕ → ℝ) (H n : ℕ) :
    deviation w n=deviation (headWeight w H) n+deviation (tailWeight w H) n := by
  have he : w=(fun p => headWeight w H p+tailWeight w H p) := by
    funext p
    by_cases hp : p ≤ H <;> simp [headWeight,tailWeight,hp,not_lt_of_ge,lt_of_not_ge]
  conv_lhs => rw [he,deviation_add]

lemma tail_energy (w : ℕ → ℝ) (H : ℕ) : energy (tailWeight w H)=tailEnergy w (H+1) := by
  apply tsum_congr
  intro p
  by_cases hp : p.Prime <;> by_cases hH : H < p <;>
    simp [tailWeight,hp,hH,show H+1 ≤ p ↔ H < p by omega]

lemma tail_summable (w : ℕ → ℝ)
    (hs : Summable (fun p : ℕ => if p.Prime then w p^2/p else 0)) (H : ℕ) :
    Summable (fun p : ℕ => if p.Prime then tailWeight w H p^2/p else 0) := by
  have he (p : ℕ) : (if p.Prime then tailWeight w H p^2/p else 0)=
      if p.Prime ∧ H+1 ≤ p then w p^2/p else 0 := by
    by_cases hp : p.Prime <;> by_cases hH : H < p <;>
      simp [tailWeight,hp,hH,show H+1 ≤ p ↔ H < p by omega]
  simp only [he]
  exact QuadraticScoreTailBounds.tail_summable (fun p => w p^2) (fun p => sq_nonneg _) hs (H+1)

/-- Removing a finite head makes the uniform normalized second moment as small
as desired. This alone does not make any short full-score band Sidon. -/
theorem tail_variance_small (w : ℕ → ℝ)
    (hs : Summable (fun p : ℕ => if p.Prime then w p^2/p else 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ H : ℕ,∀ N : ℕ,(∑n∈Icc 1 N,deviation (tailWeight w H) n^2) ≤ ε*N := by
  have ht := QuadraticScoreTailBounds.tail_tendsto (fun p => w p^2) (fun p => sq_nonneg _) hs
  have he : ∀ᶠ H : ℕ in atTop,tailEnergy w H < ε/48 :=
    (tendsto_order.mp ht).2 _ (by positivity)
  obtain ⟨H,hH⟩ := eventually_atTop.mp he
  refine ⟨H,fun N => ?_⟩
  have hh := variance_le (tailWeight w H) (tail_summable w hs H) N
  rw [tail_energy] at hh
  have hb := hH (H+1) (by omega)
  nlinarith [show (0:ℝ) ≤ N from Nat.cast_nonneg N]

#print axioms variance_le
#print axioms tail_variance_small
end Erdos1206.FullPrimeScoreVariance
