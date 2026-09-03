import FormalConjecturesUtil
import Submission.WeightedInputLargeDivisorEnergy

/-! A linear energy bound for all winning-prime/divisor groups, with the
explicit damping factor `p*d/(N+p*d)`. The damping cannot be discarded in the
subcritical range. This is not a proof of Erdős 371. -/

namespace Erdos371DampedDivisorEnergy

open Finset Erdos371PrimeDiscrepancy Erdos371ProductSignTransport
open Erdos371LargeDivisorSignedEnergy Erdos371RadicalLogMean
open Erdos371WeightedInputLargeDivisorEnergy
open Erdos371WeightedLargeDivisorEnergy (weight weight_nonneg)
open Erdos371SubcriticalPrimePairCancellation (count count_error)

lemma count_upper {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (N : ℕ) :
    (count a b N : ℝ) ≤ (N : ℝ)/(a*b : ℕ)+1 := by
  by_cases hc : a.Coprime b
  · linarith [(abs_le.mp (count_error ha hb hc N)).2]
  · have he : (range N).filter (fun n => a ∣ n ∧ b ∣ n+1) = ∅ := by
      apply filter_eq_empty_iff.mpr
      intro n hn hab
      exact hc (Nat.Coprime.of_dvd hab.1 hab.2 (by simp))
    simp only [count, he, card_empty, Nat.cast_zero]
    positivity

lemma up_card_upper {p d : ℕ} (hp : 0 < p) (hd : 0 < d) (N : ℕ) :
    ((up p d N).card : ℝ) ≤ (N : ℝ)/(p*d : ℕ)+1 := by
  have hs : up p d N ⊆ (range N).filter (fun n => d ∣ n ∧ p ∣ n+1) := by
    intro n hn
    obtain ⟨hn, hcmp⟩ := mem_filter.mp hn
    obtain ⟨hnN,hwin,hdiv⟩ := mem_filter.mp hn
    have hpn : P (n+1)=p := by simpa [winner,max_eq_right hcmp.le] using hwin
    refine mem_filter.mpr ⟨hnN,?_,hpn ▸ Nat.maxPrimeFac_dvd⟩
    simpa [lower,if_pos hcmp] using hdiv
  have hc : ((up p d N).card : ℝ) ≤ count d p N := Nat.cast_le.mpr (card_le_card hs)
  exact hc.trans (by simpa only [Nat.mul_comm d p] using count_upper hd hp N)

lemma down_card_upper {p d : ℕ} (hp : 0 < p) (hd : 0 < d) (N : ℕ) :
    ((down p d N).card : ℝ) ≤ (N : ℝ)/(p*d : ℕ)+1 := by
  have hs : down p d N ⊆ (range N).filter (fun n => p ∣ n ∧ d ∣ n+1) := by
    intro n hn
    obtain ⟨hn, hcmp⟩ := mem_filter.mp hn
    obtain ⟨hnN,hwin,hdiv⟩ := mem_filter.mp hn
    have hpn : P n=p := by simpa [winner,max_eq_left (le_of_not_gt hcmp)] using hwin
    refine mem_filter.mpr ⟨hnN,hpn ▸ Nat.maxPrimeFac_dvd,?_⟩
    simpa [lower,if_neg hcmp] using hdiv
  have hc : ((down p d N).card : ℝ) ≤ count p d N := Nat.cast_le.mpr (card_le_card hs)
  exact hc.trans (count_upper hp hd N)

lemma sum_square_bound (s : Finset ℕ) (a : ℕ → ℝ) {C : ℝ}
    (hC : (s.card : ℝ) ≤ C) :
    (∑ n ∈ s, a n)^2 ≤ C * ∑ n ∈ s, (a n)^2 := by
  have hh := sum_mul_sq_le_sq_mul_sq s (fun _ => (1 : ℝ)) a
  simp only [one_mul, one_pow, sum_const, nsmul_eq_mul, mul_one] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right hC (sum_nonneg (fun _ _ => sq_nonneg _)))

/-- Unlike the sparse bound, this applies to every positive product, at the
cost of the progression-length factor. -/
theorem inputGroup_square_bound {a : ℕ → ℝ} {p d N : ℕ}
    (hp : 0 < p) (hd : 0 < d) (ha : ∀ n ∈ members p d N, 0 ≤ a n) :
    (inputGroup a p d N)^2 ≤
      ((N : ℝ)/(p*d : ℕ)+1) * ∑ n ∈ members p d N, (a n)^2 := by
  have hu : 0 ≤ ∑ n ∈ up p d N, a n :=
    sum_nonneg (fun n hn => ha n (mem_filter.mp hn).1)
  have hd' : 0 ≤ ∑ n ∈ down p d N, a n :=
    sum_nonneg (fun n hn => ha n (mem_filter.mp hn).1)
  have hsu := sum_square_bound (up p d N) a (up_card_upper hp hd N)
  have hsd := sum_square_bound (down p d N) a (down_card_upper hp hd N)
  have hs : (∑ n ∈ up p d N, (a n)^2) + (∑ n ∈ down p d N, (a n)^2) =
      ∑ n ∈ members p d N, (a n)^2 := sum_filter_add_sum_filter_not _ _ _
  rw [inputGroup_split, ← hs, mul_add]
  nlinarith [mul_nonneg hu hd']

noncomputable def damping (N p d : ℕ) : ℝ := (p*d : ℕ)/(N+p*d : ℕ)

lemma damping_nonneg (N p d : ℕ) : 0 ≤ damping N p d := by
  unfold damping
  positivity

lemma damping_compensation {p d : ℕ} (hp : 0 < p) (hd : 0 < d) (N : ℕ) :
    damping N p d * ((N : ℝ)/(p*d : ℕ)+1) = 1 := by
  have hpd : (p*d : ℕ) ≠ 0 := Nat.ne_of_gt (Nat.mul_pos hp hd)
  have hsum : (N+p*d : ℕ) ≠ 0 := by omega
  unfold damping
  push_cast
  field_simp

lemma damped_group_square_le {a : ℕ → ℝ} {p d N : ℕ}
    (hp : 0 < p) (hd : 0 < d) (ha : ∀ n ∈ members p d N, 0 ≤ a n) :
    damping N p d * (inputGroup a p d N)^2 ≤
      ∑ n ∈ members p d N, (a n)^2 := by
  have hh := mul_le_mul_of_nonneg_left (inputGroup_square_bound hp hd ha)
    (damping_nonneg N p d)
  simpa only [← mul_assoc, damping_compensation hp hd N, one_mul] using hh

noncomputable def energy (a : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ p ∈ (N+1).primesBelow, ∑ q ∈ (N+1).primesBelow,
    weight N q * (damping N p q * (inputGroup a p q N)^2)

/-- An all-prime-pair linear energy bound, with explicit product damping.
The factor approaches zero when `p*q/N` does; no undamped bound is claimed. -/
theorem energy_le {a : ℕ → ℝ} {N : ℕ} (hN : 1 < N)
    (ha : ∀ n < N, 0 ≤ a n) :
    energy a N ≤ ∑ n ∈ range N, (a n)^2 := by
  have hb : energy a N ≤
      ∑ p ∈ (N+1).primesBelow, ∑ q ∈ (N+1).primesBelow,
        weight N q * (∑ n ∈ members p q N, (a n)^2) := by
    apply sum_le_sum
    intro p hp
    apply sum_le_sum
    intro q hq
    exact mul_le_mul_of_nonneg_left
      (damped_group_square_le (Nat.prime_of_mem_primesBelow hp).pos
        (Nat.prime_of_mem_primesBelow hq).pos
        (fun n hn => ha n (mem_range.mp (mem_filter.mp hn).1)))
      (weight_nonneg N q)
  rw [input_diagonal_eq] at hb
  apply hb.trans
  apply sum_le_sum
  intro n hn
  by_cases hz : n=0
  · simpa [hz] using (sq_nonneg (a 0))
  · rw [if_neg hz]
    have hl : level N (lower n) ≤ 1 :=
      (level_bounds hN (by have := mem_range.mp hn; have := lower_bounds n; omega)).2
    simpa using mul_le_mul_of_nonneg_left hl (sq_nonneg (a n))

/-- In particular, the damped energy of the unweighted signed groups is linear. -/
theorem unweighted_energy_le {N : ℕ} (hN : 1 < N) :
    energy (fun _ => 1) N ≤ N := by
  simpa using energy_le (a := fun _ => 1) hN (fun _ _ => zero_le_one)

end Erdos371DampedDivisorEnergy

#print axioms Erdos371DampedDivisorEnergy.inputGroup_square_bound
#print axioms Erdos371DampedDivisorEnergy.energy_le
