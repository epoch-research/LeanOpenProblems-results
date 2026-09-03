import FormalConjecturesUtil
import Submission.SelbergMoment
import Submission.ResidueSieve
import Submission.LogSmoothCount

/-! A finite two-root Selberg sieve with a polynomial cutoff error. -/

namespace Erdos371ResidueSelberg

open Finset Erdos371FiniteBrun Erdos371FiniteSelberg Erdos371SelbergMoment
  Erdos371ResidueSieve Erdos371LogSmoothCount

attribute [local instance] Classical.propDecidable

lemma local_log_sum_bound {s : Finset ℕ} {w : ℕ} (hw : 0 < w)
    (hs : s ⊆ w.primesBelow) (ν : ℕ → ℝ) (hν : ∀ p ∈ s, ν p ≤ 2/(p:ℝ)) :
    (∑ p ∈ s, ν p * Real.log (p:ℝ)) ≤ 2*(Real.log w + Real.log 4) := by
  calc
    _ ≤ ∑ p ∈ s, 2*(Real.log (p:ℝ)/(p:ℝ)) := by
      apply sum_le_sum
      intro p hp
      have hh := mul_le_mul_of_nonneg_right (hν p hp) (Real.log_natCast_nonneg p)
      convert hh using 1 <;> ring
    _ ≤ ∑ p ∈ (w+1).primesBelow, 2*(Real.log (p:ℝ)/(p:ℝ)) := by
      apply sum_le_sum_of_subset_of_nonneg (hs.trans ?_) (fun p hp _ => by positivity)
      intro p hp
      exact Nat.mem_primesBelow.mpr ⟨by have := (Nat.mem_primesBelow.mp hp).1; omega,
        (Nat.mem_primesBelow.mp hp).2⟩
    _ ≤ _ := by rw [← mul_sum]; exact mul_le_mul_of_nonneg_left (prime_log_div_bound hw) (by norm_num)

lemma cutoff_log_bound {s : Finset ℕ} {w : ℕ} (hw : 0 < w)
    (hs : s ⊆ w.primesBelow) (ν : ℕ → ℝ) (hν : ∀ p ∈ s, ν p ≤ 2/(p:ℝ)) :
    2*(∑ p ∈ s, ν p * Real.log (p:ℝ)) ≤ Real.log ((4*(w:ℝ))^4) := by
  rw [Real.log_pow, Real.log_mul (by norm_num) (Nat.cast_ne_zero.mpr hw.ne')]
  have hh := local_log_sum_bound hw hs ν hν
  norm_num
  linarith

/-- Arbitrary nonempty proper sets of at most two forbidden residues, at
primes below `w`. No arithmetic cancellation hypothesis remains. -/
theorem residue_selberg_upper {s : Finset ℕ} {w : ℕ} (hw : 0 < w)
    (hs : s ⊆ w.primesBelow) (R : ℕ → Finset ℕ)
    (hR : ∀ p ∈ s, R p ⊆ range p)
    (hR0 : ∀ p ∈ s, 0 < (R p).card) (hRp : ∀ p ∈ s, (R p).card < p)
    (hR2 : ∀ p ∈ s, (R p).card ≤ 2) (N : ℕ) :
    (survivors (range N) s (residueEvent R)).card ≤
      2*(N:ℝ)*(∏ p ∈ s, (1-localDensity R p))+(4*(w:ℝ))^16 := by
  have hp (p : ℕ) (hp : p ∈ s) : p.Prime := (Nat.mem_primesBelow.mp (hs hp)).2
  have hν (p : ℕ) (hps : p ∈ s) : 0 < localDensity R p ∧ localDensity R p < 1 := by
    have hp0 : (0:ℝ) < p := Nat.cast_pos.mpr (hp p hps).pos
    constructor
    · exact div_pos (Nat.cast_pos.mpr (hR0 p hps)) hp0
    · exact (div_lt_one hp0).mpr (Nat.cast_lt.mpr (hRp p hps))
  have hν2 (p : ℕ) (hps : p ∈ s) : localDensity R p ≤ 2/(p:ℝ) := by
    exact div_le_div_of_nonneg_right (by exact_mod_cast hR2 p hps) (Nat.cast_nonneg _)
  have hz : 1 < (4*(w:ℝ))^4 := by
    have hw' : (1:ℝ) ≤ w := by exact_mod_cast hw
    have hbase : (1:ℝ) < 4*w := by linarith
    exact one_lt_pow₀ hbase (by norm_num)
  have hb := selberg_euler_upper (range N) s (residueEvent R) (localDensity R)
    (fun p => ((R p).card:ℝ)) (fun p => (p:ℝ)) hν
    (fun p hps => by
      change (1:ℝ) ≤ (R p).card
      exact_mod_cast (show 1 ≤ (R p).card from hR0 p hps))
    (fun p hps => by
      change (2:ℝ) ≤ p
      exact_mod_cast (hp p hps).two_le)
    (fun p hps => by
      dsimp [localDensity]
      have hr : ((R p).card:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (hR0 p hps).ne'
      have hp0 : (p:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (hp p hps).ne_zero
      field_simp)
    N (Nat.cast_nonneg _) (by
      intro t ht
      exact joint_count_error (fun p hps => hp p (ht hps)) R (fun p hps => hR p (ht hps)) N)
    hz (cutoff_log_bound hw hs _ hν2)
  simpa only [← pow_mul] using hb

end Erdos371ResidueSelberg

#print axioms Erdos371ResidueSelberg.residue_selberg_upper
