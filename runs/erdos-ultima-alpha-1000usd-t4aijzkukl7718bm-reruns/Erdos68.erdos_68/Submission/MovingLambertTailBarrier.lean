import Submission.ShiftedLambertTailBarrier
import Submission.FactorialClearingIndex

/-!
A moving row cutoff at or below half the factorial index still has
quadratically large scaled Lambert tails. This auxiliary obstruction does
not settle the conjecture in Spec.lean.
-/

namespace Erdos68Development

lemma central_factorial_square_bound (k : ℕ) (hk : 9 ≤ k) :
    (2 * k + 1) ^ 2 * (k + 1).factorial ^ 2 ≤ (2 * k).factorial := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have hkk : 3 * k ≤ k * k := Nat.mul_le_mul_right k (by omega : 3 ≤ k)
    have h₁ : (2 * k + 3) ^ 2 ≤ 2 * (2 * k + 1) ^ 2 := by nlinarith
    have h₂ : 2 * (k + 2) ^ 2 ≤ (2 * k + 2) * (2 * k + 1) := by nlinarith
    have hp : (2 * k + 3) ^ 2 * (k + 2) ^ 2 ≤
        ((2 * k + 2) * (2 * k + 1)) * (2 * k + 1) ^ 2 := by
      calc
        _ ≤ (2 * (2 * k + 1) ^ 2) * (k + 2) ^ 2 := Nat.mul_le_mul_right _ h₁
        _ = (2 * (k + 2) ^ 2) * (2 * k + 1) ^ 2 := by ring
        _ ≤ _ := Nat.mul_le_mul_right _ h₂
    have hf : (2 * (k + 1)).factorial =
        ((2 * k + 2) * (2 * k + 1)) * (2 * k).factorial := by
      rw [show 2 * (k + 1) = (2 * k + 1) + 1 by omega,
        Nat.factorial_succ, Nat.factorial_succ]
      ring
    calc
      _ = ((2 * k + 3) ^ 2 * (k + 2) ^ 2) * (k + 1).factorial ^ 2 := by
        rw [Nat.factorial_succ (k + 1)]
        ring
      _ ≤ (((2 * k + 2) * (2 * k + 1)) * (2 * k + 1) ^ 2) *
          (k + 1).factorial ^ 2 := Nat.mul_le_mul_right _ hp
      _ = ((2 * k + 2) * (2 * k + 1)) *
          ((2 * k + 1) ^ 2 * (k + 1).factorial ^ 2) := by ring
      _ ≤ ((2 * k + 2) * (2 * k + 1)) * (2 * k).factorial :=
        Nat.mul_le_mul_left _ ih
      _ = _ := hf.symm

lemma half_index_factorial_square_bound (n : ℕ) (hn : 18 ≤ n) :
    n ^ 2 * (n / 2 + 1).factorial ^ 2 ≤ n.factorial := by
  calc
    _ ≤ (2 * (n / 2) + 1) ^ 2 * (n / 2 + 1).factorial ^ 2 := by
      gcongr
      omega
    _ ≤ (2 * (n / 2)).factorial := central_factorial_square_bound _ (by omega)
    _ ≤ n.factorial := Nat.factorial_le (by omega)

lemma scaledTail_ge_later (c : ℕ → ℕ)
    (hs : Summable (fun m : ℕ => (c m : ℝ) / m.factorial))
    (n m : ℕ) (hm : n < m) :
    (n.factorial : ℝ) * ((c m : ℝ) / m.factorial) ≤
      FactorialTailCriterion.scaledTail (fun j => (c j : ℤ)) n := by
  let f : ℕ → ℝ := fun j => (c j : ℝ) / j.factorial
  have ht : Summable (fun j => f (j + (n + 1))) := (summable_nat_add_iff (n + 1)).mpr hs
  have he := hs.sum_add_tsum_nat_add (n + 1)
  have hsingle : f m ≤ ∑' j : ℕ, f (j + (n + 1)) := by
    simpa only [Nat.sub_add_cancel (by omega : n + 1 ≤ m)] using
      ht.le_tsum (m - (n + 1)) (fun _ _ => by dsimp [f]; positivity)
  have he' : (∑' j : ℕ, f (j + (n + 1))) =
      (∑' j : ℕ, f j) - ∑ j ∈ Finset.range (n + 1), f j := by
    change (∑ j ∈ Finset.range (n + 1), f j) + _ = _ at he
    linarith
  have h := mul_le_mul_of_nonneg_left hsingle (show (0 : ℝ) ≤ n.factorial by positivity)
  rw [he'] at h
  simpa [FactorialTailCriterion.scaledTail, f] using h

/-- Keeping row `n/2+1` already forces a quadratic lower bound, uniformly
in the cutoff. No rationality assumption is involved. -/
theorem moving_lambert_tail_ge_square (K n : ℕ)
    (hn : 18 ≤ n) (hK : K ≤ n / 2 + 1) :
    (n : ℝ) ^ 2 ≤
      FactorialTailCriterion.scaledTail (fun m => (lambertCoeffFrom K m : ℤ)) n := by
  let d := n / 2 + 1
  have hd : 2 ≤ d := by dsimp [d]; omega
  have hnd : n < d * 2 := by dsimp [d]; omega
  have hfac : (n : ℝ) ^ 2 * (d.factorial : ℝ) ^ 2 ≤ n.factorial := by
    exact_mod_cast half_index_factorial_square_bound n hn
  have hscl : (n : ℝ) ^ 2 ≤ (n.factorial : ℝ) / (d.factorial : ℝ) ^ 2 :=
    (le_div_iff₀ (by positivity)).mpr hfac
  have hrow := lambertFrom_single_row_lower K d 2 hd hK (by norm_num)
  have hlater := scaledTail_ge_later (lambertCoeffFrom K)
    (summable_factorial_lambertFrom K) n (d * 2) hnd
  calc
    _ ≤ (n.factorial : ℝ) / (d.factorial : ℝ) ^ 2 := hscl
    _ = (n.factorial : ℝ) * (1 / (d.factorial : ℝ) ^ 2) := by ring
    _ ≤ (n.factorial : ℝ) *
        ((lambertCoeffFrom K (d * 2) : ℝ) / (d * 2).factorial) := by gcongr
    _ ≤ _ := hlater

/-- Clearing even the last removed denominator termwise forces the index
into the range where the remaining Lambert scaled tail is at least `n²`.
This makes no claim about reduced denominators of a sum. -/
theorem cleared_moving_lambert_tail_ge_square (K n : ℕ)
    (hK : 10 ≤ K) (hclear : (K - 1).factorial - 1 ∣ n.factorial) :
    (n : ℝ) ^ 2 ≤
      FactorialTailCriterion.scaledTail (fun m => (lambertCoeffFrom K m : ℤ)) n := by
  have hlarge : 2 * (K - 1) < n := by
    by_contra h
    exact FactorialClearingIndex.not_dvd_double_factorial (by omega : 9 ≤ K - 1)
      (hclear.trans (Nat.factorial_dvd_factorial (by omega)))
  exact moving_lambert_tail_ge_square K n (by omega) (by omega)

#print axioms moving_lambert_tail_ge_square
#print axioms cleared_moving_lambert_tail_ge_square

end Erdos68Development
