import Submission.FactorialLambert
import Submission.FactorialTailCriterion

/-!
The factorial Lambert expansion does not meet the small-tail hypothesis of
the auxiliary descent criterion. This is an obstruction to that direct
application, not a proof or disproof of the original irrationality problem.
-/

namespace Erdos68Development

lemma factorial_lambert_even_term_lower (k : ℕ) (hk : 0 < k) :
    1 / (2 : ℝ) ^ k ≤
      (lambertCoeff (2 * k) : ℝ) / (2 * k).factorial := by
  have h := lambertCoeff_even_lower k hk
  have hd : 2 ^ k ∣ (2 * k).factorial := by
    simpa using factorial_pow_dvd_factorial_mul 2 k
  have hcast : ((2 * k).factorial : ℝ) / (2 : ℝ) ^ k ≤ lambertCoeff (2 * k) := by
    exact_mod_cast (show ((2 * k).factorial / 2 ^ k : ℕ) ≤ lambertCoeff (2 * k) from h)
  have hf : (0 : ℝ) < (2 * k).factorial := by positivity
  apply (le_div_iff₀ hf).mpr
  simpa [div_eq_mul_inv, mul_comm] using hcast

lemma factorial_lambert_tail_large (k : ℕ) :
    (2 * k + 5 : ℝ) ≤
      FactorialTailCriterion.scaledTail (fun m => (lambertCoeff m : ℤ)) (2 * k + 5) := by
  let n := 2 * k + 5
  let f : ℕ → ℝ := fun m => (lambertCoeff m : ℝ) / m.factorial
  have hs : Summable f := summable_factorial_lambert
  have ht : Summable (fun j => f (j + (n + 1))) := (summable_nat_add_iff (n + 1)).mpr hs
  have hsplit := hs.sum_add_tsum_nat_add (n + 1)
  have hsingle : f (n + 1) ≤ ∑' j : ℕ, f (j + (n + 1)) := by
    simpa only [zero_add] using ht.le_tsum 0 (fun _ _ => by dsimp [f]; positivity)
  have htail : FactorialTailCriterion.scaledTail (fun m => (lambertCoeff m : ℤ)) n =
      (n.factorial : ℝ) * ∑' j : ℕ, f (j + (n + 1)) := by
    unfold FactorialTailCriterion.scaledTail
    simp only [Int.cast_natCast]
    change (n.factorial : ℝ) * ((∑' m, f m) - ∑ m ∈ Finset.range (n + 1), f m) = _
    congr 1
    linarith
  have hterm : 1 / (2 : ℝ) ^ (k + 3) ≤ f (n + 1) := by
    have h := factorial_lambert_even_term_lower (k + 3) (by omega)
    simpa [f, n, show 2 * (k + 3) = 2 * k + 5 + 1 by omega] using h
  have hfac : 2 ^ (k + 3) ≤ (2 * k + 4).factorial := by
    have h := even_factorial_lower k
    rw [show 2 * (k + 2) = 2 * k + 4 by omega] at h
    rw [show k + 3 = (k + 2) + 1 by omega, pow_succ]
    nlinarith [show 0 < (2 : ℕ) ^ (k + 2) by positivity]
  have hscaled : (n : ℝ) ≤ (n.factorial : ℝ) / (2 : ℝ) ^ (k + 3) := by
    apply (le_div_iff₀ (by positivity)).mpr
    have hfacr : (2 : ℝ) ^ (k + 3) ≤ (2 * k + 4).factorial := by exact_mod_cast hfac
    have hnfac : n.factorial = n * (2 * k + 4).factorial := by
      dsimp [n]
      rw [show 2 * k + 5 = (2 * k + 4) + 1 by omega, Nat.factorial_succ]
    rw [hnfac, Nat.cast_mul]
    exact mul_le_mul_of_nonneg_left hfacr (by positivity)
  have hncast : (n : ℝ) = 2 * k + 5 := by dsimp [n]; push_cast; ring
  rw [← hncast]
  change (n : ℝ) ≤ FactorialTailCriterion.scaledTail (fun m => (lambertCoeff m : ℤ)) n
  rw [htail]
  calc
    (n : ℝ) ≤ (n.factorial : ℝ) / (2 : ℝ) ^ (k + 3) := hscaled
    _ = (n.factorial : ℝ) * (1 / (2 : ℝ) ^ (k + 3)) := by ring
    _ ≤ (n.factorial : ℝ) * ∑' j : ℕ, f (j + (n + 1)) :=
      mul_le_mul_of_nonneg_left (hterm.trans hsingle) (by positivity)

lemma factorial_lambert_not_eventually_small_tail :
    ¬ ∃ N : ℕ, ∀ n ≥ N,
      FactorialTailCriterion.scaledTail (fun m => (lambertCoeff m : ℤ)) n < (n : ℝ) - 1 := by
  rintro ⟨N, hN⟩
  have h := hN (2 * N + 5) (by omega)
  have hl := factorial_lambert_tail_large N
  push_cast at h
  linarith

end Erdos68Development

#print axioms Erdos68Development.factorial_lambert_tail_large
#print axioms Erdos68Development.factorial_lambert_not_eventually_small_tail
