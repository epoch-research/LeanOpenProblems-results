import Mathlib
import Submission.Spec
import Submission.Helper4

open Nat

lemma a_even_eval_rearranged (k : ℕ) (hk : 2 ≤ k) :
  A340738 (2 * k) + A340738 (2 * k - 2) + (k - 1) * A340738 (2 * k - 3) = (k + 1) * A340738 (2 * k - 1) := by
  have def_2k : A340738 (2 * k) = (k + 1) * A340738 (2 * k - 1) - A340738 (2 * k - 2) - (k - 1) * A340738 (2 * k - 3) := by
    have heq : 2 * k = 2 * k - 3 + 3 := by omega
    nth_rw 1 [heq]; rw [A340738]; rw [show (2 * k - 3 + 3) % 2 = 0 by omega]; dsimp
    have c1 : (2 * k - 3 + 3 + 2) / 2 = k + 1 := by omega
    have c2 : (2 * k - 3 + 3 - 2) / 2 = k - 1 := by omega
    have r1 : A340738 (2 * k - 3 + 2) = A340738 (2 * k - 1) := by congr 1; omega
    have r2 : A340738 (2 * k - 3 + 3 - 2) = A340738 (2 * k - 2) := by congr 1; omega
    have r3 : A340738 (2 * k - 3 + 3 - 3) = A340738 (2 * k - 3) := by congr 1
    rw [c1, c2, r1, r2, r3]
  have mono := a_mono_pair (k - 1) (by omega)
  have h4 := mono.2.2.2
  have h_replace : A340738 (2 * (k - 1)) + (k - 1) * A340738 (2 * (k - 1) - 1) ≤ (k - 1 + 1) * A340738 (2 * (k - 1) + 1) := h4
  have eq1 : A340738 (2 * (k - 1)) = A340738 (2 * k - 2) := by congr 1; omega
  have eq2 : A340738 (2 * (k - 1) - 1) = A340738 (2 * k - 3) := by congr 1; omega
  have eq3 : A340738 (2 * (k - 1) + 1) = A340738 (2 * k - 1) := by congr 1; omega
  have e4 : k - 1 + 1 = k := by omega
  rw [eq1, eq2, eq3, e4] at h_replace
  have h_mul : k * A340738 (2 * k - 1) + A340738 (2 * k - 1) = (k + 1) * A340738 (2 * k - 1) := by ring
  omega

lemma b_even_eval_rearranged (k : ℕ) (hk : 2 ≤ k) :
  A340737 (2 * k) + A340737 (2 * k - 2) + (k - 1) * A340737 (2 * k - 3) = (k + 1) * A340737 (2 * k - 1) := by
  have def_2k : A340737 (2 * k) = (k + 1) * A340737 (2 * k - 1) - A340737 (2 * k - 2) - (k - 1) * A340737 (2 * k - 3) := by
    have heq : 2 * k = 2 * k - 3 + 3 := by omega
    nth_rw 1 [heq]; rw [A340737]; rw [show (2 * k - 3 + 3) % 2 = 0 by omega]; dsimp
    have c1 : (2 * k - 3 + 3 + 2) / 2 = k + 1 := by omega
    have c2 : (2 * k - 3 + 3 - 2) / 2 = k - 1 := by omega
    have r1 : A340737 (2 * k - 3 + 2) = A340737 (2 * k - 1) := by congr 1; omega
    have r2 : A340737 (2 * k - 3 + 3 - 2) = A340737 (2 * k - 2) := by congr 1; omega
    have r3 : A340737 (2 * k - 3 + 3 - 3) = A340737 (2 * k - 3) := by congr 1
    rw [c1, c2, r1, r2, r3]
  have mono := b_mono_pair (k - 1) (by omega)
  have h4 := mono.2.2.2
  have h_replace : A340737 (2 * (k - 1)) + (k - 1) * A340737 (2 * (k - 1) - 1) ≤ (k - 1 + 1) * A340737 (2 * (k - 1) + 1) := h4
  have eq1 : A340737 (2 * (k - 1)) = A340737 (2 * k - 2) := by congr 1; omega
  have eq2 : A340737 (2 * (k - 1) - 1) = A340737 (2 * k - 3) := by congr 1; omega
  have eq3 : A340737 (2 * (k - 1) + 1) = A340737 (2 * k - 1) := by congr 1; omega
  have e4 : k - 1 + 1 = k := by omega
  rw [eq1, eq2, eq3, e4] at h_replace
  have h_mul : k * A340737 (2 * k - 1) + A340737 (2 * k - 1) = (k + 1) * A340737 (2 * k - 1) := by ring
  omega

