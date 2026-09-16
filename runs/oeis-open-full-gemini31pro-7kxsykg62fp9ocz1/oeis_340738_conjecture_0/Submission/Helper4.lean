import Mathlib
import Submission.Spec
open Nat

lemma a_odd_eval (k : ℕ) (hk : 1 ≤ k) :
  A340738 (2 * k + 1) = 2 * A340738 (2 * k) + (2 * k + 1) * A340738 (2 * k - 1) := by
  have h_eq : 2 * k + 1 = (2 * k - 2) + 3 := by omega
  nth_rw 1 [h_eq]; rw [A340738]; rw [show ((2 * k - 2) + 3) % 2 = 1 by omega]; dsimp
  have e1 : (2 * k - 2) + 2 = 2 * k := by omega
  have e2 : (2 * k - 2) + 3 = 2 * k + 1 := by omega
  have e3 : (2 * k - 2) + 3 - 2 = 2 * k - 1 := by omega
  have h1 : A340738 ((2 * k - 2) + 2) = A340738 (2 * k) := by rw [e1]
  have h2 : A340738 ((2 * k - 2) + 3 - 2) = A340738 (2 * k - 1) := by rw [e3]
  rw [h1, h2, e2]

lemma a_mono_pair (k : ℕ) (hk : 1 ≤ k) :
  1 ≤ A340738 (2 * k - 1) ∧ 
  A340738 (2 * k - 1) < A340738 (2 * k) ∧ 
  A340738 (2 * k) < A340738 (2 * k + 1) ∧
  A340738 (2 * k) + k * A340738 (2 * k - 1) ≤ (k + 1) * A340738 (2 * k + 1) := by
  induction' k, hk using Nat.le_induction with k hk ih
  · exact ⟨by decide, by decide, by decide, by decide⟩
  · rcases ih with ⟨ih1, ih2, ih3, ih4⟩
    have e1 : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
    have h1 : 1 ≤ A340738 (2 * (k + 1) - 1) := by rw [e1]; omega
    have h2 : A340738 (2 * (k + 1) - 1) < A340738 (2 * (k + 1)) := by
      have def_2k2 : A340738 (2 * (k + 1)) = (k + 2) * A340738 (2 * k + 1) - A340738 (2 * k) - k * A340738 (2 * k - 1) := by
        have heq : 2 * (k + 1) = 2 * k - 1 + 3 := by omega
        nth_rw 1 [heq]; rw [A340738]; rw [show (2 * k - 1 + 3) % 2 = 0 by omega]; dsimp
        have c1 : (2 * k - 1 + 3 + 2) / 2 = k + 2 := by omega
        have c2 : (2 * k - 1 + 3 - 2) / 2 = k := by omega
        have r1 : A340738 (2 * k - 1 + 2) = A340738 (2 * k + 1) := by congr 1; omega
        have r2 : A340738 (2 * k - 1 + 3 - 2) = A340738 (2 * k) := by congr 1; omega
        have r3 : A340738 (2 * k - 1 + 3 - 3) = A340738 (2 * k - 1) := by congr 1
        rw [c1, c2, r1, r2, r3]
      rw [def_2k2, e1]
      have hk_z : (1:ℤ) ≤ (k:ℤ) := by exact_mod_cast hk
      have step1 : (A340738 (2 * k) : ℤ) ≤ (A340738 (2 * k + 1) : ℤ) - 1 := by omega
      have step2 : (A340738 (2 * k - 1) : ℤ) ≤ (A340738 (2 * k + 1) : ℤ) - 2 := by omega
      have step3 : (k : ℤ) * (A340738 (2 * k - 1) : ℤ) ≤ (k : ℤ) * ((A340738 (2 * k + 1) : ℤ) - 2) := by nlinarith
      have step4 : (A340738 (2 * k) : ℤ) + (k : ℤ) * (A340738 (2 * k - 1) : ℤ) ≤ (A340738 (2 * k + 1) : ℤ) - 1 + (k : ℤ) * ((A340738 (2 * k + 1) : ℤ) - 2) := by linarith
      have step5 : (A340738 (2 * k + 1) : ℤ) - 1 + (k : ℤ) * ((A340738 (2 * k + 1) : ℤ) - 2) < ((k + 2 : ℕ) : ℤ) * (A340738 (2 * k + 1) : ℤ) - (A340738 (2 * k + 1) : ℤ) := by
        calc
          (A340738 (2 * k + 1) : ℤ) - 1 + (k : ℤ) * ((A340738 (2 * k + 1) : ℤ) - 2)
            = ((k:ℤ) + 1) * (A340738 (2 * k + 1) : ℤ) - 2 * (k:ℤ) - 1 := by ring
          _ < ((k:ℤ) + 1) * (A340738 (2 * k + 1) : ℤ) := by linarith
          _ = ((k + 2 : ℕ) : ℤ) * (A340738 (2 * k + 1) : ℤ) - (A340738 (2 * k + 1) : ℤ) := by push_cast; ring
      have step6 : (A340738 (2 * k) : ℤ) + (k : ℤ) * (A340738 (2 * k - 1) : ℤ) + (A340738 (2 * k + 1) : ℤ) < ((k + 2 : ℕ) : ℤ) * (A340738 (2 * k + 1) : ℤ) := by linarith
      have step6_nat : A340738 (2 * k) + k * A340738 (2 * k - 1) + A340738 (2 * k + 1) < (k + 2) * A340738 (2 * k + 1) := by exact_mod_cast step6
      omega
    have h3 : A340738 (2 * (k + 1)) < A340738 (2 * (k + 1) + 1) := by
      have odd_eval := a_odd_eval (k + 1) (by omega)
      nlinarith
    have h4 : A340738 (2 * (k + 1)) + (k + 1) * A340738 (2 * (k + 1) - 1) ≤ (k + 2) * A340738 (2 * (k + 1) + 1) := by
      nlinarith
    exact ⟨h1, h2, h3, h4⟩

lemma b_odd_eval (k : ℕ) (hk : 1 ≤ k) :
  A340737 (2 * k + 1) = 2 * A340737 (2 * k) + (2 * k + 1) * A340737 (2 * k - 1) := by
  have h_eq : 2 * k + 1 = (2 * k - 2) + 3 := by omega
  nth_rw 1 [h_eq]; rw [A340737]; rw [show ((2 * k - 2) + 3) % 2 = 1 by omega]; dsimp
  have e1 : (2 * k - 2) + 2 = 2 * k := by omega
  have e2 : (2 * k - 2) + 3 = 2 * k + 1 := by omega
  have e3 : (2 * k - 2) + 3 - 2 = 2 * k - 1 := by omega
  have h1 : A340737 ((2 * k - 2) + 2) = A340737 (2 * k) := by rw [e1]
  have h2 : A340737 ((2 * k - 2) + 3 - 2) = A340737 (2 * k - 1) := by rw [e3]
  rw [h1, h2, e2]

lemma b_mono_pair (k : ℕ) (hk : 1 ≤ k) :
  1 ≤ A340737 (2 * k - 1) ∧ 
  A340737 (2 * k - 1) < A340737 (2 * k) ∧ 
  A340737 (2 * k) < A340737 (2 * k + 1) ∧
  A340737 (2 * k) + k * A340737 (2 * k - 1) ≤ (k + 1) * A340737 (2 * k + 1) := by
  induction' k, hk using Nat.le_induction with k hk ih
  · exact ⟨by decide, by decide, by decide, by decide⟩
  · rcases ih with ⟨ih1, ih2, ih3, ih4⟩
    have e1 : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
    have h1 : 1 ≤ A340737 (2 * (k + 1) - 1) := by rw [e1]; omega
    have h2 : A340737 (2 * (k + 1) - 1) < A340737 (2 * (k + 1)) := by
      have def_2k2 : A340737 (2 * (k + 1)) = (k + 2) * A340737 (2 * k + 1) - A340737 (2 * k) - k * A340737 (2 * k - 1) := by
        have heq : 2 * (k + 1) = 2 * k - 1 + 3 := by omega
        nth_rw 1 [heq]; rw [A340737]; rw [show (2 * k - 1 + 3) % 2 = 0 by omega]; dsimp
        have c1 : (2 * k - 1 + 3 + 2) / 2 = k + 2 := by omega
        have c2 : (2 * k - 1 + 3 - 2) / 2 = k := by omega
        have r1 : A340737 (2 * k - 1 + 2) = A340737 (2 * k + 1) := by congr 1; omega
        have r2 : A340737 (2 * k - 1 + 3 - 2) = A340737 (2 * k) := by congr 1; omega
        have r3 : A340737 (2 * k - 1 + 3 - 3) = A340737 (2 * k - 1) := by congr 1
        rw [c1, c2, r1, r2, r3]
      rw [def_2k2, e1]
      have hk_z : (1:ℤ) ≤ (k:ℤ) := by exact_mod_cast hk
      have step1 : (A340737 (2 * k) : ℤ) ≤ (A340737 (2 * k + 1) : ℤ) - 1 := by omega
      have step2 : (A340737 (2 * k - 1) : ℤ) ≤ (A340737 (2 * k + 1) : ℤ) - 2 := by omega
      have step3 : (k : ℤ) * (A340737 (2 * k - 1) : ℤ) ≤ (k : ℤ) * ((A340737 (2 * k + 1) : ℤ) - 2) := by nlinarith
      have step4 : (A340737 (2 * k) : ℤ) + (k : ℤ) * (A340737 (2 * k - 1) : ℤ) ≤ (A340737 (2 * k + 1) : ℤ) - 1 + (k : ℤ) * ((A340737 (2 * k + 1) : ℤ) - 2) := by linarith
      have step5 : (A340737 (2 * k + 1) : ℤ) - 1 + (k : ℤ) * ((A340737 (2 * k + 1) : ℤ) - 2) < ((k + 2 : ℕ) : ℤ) * (A340737 (2 * k + 1) : ℤ) - (A340737 (2 * k + 1) : ℤ) := by
        calc
          (A340737 (2 * k + 1) : ℤ) - 1 + (k : ℤ) * ((A340737 (2 * k + 1) : ℤ) - 2)
            = ((k:ℤ) + 1) * (A340737 (2 * k + 1) : ℤ) - 2 * (k:ℤ) - 1 := by ring
          _ < ((k:ℤ) + 1) * (A340737 (2 * k + 1) : ℤ) := by linarith
          _ = ((k + 2 : ℕ) : ℤ) * (A340737 (2 * k + 1) : ℤ) - (A340737 (2 * k + 1) : ℤ) := by push_cast; ring
      have step6 : (A340737 (2 * k) : ℤ) + (k : ℤ) * (A340737 (2 * k - 1) : ℤ) + (A340737 (2 * k + 1) : ℤ) < ((k + 2 : ℕ) : ℤ) * (A340737 (2 * k + 1) : ℤ) := by linarith
      have step6_nat : A340737 (2 * k) + k * A340737 (2 * k - 1) + A340737 (2 * k + 1) < (k + 2) * A340737 (2 * k + 1) := by exact_mod_cast step6
      omega
    have h3 : A340737 (2 * (k + 1)) < A340737 (2 * (k + 1) + 1) := by
      have odd_eval := b_odd_eval (k + 1) (by omega)
      nlinarith
    have h4 : A340737 (2 * (k + 1)) + (k + 1) * A340737 (2 * (k + 1) - 1) ≤ (k + 2) * A340737 (2 * (k + 1) + 1) := by
      nlinarith
    exact ⟨h1, h2, h3, h4⟩

