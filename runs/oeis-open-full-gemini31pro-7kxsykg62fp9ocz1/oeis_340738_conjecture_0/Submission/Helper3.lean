import Mathlib
import Submission.Spec
open Nat

lemma a_odd_eval (k : ℕ) (hk : 1 ≤ k) :
  A340738 (2 * k + 1) = 2 * A340738 (2 * k) + (2 * k + 1) * A340738 (2 * k - 1) := by
  have h_eq : 2 * k + 1 = (2 * k - 2) + 3 := by omega
  nth_rw 1 [h_eq]; rw [A340738]
  have h_mod : ((2 * k - 2) + 3) % 2 = 1 := by omega
  rw [h_mod]; dsimp
  have e1 : (2 * k - 2) + 2 = 2 * k := by omega
  have e2 : (2 * k - 2) + 3 = 2 * k + 1 := by omega
  have e3 : (2 * k - 2) + 3 - 2 = 2 * k - 1 := by omega
  have h1 : A340738 ((2 * k - 2) + 2) = A340738 (2 * k) := by rw [e1]
  have h2 : A340738 ((2 * k - 2) + 3 - 2) = A340738 (2 * k - 1) := by rw [e3]
  rw [h1, h2, e2]

lemma a_even_eval_add (k : ℕ) (hk : 2 ≤ k) :
  A340738 (2 * k) + A340738 (2 * k - 2) + (k - 1) * A340738 (2 * k - 3) = (k + 1) * A340738 (2 * k - 1) := by
  have h_eq : 2 * k = (2 * k - 3) + 3 := by omega
  nth_rw 1 [h_eq]; rw [A340738]
  have h_mod : ((2 * k - 3) + 3) % 2 = 0 := by omega
  rw [h_mod]; dsimp
  have e1 : ((2 * k - 3) + 3 + 2) / 2 = k + 1 := by omega
  have e2 : ((2 * k - 3) + 3 - 2) / 2 = k - 1 := by omega
  rw [e1, e2]
  have h1 : A340738 (2 * k - 3 + 2) = A340738 (2 * k - 1) := by congr 1; omega
  have h2 : A340738 (2 * k - 3 + 3 - 2) = A340738 (2 * k - 2) := by congr 1; omega
  have h3 : A340738 (2 * k - 3 + 3 - 3) = A340738 (2 * k - 3) := by congr 1
  rw [h1, h2, h3]
  omega

lemma b_odd_eval (k : ℕ) (hk : 1 ≤ k) :
  A340737 (2 * k + 1) = 2 * A340737 (2 * k) + (2 * k + 1) * A340737 (2 * k - 1) := by
  have h_eq : 2 * k + 1 = (2 * k - 2) + 3 := by omega
  nth_rw 1 [h_eq]; rw [A340737]
  have h_mod : ((2 * k - 2) + 3) % 2 = 1 := by omega
  rw [h_mod]; dsimp
  have e1 : (2 * k - 2) + 2 = 2 * k := by omega
  have e2 : (2 * k - 2) + 3 = 2 * k + 1 := by omega
  have e3 : (2 * k - 2) + 3 - 2 = 2 * k - 1 := by omega
  have h1 : A340737 ((2 * k - 2) + 2) = A340737 (2 * k) := by rw [e1]
  have h2 : A340737 ((2 * k - 2) + 3 - 2) = A340737 (2 * k - 1) := by rw [e3]
  rw [h1, h2, e2]

lemma b_even_eval_add (k : ℕ) (hk : 2 ≤ k) :
  A340737 (2 * k) + A340737 (2 * k - 2) + (k - 1) * A340737 (2 * k - 3) = (k + 1) * A340737 (2 * k - 1) := by
  have h_eq : 2 * k = (2 * k - 3) + 3 := by omega
  nth_rw 1 [h_eq]; rw [A340737]
  have h_mod : ((2 * k - 3) + 3) % 2 = 0 := by omega
  rw [h_mod]; dsimp
  have e1 : ((2 * k - 3) + 3 + 2) / 2 = k + 1 := by omega
  have e2 : ((2 * k - 3) + 3 - 2) / 2 = k - 1 := by omega
  rw [e1, e2]
  have h1 : A340737 (2 * k - 3 + 2) = A340737 (2 * k - 1) := by congr 1; omega
  have h2 : A340737 (2 * k - 3 + 3 - 2) = A340737 (2 * k - 2) := by congr 1; omega
  have h3 : A340737 (2 * k - 3 + 3 - 3) = A340737 (2 * k - 3) := by congr 1
  rw [h1, h2, h3]
  omega
