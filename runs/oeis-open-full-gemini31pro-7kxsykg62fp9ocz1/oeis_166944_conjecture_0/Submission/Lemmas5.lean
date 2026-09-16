import Submission.Lemmas
import Mathlib

lemma C_add_d (k : ℕ) (hk : 1 ≤ k) : C (k + 1) = C k + d (k + 1) - 1 := by
  have ha : a (k + 1) = C (k + 1) + (k + 1) := a_eq_C_add_n _
  have hak : a k = C k + k := a_eq_C_add_n _
  have hd : d (k + 1) = a (k + 1) - a k := rfl
  have hC_mono : C k ≤ C (k + 1) := C_mono hk
  omega

lemma d_pos (k : ℕ) (hk : 1 ≤ k) : 1 ≤ d (k + 1) := by
  have hd : d (k + 1) = a (k + 1) - a k := rfl
  have hC_mono : C k ≤ C (k + 1) := C_mono hk
  have ha : a (k + 1) = C (k + 1) + (k + 1) := a_eq_C_add_n _
  have hak : a k = C k + k := a_eq_C_add_n _
  omega
