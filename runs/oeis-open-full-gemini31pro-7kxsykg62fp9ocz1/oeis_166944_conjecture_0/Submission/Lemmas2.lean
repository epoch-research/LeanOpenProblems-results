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

lemma d_sum (n : ℕ) (hn : 2 ≤ n) : C n = 1 + ∑ k ∈ Finset.Ico 2 (n + 1), (d k - 1) := by
  induction n, hn using Nat.le_induction with
  | base =>
    have hd2 : d 2 = 2 := rfl
    have hC2 : C 2 = 2 := rfl
    rw [hC2]
    have : Finset.Ico 2 (2 + 1) = {2} := rfl
    rw [this, Finset.sum_singleton, hd2]
  | succ k hk ih =>
    rw [C_add_d k (by omega)]
    rw [ih]
    have h_ico : Finset.Ico 2 (k + 1 + 1) = Finset.Ico 2 (k + 1) ∪ {k + 1} := by
      ext x
      simp only [Finset.mem_Ico, Finset.mem_union, Finset.mem_singleton]
      omega
    rw [h_ico]
    rw [Finset.sum_union]
    · rw [Finset.sum_singleton]
      have : 1 ≤ d (k + 1) := d_pos k (by omega)
      omega
    · simp [Finset.disjoint_singleton_right]
