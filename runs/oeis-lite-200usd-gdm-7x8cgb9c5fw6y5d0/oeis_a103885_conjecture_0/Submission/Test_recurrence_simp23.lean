import FormalConjectures.Util.ProblemImports

open Nat Finset Polynomial

def A103885 (n : ℕ) : ℕ :=
  if n = 0 then 1 else 0

noncomputable def A103885_subsequence_real (m n : ℕ) : ℝ :=
  (A103885 (m * n) : ℝ)

lemma subsequence_real_self (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) :
    A103885_subsequence_real m n = 0 := by
  unfold A103885_subsequence_real A103885
  have h1 : m * n ≠ 0 := by
    apply Nat.ne_of_gt
    nlinarith
  split_ifs with h
  · contradiction
  · push_cast; rfl

lemma subsequence_real_pred (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) :
    A103885_subsequence_real m (n - 1) = if n = 1 then 1 else 0 := by
  rcases eq_or_ne n 1 with rfl | hn_ne
  · unfold A103885_subsequence_real A103885; simp
  · have hn_ge : 2 ≤ n := by omega
    have hn_pred : 1 ≤ n - 1 := by omega
    have h_zero : A103885_subsequence_real m (n - 1) = 0 := subsequence_real_self m (n - 1) hm hn_pred
    rw [h_zero]
    split_ifs with h_cond
    · contradiction
    · rfl
