import FormalConjectures.Util.ProblemImports

open Nat Finset Polynomial

def A103885 (n : ℕ) : ℕ :=
  if n = 0 then 1 else 0

noncomputable def A103885_subsequence_real (m n : ℕ) : ℝ :=
  (A103885 (m * n) : ℝ)

lemma subsequence_real_succ (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) :
    A103885_subsequence_real m (n + 1) = 0 := by
  unfold A103885_subsequence_real A103885
  have h1 : m * (n + 1) ≠ 0 := by
    apply Nat.ne_of_gt
    calc
      0 < m * 2 := by omega
      _ ≤ m * (n + 1) := by gcongr; omega
  split_ifs with h
  · contradiction
  · push_cast; rfl
