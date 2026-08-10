import FormalConjectures.Util.ProblemImports

open Nat Finset Polynomial

def A103885 (n : ℕ) : ℕ :=
  if n = 0 then 1 else 0

noncomputable def A103885_subsequence_real (m n : ℕ) : ℝ :=
  (A103885 (m * n) : ℝ)

lemma subsequence_real_eq (m n : ℕ) (hm : 1 ≤ m) :
    A103885_subsequence_real m n = if n = 0 then 1 else 0 := by
  unfold A103885_subsequence_real A103885
  split_ifs with h1 h2 h3
  · push_cast; rfl
  · have : m * n = 0 := h1
    have h_or := Nat.mul_eq_zero.mp this
    rcases h_or with h | h
    · omega
    · contradiction
  · subst h3
    simp at h1
  · push_cast; rfl
