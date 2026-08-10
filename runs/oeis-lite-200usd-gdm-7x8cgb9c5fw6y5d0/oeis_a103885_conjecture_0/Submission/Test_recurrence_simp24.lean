import FormalConjectures.Util.ProblemImports

open Nat Finset Polynomial

def A103885 (n : ℕ) : ℕ :=
  if n = 0 then 1 else 0

noncomputable def A103885_subsequence_real (m n : ℕ) : ℝ :=
  (A103885 (m * n) : ℝ)

private def product_indices (m : ℕ) : Finset ℕ :=
  Finset.Ioc 0 (2 * m)

noncomputable def prod_factor_minus (m n : ℕ) : ℝ :=
  (product_indices m).prod fun k =>
    ((2 * m * n : ℝ) - (k : ℝ))

lemma subsequence_real_self (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) :
    A103885_subsequence_real m n = 0 := by
  unfold A103885_subsequence_real A103885
  have h1 : m * n ≠ 0 := by
    apply Nat.ne_of_gt
    nlinarith
  split_ifs with h
  · contradiction
  · push_cast; rfl

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

theorem recurrence_simp (m : ℕ) (hm : 1 ≤ m) (P Q : Polynomial ℝ)
    (h_prod_minus : prod_factor_minus m 1 = 0) :
    ∀ (n : ℕ) (hn : 1 ≤ n),
      (prod_factor_plus m n * P.eval (n : ℝ)) * (A103885_subsequence_real m (n + 1)) +
      ((-1 : ℝ) ^ m * prod_factor_minus m n * P.eval (-(n : ℝ))) * (A103885_subsequence_real m (n - 1)) =
      (Q.eval ((n : ℝ)^2)) * (A103885_subsequence_real m n) := by
  intro n hn
  rw [subsequence_real_succ m n hm hn]
  rw [subsequence_real_self m n hm hn]
  rw [subsequence_real_pred m n hm hn]
  simp
  split_ifs with h_cond
  · subst h_cond
    rw [h_prod_minus]
    ring
  · rfl
