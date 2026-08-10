import FormalConjectures.Util.ProblemImports
open Finset
namespace SK

def T (n k : ℕ) : ℤ := ((n.choose k) ^ 2 * ((n + k).choose k) * ((3 * n + 2 * k).choose n) : ℕ)
def aSeq (n : ℕ) : ℤ := ∑ k ∈ range (n + 1), T n k
def P0 (n : ℤ) : ℤ := n + 1
def P1 (n : ℤ) : ℤ := n + 2
def P2 (n : ℤ) : ℤ := n + 3
def Npol (n k : ℤ) : ℤ := n + k
def Dpol (n k : ℤ) : ℤ := (k-n-2)^2*(k-n-1)^2*(2*k+2*n+1)*(2*k+2*n+3)
def Fpol (n k : ℕ) : ℤ := P0 n * T n k + P1 n * T (n+1) k + P2 n * T (n+2) k
noncomputable def Gq (n k : ℕ) : ℚ := (Npol n k : ℚ) * (T n k : ℚ) / (Dpol n k : ℚ)

lemma T_vanish (m k : ℕ) (h : m < k) : T m k = 0 := by
  unfold T; rw [Nat.choose_eq_zero_of_lt h]; push_cast; ring

lemma CERT2 (n k : ℕ) (hk : k ≤ n) :
    Dpol n k * Dpol n (k+1) * Fpol n k
      = Npol n (k+1) * Dpol n k * T n (k+1) - Npol n k * Dpol n (k+1) * T n k := by
  sorry

lemma Dpol_ne (n k : ℕ) (hk : k ≤ n) : (Dpol n k : ℚ) ≠ 0 := by
  sorry

lemma Gq_zero (n : ℕ) : Gq n 0 = 0 := by
  sorry

lemma star (n : ℕ) :
    Gq n n + (Fpol n n : ℚ) + (Fpol n (n+1) : ℚ) + (Fpol n (n+2) : ℚ) = 0 := by
  sorry

lemma F_eq_dG (n k : ℕ) (hk : k + 1 ≤ n) : Gq n (k+1) - Gq n k = (Fpol n k : ℚ) := by
  have hc := CERT2 n k (by omega)
  have hd1 : (Dpol n k : ℚ) ≠ 0 := Dpol_ne n k (by omega)
  have hd2 : (Dpol n (k+1) : ℚ) ≠ 0 := Dpol_ne n (k+1) (by omega)
  have hcq : (Dpol n k : ℚ) * Dpol n (k+1) * Fpol n k
      = Npol n (k+1) * Dpol n k * T n (k+1) - Npol n k * Dpol n (k+1) * T n k := by exact_mod_cast hc
  rw [Gq, Gq]
  push_cast
  rw [div_sub_div _ _ hd2 hd1, div_eq_iff (mul_ne_zero hd2 hd1)]
  linear_combination -hcq

lemma tele (n : ℕ) : (∑ k ∈ range n, (Fpol n k : ℚ)) = Gq n n := by
  have h : ∑ k ∈ range n, (Fpol n k : ℚ) = ∑ k ∈ range n, (Gq n (k+1) - Gq n k) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_range] at hk
    exact (F_eq_dG n k (by omega)).symm
  rw [h, Finset.sum_range_sub (fun k => Gq n k) n, Gq_zero]
  ring

lemma ha (n : ℕ) : ∑ k ∈ range (n+3), (T n k : ℚ) = (aSeq n : ℚ) := by
  unfold aSeq; push_cast
  rw [show n+3 = (n+1)+1+1 from rfl, Finset.sum_range_succ, Finset.sum_range_succ]
  rw [show ((T n (n+1) : ℤ) : ℚ) = 0 by rw [T_vanish n (n+1) (by omega)]; norm_num,
      show ((T n ((n+1)+1) : ℤ) : ℚ) = 0 by rw [T_vanish n ((n+1)+1) (by omega)]; norm_num]
  ring

lemma ha1 (n : ℕ) : ∑ k ∈ range (n+3), (T (n+1) k : ℚ) = (aSeq (n+1) : ℚ) := by
  unfold aSeq; push_cast
  rw [show n+3 = (n+1+1)+1 from rfl, Finset.sum_range_succ]
  rw [show ((T (n+1) (n+1+1) : ℤ) : ℚ) = 0 by rw [T_vanish (n+1) (n+1+1) (by omega)]; norm_num]
  ring

lemma ha2 (n : ℕ) : ∑ k ∈ range (n+3), (T (n+2) k : ℚ) = (aSeq (n+2) : ℚ) := by
  unfold aSeq; push_cast
  rw [show n+3 = n+2+1 from rfl]

theorem aSeq_rec (n : ℕ) :
    P0 n * aSeq n + P1 n * aSeq (n+1) + P2 n * aSeq (n+2) = 0 := by
  have key : (∑ k ∈ range (n+3), (Fpol n k : ℚ)) = 0 := by
    rw [show n+3 = n+1+1+1 from rfl, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_succ, tele]
    linear_combination star n
  have expand : (∑ k ∈ range (n+3), (Fpol n k : ℚ))
      = (P0 n : ℚ) * aSeq n + (P1 n : ℚ) * aSeq (n+1) + (P2 n : ℚ) * aSeq (n+2) := by
    have : ∀ k, (Fpol n k : ℚ) = (P0 n : ℚ) * (T n k : ℚ) + (P1 n : ℚ) * (T (n+1) k : ℚ)
        + (P2 n : ℚ) * (T (n+2) k : ℚ) := by intro k; unfold Fpol; push_cast; ring
    rw [Finset.sum_congr rfl (fun k _ => this k)]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
        ← Finset.mul_sum, ha n, ha1 n, ha2 n]
  rw [← @Int.cast_inj ℚ]
  push_cast
  rw [← expand, key]

end SK
