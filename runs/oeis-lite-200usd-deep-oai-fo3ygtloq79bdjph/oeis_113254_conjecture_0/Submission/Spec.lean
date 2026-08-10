import FormalConjectures.Util.ProblemImports

open Nat Int

def a (n : ℕ) : ℤ :=
  match n with
  | 0 => -1
  | 1 => 4
  | 2 => 176
  | 3 => 3136
  | n' + 4 => -4 * a (n' + 3) + 256 * a (n' + 1) + 4096 * a n'

def d : ℕ → ℤ
  | 0 => 1
  | 1 => 7
  | n + 2 => - d (n+1) - 4 * d n

def e : ℕ → ℤ
  | 0 => 1
  | 1 => -11
  | n + 2 => -7 * e (n+1) - 16 * e n

@[simp] lemma d_zero : d 0 = 1 := rfl
@[simp] lemma d_one : d 1 = 7 := rfl
@[simp] lemma d_add_two (n : ℕ) : d (n+2) = - d (n+1) - 4 * d n := rfl
@[simp] lemma e_zero : e 0 = 1 := rfl
@[simp] lemma e_one : e 1 = -11 := rfl
@[simp] lemma e_add_two (n : ℕ) : e (n+2) = -7 * e (n+1) - 16 * e n := rfl

lemma a_add_four (n : ℕ) : a (n+4) = -4 * a (n+3) + 256 * a (n+1) + 4096 * a n := by
  rfl

lemma de_inv (n : ℕ) :
    60 * e n = 11 * d n^2 + 14 * d n * d (n+1) - d (n+1)^2 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      match n with
      | 0 => norm_num [d, e]
      | 1 => norm_num [d, e]
      | k+2 =>
          have hk := ih k (by omega)
          have hk1 := ih (k+1) (by omega)
          rw [show k+1+1 = k+2 by omega] at hk1
          rw [d_add_two] at hk1
          rw [show k+2+1 = k+3 by omega]
          rw [show k+3 = (k+1)+2 by omega, d_add_two]
          rw [show k+2 = k+0+2 by omega, d_add_two]
          rw [show k+1+1 = k+0+2 by omega, d_add_two]

          rw [e_add_two]
          ring_nf at hk hk1 ⊢
          nlinarith [hk, hk1]

lemma de_id1 (n : ℕ) : e (n+2) = d (n+1)^2 - 4 * d n^2 + 16 * e n := by
  have h0 := de_inv n
  have h1 := de_inv (n+1)
  rw [show n+1+1 = n+2 by omega] at h1
  rw [d_add_two] at h1
  rw [e_add_two]
  ring_nf at h0 h1 ⊢
  nlinarith [h0, h1]

lemma de_id2 (n : ℕ) : d (n+2)^2 = e (n+2) - 4 * e (n+1) + 16 * d n^2 := by
  have h0 := de_inv n
  have h1 := de_inv (n+1)
  rw [show n+1+1 = n+2 by omega] at h1
  rw [d_add_two] at h1
  rw [d_add_two]
  rw [e_add_two]
  ring_nf at h0 h1 ⊢
  nlinarith [h0, h1]

lemma a_even_odd (n : ℕ) :
    a (2*n) = - (16:ℤ)^n * e n ∧
    a (2*n+1) = 4 * (16:ℤ)^n * d n^2 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    match n with
    | 0 =>
        norm_num [a, d, e]
    | 1 =>
        norm_num [a, d, e]
    | k+2 =>
        have hk := ih k (by omega)
        have hk1 := ih (k+1) (by omega)
        rcases hk with ⟨hke, hko⟩
        rcases hk1 with ⟨hk1e, hk1o⟩
        have id1 := de_id1 k
        have id2 := de_id2 k
        constructor
        · rw [show 2*(k+2) = 2*k+4 by omega]
          rw [a_add_four]
          rw [show 2*k+3 = 2*(k+1)+1 by omega]
          rw [show 2*k+1 = 2*k+1 by rfl]
          rw [show 2*k = 2*k by rfl]
          rw [hk1o, hko, hke]
          rw [show (16:ℤ)^(k+2) = 16^k * 256 by ring]
          rw [id1]
          ring
        · rw [show 2*(k+2)+1 = 2*k+5 by omega]
          rw [show 2*k+5 = (2*k+1)+4 by omega]
          rw [a_add_four]
          rw [show 2*k+4 = 2*(k+2) by omega]
          rw [show 2*k+2 = 2*(k+1) by omega]
          rw [show 2*k+1 = 2*k+1 by rfl]
          have even_k2 : a (2*(k+2)) = - (16:ℤ)^(k+2) * e (k+2) := by
            rw [show 2*(k+2) = 2*k+4 by omega]
            rw [a_add_four]
            rw [show 2*k+3 = 2*(k+1)+1 by omega]
            rw [hk1o, hko, hke]
            rw [show (16:ℤ)^(k+2) = 16^k * 256 by ring]
            rw [id1]
            ring
          rw [even_k2, hk1e, hko]
          rw [show (16:ℤ)^(k+2) = 16^k * 256 by ring]
          rw [id2]
          ring


theorem oeis_113254_conjecture_0 : ∀ n : ℕ, IsSquare (a (2 * n + 1)) := by
  intro n
  refine ⟨2 * (4:ℤ)^n * d n, ?_⟩
  rw [(a_even_odd n).2]
  have hpow : (4:ℤ)^n * 4^n = 16^n := by
    rw [← mul_pow]
    norm_num
  rw [← hpow]
  ring
