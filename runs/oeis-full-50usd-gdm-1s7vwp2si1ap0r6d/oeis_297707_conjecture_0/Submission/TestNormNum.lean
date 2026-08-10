import FormalConjectures.Util.ProblemImports

open Nat Finset BigOperators

def f_tuple (n k : ℕ) : ℕ :=
  if 0 < k then
    let max_j : ℕ := (n - 1) / k
    Finset.prod (range (max_j + 1)) fun j => n - j * k
  else
    1

def bin_pow {M : Type*} [Monoid M] (x : M) : ℕ → ℕ → M
  | 0, _ => 1
  | _ + 1, 0 => 1
  | f + 1, n + 1 =>
    let y := bin_pow x f ((n + 1) / 2)
    if (n + 1) % 2 = 0 then
      y * y
    else
      x * (y * y)

theorem bin_pow_eq_pow {M : Type*} [Monoid M] (x : M) (f n : ℕ) (h : n < 2 ^ f) : bin_pow x f n = x ^ n := by
  induction' f with f ih generalizing n
  · simp only [pow_zero] at h
    have : n = 0 := by omega
    subst this
    rw [pow_zero]
    unfold bin_pow
    rfl
  · cases n with
    | zero =>
      rw [pow_zero]
      unfold bin_pow
      rfl
    | succ k =>
      dsimp [bin_pow]
      have h_div : (k + 1) / 2 < 2 ^ f := by
        have h_pow : 2 ^ (f + 1) = 2 ^ f * 2 := by ring
        rw [h_pow] at h
        have h_comm : 2 ^ f * 2 = 2 * 2 ^ f := by ring
        rw [h_comm] at h
        exact Nat.div_lt_of_lt_mul h
      rw [ih ((k + 1) / 2) h_div]
      by_cases he : (k + 1) % 2 = 0
      · rw [if_pos he]
        rw [← pow_add]
        congr 1
        omega
      · rw [if_neg he]
        rw [← pow_add]
        rw [_root_.pow_succ']
        congr 1
        have h_mod : (k + 1) % 2 = 1 := by omega
        have h_div_add := Nat.div_add_mod (k + 1) 2
        generalize h_x : (k + 1) / 2 = x at h_div_add ⊢
        generalize h_y : (k + 1) % 2 = y at h_div_add h_mod ⊢
        clear f ih h_div h h_x h_y
        omega

