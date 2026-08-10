import FormalConjectures.Util.ProblemImports

open Nat

def digits_fast_aux : ℕ → ℕ → List ℕ
  | 0, _ => []
  | fuel + 1, n =>
    if n = 0 then []
    else (n % 2) :: digits_fast_aux fuel (n / 2)

def A030101_fast (n : ℕ) : ℕ :=
  Nat.ofDigits 2 (List.reverse (digits_fast_aux n n))

def a_aux : ℕ → ℕ × ℕ
  | 0 => (0, 1)
  | n + 1 =>
    let (x, y) := a_aux n
    (y, x.xor (A030101_fast y) + 1)

def a_step (acc : ℕ × ℕ) : ℕ × ℕ :=
  (acc.2, acc.1.xor (A030101_fast acc.2) + 1)

def a_aux_iter : ℕ → ℕ × ℕ → ℕ × ℕ
  | 0, acc => acc
  | n + 1, acc => a_aux_iter n (a_step acc)

theorem a_aux_iter_step (n : ℕ) (acc : ℕ × ℕ) :
  a_aux_iter n (a_step acc) = a_step (a_aux_iter n acc) := by
  induction n generalizing acc with
  | zero => rfl
  | succ n ih =>
    dsimp [a_aux_iter]
    rw [ih (a_step acc)]

theorem a_aux_eq_a_aux_iter (n : ℕ) : a_aux n = a_aux_iter n (0, 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    dsimp [a_aux]
    rw [ih]
    exact (a_aux_iter_step n (0, 1)).symm

#eval (a_aux_iter 19738 (0, 1)).1

