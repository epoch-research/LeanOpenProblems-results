import FormalConjectures.Util.ProblemImports
set_option maxRecDepth 100000
open Nat
def digits_fast_aux : ℕ → ℕ → List ℕ
  | 0, _ => []
  | fuel + 1, n =>
    if n = 0 then []
    else (n % 2) :: digits_fast_aux fuel (n / 2)
def A030101_fast (n : ℕ) : ℕ :=
  Nat.ofDigits 2 (List.reverse (digits_fast_aux n n))
def a_step (acc : ℕ × ℕ) : ℕ × ℕ :=
  (acc.2, acc.1.xor (A030101_fast acc.2) + 1)
def a_aux_iter : ℕ → ℕ × ℕ → ℕ × ℕ
  | 0, acc => acc
  | n + 1, acc => a_aux_iter n (a_step acc)
theorem test_decide : (a_aux_iter 13882 (0, 1)).1 = 12060 := by
  rfl

