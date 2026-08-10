import FormalConjectures.Util.ProblemImports

set_option exponentiation.threshold 30000
set_option maxRecDepth 30000

open Nat ZMod

def pow10_rec (M : ℕ) (steps : ℕ) (acc : ZMod M) : ZMod M :=
  match steps with
  | 0 => acc
  | n + 1 => pow10_rec M n (acc ^ 10)

theorem pow10_rec_eq_acc_pow (M : ℕ) (steps : ℕ) (acc : ZMod M) :
    pow10_rec M steps acc = acc ^ (10 ^ steps) := by
  induction steps generalizing acc with
  | zero => simp [pow10_rec]
  | succ n ih =>
    rw [pow10_rec]
    rw [ih]
    rw [← pow_mul]
    congr 1
    exact (pow_succ' 10 n).symm

theorem lemma_13 : (3 : ZMod (10 ^ (2 ^ 13) + 1)) ^ (10 ^ (2 ^ 13)) ≠ 1 := by
  have h : (3 : ZMod (10 ^ (2 ^ 13) + 1)) ^ (10 ^ (2 ^ 13)) = pow10_rec (10 ^ (2 ^ 13) + 1) 8192 3 := by
    rw [pow10_rec_eq_acc_pow]
    congr 1
    decide
  rw [h]
  decide
