import FormalConjectures.Util.ProblemImports
import Submission.Spec
open Nat Finset

def p (i : ℕ) : ℕ := Nat.nth Nat.Prime i

def S (n : ℕ) : ℕ := (range n).sum p

def a_eval (n : ℕ) : ℕ :=
  (range n).sum (fun i => S n % p i)

-- Since Nat.nth is noncomputable, we cannot #eval a_eval directly.
-- Can we prove a 1 = 0?
theorem a_1_eq_0 : a 1 = 0 := by
  -- a 1 = (range 1).sum (fun i => S_1 % (Nat.nth Nat.Prime i))
  -- = S_1 % (Nat.nth Nat.Prime 0)
  -- S_1 = (range 1).sum (fun k => Nat.nth Nat.Prime k) = Nat.nth Nat.Prime 0
  -- So a 1 = Nat.nth Nat.Prime 0 % Nat.nth Nat.Prime 0 = 0
  sorry
