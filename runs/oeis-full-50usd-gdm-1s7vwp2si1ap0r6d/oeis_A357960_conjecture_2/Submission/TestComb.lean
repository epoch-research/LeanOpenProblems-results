import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import FormalConjectures.Util.ProblemImports

open Nat Finset
open scoped BigOperators

def a (n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    (∑ k ∈ range n, (Nat.choose (n - 1) k) ^ 2 * (Nat.choose (n - 1 + k) k) ^ 2) ^ 5 *
    (∑ k ∈ range (n + 1), (Nat.choose n k) ^ 2 * (Nat.choose (n + k) k)) ^ 6

theorem val_3_2 : a (3^2) ≡ a (3^(2-1)) [MOD 3^(3*2 + 3)] := by rfl













