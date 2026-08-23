import FormalConjectures.Util.ProblemImports

open Nat

set_option linter.unusedVariables false
set_option maxHeartbeats 80000000
set_option maxRecDepth 40000

def isSqAux : ℕ → ℕ → Bool
  | n, 0 => n == 0
  | n, k + 1 => ((k + 1) * (k + 1) == n) || isSqAux n k

def checkValid (n x y z : ℕ) : Bool :=
  let s := x * x + y * y + z * z
  decide (s ≤ n) && isSqAux (n - s) (n - s) && decide (z * z ≤ n - s) &&
    decide (0 < y) && decide (y ≥ z) &&
    isSqAux ((x + 4 * y + 4 * z) * (x + 4 * y + 4 * z) +
             (9 * x + 3 * y + 3 * z) * (9 * x + 3 * y + 3 * z))
            (10 * x + 7 * y + 7 * z)

def sumZ : ℕ → ℕ → ℕ → ℕ → ℕ
  | n, x, y, 0 => bif checkValid n x y 0 then 1 else 0
  | n, x, y, k + 1 => (bif checkValid n x y (k + 1) then 1 else 0) + sumZ n x y k

def sumY : ℕ → ℕ → ℕ → ℕ
  | n, x, 0 => 0
  | n, x, y + 1 => sumZ n x (y + 1) (y + 1) + sumY n x y

def sumX : ℕ → ℕ → ℕ
  | n, 0 => sumY n 0 n
  | n, x + 1 => sumY n (x + 1) n + sumX n x

def countB (n b : ℕ) : ℕ := sumX n b

theorem c191 : countB 191 14 = 1 := by rfl
theorem c311 : countB 311 18 = 1 := by rfl
theorem c671 : countB 671 26 = 1 := by rfl
