import FormalConjectures.Util.ProblemImports

open Nat

def check (n x y z : ℕ) : Bool :=
  let s := x * x + y * y + z * z
  decide (s ≤ n) &&
    let r := n - s
    let w := r.sqrt
    decide (w * w = r) && decide (z ≤ w) && decide (0 < y) && decide (y ≥ z) &&
    let E := (x + 4 * y + 4 * z) * (x + 4 * y + 4 * z) +
             (9 * x + 3 * y + 3 * z) * (9 * x + 3 * y + 3 * z)
    decide (E.sqrt * E.sqrt = E)

def sumZ : ℕ → ℕ → ℕ → ℕ → ℕ
  | n, x, y, 0 => bif check n x y 0 then 1 else 0
  | n, x, y, Nat.succ k => (bif check n x y (k+1) then 1 else 0) + sumZ n x y k

def sumY : ℕ → ℕ → ℕ → ℕ
  | n, x, 0 => 0
  | n, x, Nat.succ y => sumZ n x (y+1) (y+1) + sumY n x y

def sumX : ℕ → ℕ → ℕ
  | n, 0 => sumY n 0 n
  | n, Nat.succ x => sumY n (x+1) n + sumX n x

def countF (n b : ℕ) : ℕ := sumX n b

set_option maxHeartbeats 20000000
theorem c1 : countF 1 1 = 1 := by rfl
theorem c7 : countF 7 2 = 1 := by rfl
theorem c23 : countF 23 4 = 1 := by rfl
