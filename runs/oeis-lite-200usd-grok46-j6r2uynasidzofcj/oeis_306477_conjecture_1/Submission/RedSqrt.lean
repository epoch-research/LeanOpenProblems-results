import FormalConjectures.Util.ProblemImports

open Nat

/-- Kernel-reducible integer square root via binary search. -/
def isqrtF (t : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, lo, _ => lo
  | fuel + 1, lo, hi =>
    if hi ≤ lo + 1 then lo
    else
      let mid := lo + (hi - lo) / 2
      if mid * mid ≤ t then isqrtF t fuel mid hi else isqrtF t fuel lo mid

def isqrtR (t : ℕ) : ℕ := isqrtF t 64 0 (t + 1)

example : isqrtR 49 = 7 := rfl
example : isqrtR 48 = 6 := rfl
example : isqrtR 57 = 7 := rfl
example : isqrtR 0 = 0 := rfl
example : isqrtR 1 = 1 := rfl
example : isqrtR 100000000 = 10000 := rfl

def isOddSquareR (t : ℕ) : Bool :=
  let s := isqrtR t
  (s * s == t) && (s % 2 == 1)

example : isOddSquareR 49 = true := rfl
example : isOddSquareR 57 = false := rfl
example : isOddSquareR (8 * 6 + 1) = true := rfl

-- larger
example : isqrtR (8 * 100000000003 + 1) * isqrtR (8 * 100000000003 + 1)
    ≠ 8 * 100000000003 + 1 := by decide
