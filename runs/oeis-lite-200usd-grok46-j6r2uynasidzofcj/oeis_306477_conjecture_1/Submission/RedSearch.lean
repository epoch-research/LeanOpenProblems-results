import FormalConjectures.Util.ProblemImports

open Nat

def isqrtF (t : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, lo, _ => lo
  | fuel + 1, lo, hi =>
    if hi ≤ lo + 1 then lo
    else
      let mid := lo + (hi - lo) / 2
      if mid * mid ≤ t then isqrtF t fuel mid hi else isqrtF t fuel lo mid

def isqrtR (t : ℕ) : ℕ := isqrtF t 80 0 (t + 1)

def isTriR (m : ℕ) : Bool :=
  let t := 8 * m + 1
  let s := isqrtR t
  (s * s == t) && (s % 2 == 1)

/-- Count representations with x<X, y<Y, z<Z (w determined by triangular test). -/
def countRep (n X Y Z : ℕ) : ℕ :=
  Id.run do
    let mut c := 0
    for z in [0:Z] do
      let S := (z + 7).choose 8
      if S < n then
        for y in [0:Y] do
          let R := (y + 5).choose 6
          if S + R < n then
            for x in [0:X] do
              let Q := (x + 3).choose 4
              if S + R + Q < n && isTriR (n - S - R - Q) then
                c := c + 1
    return c

-- Small checks
example : isTriR 1 = true := rfl
example : isTriR 2 = false := rfl
example : isTriR 6 = true := rfl

-- countRep for n=10 with generous bounds. 10=T(3)+0+0+0 and maybe more
#eval countRep 10 10 10 10

set_option maxHeartbeats 5000000
-- Does decide work on Id.run loops? Previous notes said NO.
-- Try a recursive version instead.

def countX (n rem : ℕ) : ℕ → ℕ
  | 0 => if isTriR rem then 1 else 0
  | x + 1 =>
      let q := (x + 1 + 3).choose 4
      let here := if q ≤ rem && isTriR (rem - q) then 1 else 0
      here + countX n rem x

def countY (n rem : ℕ) : ℕ → ℕ
  | 0 => countX n rem 20
  | y + 1 =>
      let r := (y + 1 + 5).choose 6
      let here := if r ≤ rem then countX n (rem - r) 20 else 0
      here + countY n rem y

def countZ (n : ℕ) : ℕ → ℕ
  | 0 => countY n n 10
  | z + 1 =>
      let s := (z + 1 + 7).choose 8
      let here := if s ≤ n then countY n (n - s) 10 else 0
      here + countZ n z

example : countX 10 10 8 > 0 := by decide
example : countZ 10 5 > 0 := by decide
example : countZ 2 5 > 0 := by decide
example : countZ 7 5 > 0 := by decide
