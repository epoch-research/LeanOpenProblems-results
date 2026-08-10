import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 10000

open Nat

def f0_fast (x M : ℕ) : ℕ :=
  let x2 := x * x % M
  let x4 := x2 * x2 % M
  let x8 := x4 * x4 % M
  x8 * x2 % M

def f1 (x M : ℕ) : ℕ := f0_fast (f0_fast x M) M
def f2 (x M : ℕ) : ℕ := f1 (f1 x M) M
def f3 (x M : ℕ) : ℕ := f2 (f2 x M) M
def f4 (x M : ℕ) : ℕ := f3 (f3 x M) M
def f5 (x M : ℕ) : ℕ := f4 (f4 x M) M
def f6 (x M : ℕ) : ℕ := f5 (f5 x M) M
def f7 (x M : ℕ) : ℕ := f6 (f6 x M) M
def f8 (x M : ℕ) : ℕ := f7 (f7 x M) M
def f9 (x M : ℕ) : ℕ := f8 (f8 x M) M
def f10 (x M : ℕ) : ℕ := f9 (f9 x M) M
def f11 (x M : ℕ) : ℕ := f10 (f10 x M) M
def f12 (x M : ℕ) : ℕ := f11 (f11 x M) M
def f13 (x M : ℕ) : ℕ := f12 (f12 x M) M

abbrev M_val : ℕ := 10 ^ (2 ^ 21) + 1

#eval f13 3 M_val % 10
