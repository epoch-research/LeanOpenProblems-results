import FormalConjectures.Util.ProblemImports

open Nat BigOperators

def A352656_num_prod (n : ℕ) : ℕ :=
  (Finset.Icc 1 n).prod fun i =>
    (3 * n + i - 1).factorial * (i - 1).factorial

def A352656_den_prod (n : ℕ) : ℕ :=
  (Finset.Icc 1 n).prod fun i =>
    (2 * n + i - 1).factorial * (n + i - 1).factorial

def A352656 (n : ℕ) : ℕ :=
  if n = 0 then
    1
  else
    A352656_num_prod n / A352656_den_prod n

def superfactorial (n : ℕ) : ℕ :=
  (Finset.range n).prod fun k => k.factorial

def F (a b c : ℕ) : ℕ :=
  let num := superfactorial a * superfactorial b * superfactorial c * superfactorial (a + b + c)
  let den := superfactorial (a + b) * superfactorial (a + c) * superfactorial (b + c)
  num / den

theorem oeis_A352656_conjecture_1 (p : ℕ) (hp : p.Prime) (r : ℕ) (hr : 0 < r) (a b c : ℕ) :
  (F (a * p ^ r) (b * p ^ r) (c * p ^ r) : ℤ) ≡
  (F (a * p ^ (r - 1)) (b * p ^ (r - 1)) (c * p ^ (r - 1)) : ℤ) ^ p
    [ZMOD (p ^ (4 * r) : ℤ)] :=
sorry

theorem oeis_A352656_conjecture_1.disproof : ¬ (type_of% @oeis_A352656_conjecture_1) :=
by sorry
