P = 1093**1093
M = 1194648

def dc_mod(a, b):
    if a + 1 == b:
        k = a + 1
        return (k % P, 1 if k % 2 == 0 else P - 1)
    mid = (a + b) // 2
    x1, z1 = dc_mod(a, mid)
    x2, z2 = dc_mod(mid, b)
    x = (x2 * x1) % P
    z = (x2 * z1 + z2 * x1) % P
    return (x, z)

x, z = dc_mod(0, M)

with open('/workspace/leanproject/Submission/Spec.lean', 'w') as f:
    f.write('''import FormalConjectures.Util.ProblemImports

open Nat Int Finset

/-- The auxiliary integer sequence $F(n) = n! \sum_{k=2}^n \frac{(-1)^k}{k}$, corresponding to OEIS A024168. -/
def F_aux (n : ℕ) : ℤ :=
  if n < 2 then 0 else
  Finset.sum (Icc 2 n) $ fun k : ℕ =>
    let n_fact : ℤ := n.factorial
    let k_int : ℤ := k
    -- Term is $\frac{n!}{k} (-1)^{k}$.
    let quotient : ℤ := n_fact / k_int
    quotient * (if k % 2 = 0 then 1 else -1)

/--
A335023: Ratios of consecutive terms of A334958.
$$a(n) = \frac{A334958(n+1)}{A334958(n)}$$
where $A334958(m) = \gcd(F(m+1), F(m))$.
-/
def a (n : ℕ) : ℕ :=
  let A334958 (m : ℕ) : ℕ := Int.gcd (F_aux (m + 1)) (F_aux m)

  let g_n := A334958 n
  let g_n_plus_1 := A334958 (n + 1)

  -- A334958(n) is non-zero for $n \ge 1$.
  if g_n = 0 then 0 else g_n_plus_1 / g_n

theorem oeis_335023_conjecture_0 (n : ℕ) (h : n > 0) :
  a n = 1 ↔ Nat.Prime (n + 1) := by sorry

def P : ℕ := 1093^1093

def dc_mod (fuel a b : ℕ) : ℕ × ℕ :=
  match fuel with
  | 0 => (1, 0)
  | fuel' + 1 =>
    if a + 1 = b then
      let k := a + 1
      let X := k % P
      let Z := if k % 2 == 0 then 1 else P - 1
      (X, Z)
    else if a + 1 < b then
      let mid := (a + b) / 2
      let (X1, Z1) := dc_mod fuel' a mid
      let (X2, Z2) := dc_mod fuel' mid b
      let X := (X2 * X1) % P
      let Z := (X2 * Z1 + Z2 * X1) % P
      (X, Z)
    else
      (1, 0)

set_option exponentiation.threshold 2000
set_option maxHeartbeats 2000000000

''')
    f.write(f'theorem main_eval : dc_mod 22 0 {M} = ({x}, {z}) := by decide\n')
    f.write('''
theorem oeis_335023_conjecture_0.disproof : ¬ (type_of% @oeis_335023_conjecture_0) := by
  sorry
''')

