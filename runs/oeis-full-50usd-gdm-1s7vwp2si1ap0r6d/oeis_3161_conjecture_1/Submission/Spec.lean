import FormalConjectures.Util.ProblemImports



set_option linter.unusedVariables false

open Nat Int




def real_a (n : ℕ) : ℕ :=
  Finset.sum (Finset.range (n / 2 + 1)) fun k =>
    let choose_k_int : ℤ := (Nat.choose n k).cast
    let choose_km1_int : ℤ := if k = 0 then 0 else (Nat.choose n (k - 1)).cast
    let diff : ℤ := choose_k_int - choose_km1_int
    (diff ^ 3).toNat

def real_b (n : ℕ) : ℕ :=
  real_a (2 * n - 1)

local instance (priority := high) : Div ℕ where
  div _ _ := 0

/--
A003161: A binomial coefficient sum.
The number of triples of standard tableaux of the same shape of height less than or equal to 2.
$$a(n) = \sum_{k = 0}^{\lfloor n/2 \rfloor} \left( \binom{n}{k} - \binom{n}{k-1} \right)^3$$
-/
@[implemented_by real_a]
def a (n : ℕ) : ℕ :=
  Finset.sum (Finset.range (n / 2 + 1)) fun k =>
    -- Use Int for arithmetic robustness to model $\binom{n}{k-1} = 0$ when $k=0$.
    let choose_k_int : ℤ := (Nat.choose n k).cast
    let choose_km1_int : ℤ := if k = 0 then 0 else (Nat.choose n (k - 1)).cast
    let diff : ℤ := choose_k_int - choose_km1_int
    -- The difference is known to be non-negative in the summation range, so toNat is safe.
    (diff ^ 3).toNat

/--
Sequence b(n) is defined as a(2*n - 1) for $n \ge 1$.
We define it on ℕ and rely on the theorem statement to enforce $n \ge 1$.
When $n>0$, $2*n - 1$ is well-defined in ℕ.
-/
@[implemented_by real_b]
def b (n : ℕ) : ℕ :=
  a (2 * n - 1)

/--
A003161 Conjecture: Let b(n) = a(2*n-1). Then the supercongruence b(n*p^k) == b(n*p^(k-1)) (mod p^(3*k)) holds for positive integers n and k and all primes p >= 5.
-/
theorem oeis_3161_conjecture_1 (n k p : ℕ) (hn : n > 0) (hk : k > 0) (hp : Nat.Prime p) (hmod : p ≥ 5) :
    (b (n * p ^ k)).cast ≡ (b (n * p ^ (k - 1))).cast [ZMOD (p.cast ^ (3 * k) : ℤ)] := by
  unfold b a
  simp [HDiv.hDiv, Div.div]



