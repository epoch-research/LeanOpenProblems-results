import FormalConjectures.Util.ProblemImports

open Nat Set List
open scoped Classical

/--
A083753: Smallest palindromic number with exactly $n$ divisors, or 0 if no such number exists.
-/
noncomputable def a (n : ℕ) : ℕ :=
  let is_palindrome (m : ℕ) : Prop := Nat.digits 10 m = (Nat.digits 10 m).reverse

  -- The number of divisors of m.
  let tau (m : ℕ) : ℕ := Finset.card (Nat.divisors m)

  -- The set of positive natural numbers $m$ that are palindromes and have n divisors.
  let S : Set ℕ := {m : ℕ | m > 0 ∧ is_palindrome m ∧ tau m = n}

  -- Since Nat.sInf returns the smallest element of a set if non-empty, and 0 if empty,
  -- we can use an if statement to formally satisfy the "or 0 if no such number exists" clause.
  if h : S.Nonempty then
    sInf S
  else
    0

/--
A conjecture often cited in connection with A083753:
There are no palindromic numbers greater than 1 which are the fifth or higher power of a natural number.
This implies that a(n)=0 for certain values of n (like 7, 11, 13, 17, 19, 23, 29, 31, 37, 41)
because the only numbers with these prime numbers of divisors are high perfect powers.
-/
theorem oeis_83753_conjecture_0 :
  ∀ (m k : ℕ),
    m > 1 ∧
    (Nat.digits 10 m = (Nat.digits 10 m).reverse) ∧
    k ≥ 5 ∧
    (∃ x : ℕ, m = x ^ k)
    →
    False
:= by
  rintro m k ⟨hm, hpal, hk, x, hx⟩
  -- After reduction, the goal `False` is equivalent to asserting that the base-10
  -- palindrome `m = x ^ k` (with `m > 1`, hence `x ≥ 2`, and `k ≥ 5`) cannot exist.
  -- This is exactly **Simmons' conjecture (1972)**: no base-10 palindrome greater
  -- than 1 is a perfect `k`-th power for `k ≥ 5`.  (Guy, *Unsolved Problems in
  -- Number Theory*.)
  --
  -- It is an OPEN problem.  It is *true* as far as is known: verified free of
  -- counterexamples for all perfect powers below 10^38 (all exponents), below 10^66
  -- for k = 5, below 10^79 for k = 6, and among structured/sparse bases.  The total
  -- heuristic expected count of palindromic k-th powers (k ≥ 5) over all sizes is
  -- only ≈ 1, and it is entirely concentrated in the (checked, empty) small range.
  --
  -- No elementary/formalizable proof is available:
  --  * No modular obstruction can exist.  Palindromes equidistribute modulo every N,
  --    so they meet every k-th-power residue class.  For k coprime to 10 (e.g. k = 7,
  --    which is in range), x ↦ x^k is a bijection modulo any N with gcd(k, φ N) = 1,
  --    so 7th powers already occupy *all* residues — no modulus separates them from
  --    palindromes.
  --  * Divisibility by 11 constrains only *even-length* palindromes; odd-length
  --    palindromic powers carry no forced divisor.
  --  * The (10^n+1)^k families give palindromes exactly for k ≤ 4 (all binomials < 10,
  --    no carries); for k ≥ 5, C(5,2)=10 forces carries — this rules out those
  --    families but not sporadic coincidences.
  --  * Counting gives density → 0, not emptiness; no effective digit bound is known.
  --  * Mathlib provides no relevant machinery (no Catalan/Mihailescu, Baker, or
  --    S-unit theory).
  --
  -- Resolving it requires ineffective/transcendental Diophantine methods beyond
  -- current formalization. The statement below is left with `sorry`.
  sorry
