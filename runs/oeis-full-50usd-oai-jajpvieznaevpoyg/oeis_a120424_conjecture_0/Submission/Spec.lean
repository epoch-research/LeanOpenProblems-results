import FormalConjectures.Util.ProblemImports

/--
A120424: Having specified two initial terms, the "Half-Fibonacci" sequence proceeds like the
Fibonacci sequence, except that the terms are halved before being added if they are even.
$$a(n) = (\text{if } a(n-1) \text{ is odd then } a(n-1) \text{ else } a(n-1)/2) + (\text{if } a(n-2) \text{ is odd then } a(n-2) \text{ else } a(n-2)/2)$$
with $a(0)=1$ and $a(1)=3$.
-/
def A120424 : ℕ → ℕ
| 0     => 1
| 1     => 3
| n + 2 =>
  let f (x : ℕ) : ℕ := if x % 2 = 0 then x / 2 else x
  f (A120424 (n + 1)) + f (A120424 n)

/--
Conjecture A120424: For the Half-Fibonacci sequence, the natural density of even terms is $1/2$,
and there are infinitely many consecutive pairs that differ by 1.
The "infinitely increasing" part of the OEIS comment is deliberately ignored as the sequence clearly is not always increasing.
Half of the terms are even in the limit. There are infinitely many consecutive pairs that differ by 1.
-/
theorem oeis_a120424_conjecture_0 :
  -- Half of the terms are even in the limit (Asymptotic Density = 1/2)
  ({n : ℕ | A120424 n % 2 = 0}).HasDensity (1/2 : ℝ) ∧
  -- There are infinitely many consecutive pairs that differ by 1.
  Set.Infinite { n : ℕ | A120424 (n + 1) = A120424 n + 1 ∨ A120424 n = A120424 (n + 1) + 1 } := by
  sorry
