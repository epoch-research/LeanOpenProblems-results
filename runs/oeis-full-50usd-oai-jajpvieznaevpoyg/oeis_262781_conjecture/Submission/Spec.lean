import FormalConjectures.Util.ProblemImports

open Nat
open scoped Nat.Prime

/--
A262781: Number of ordered ways to write $n$ as $x^2 + \phi(y^2) + \phi(z^2)$
($x \ge 0$ and $0 < y \le z$) with $y$ or $z$ prime, where $\phi(\cdot)$ is Euler's totient function.
-/
def A262781 (n : ℕ) : ℕ :=
  -- Define the cartesian product of search ranges for (x, y, z).
  -- $x$ is bounded by $\sqrt{n}$. $y, z$ are conservatively bounded by $n$.
  let R_x := Finset.range (Nat.sqrt n + 1)
  let R_y_z := (Finset.range (n + 1)).product (Finset.range (n + 1))

  Finset.card $
  (R_x.product R_y_z)
  |>.filter (fun p =>
    let x := p.fst
    let y := p.snd.fst
    let z := p.snd.snd

    -- Constraints: $0 < y \le z$
    0 < y ∧ y ≤ z ∧
    -- Primality: $y$ or $z$ is prime
    (y.Prime ∨ z.Prime) ∧
    -- Equation: $n = x^2 + \totient (y ^ 2) + \totient (z ^ 2)$
    x^2 + totient (y ^ 2) + totient (z ^ 2) = n
  )

/--
The set of natural numbers $n$ for which $A262781(n) = 1$ according to the conjecture.
-/
def A262781_ones : Finset ℕ := {
  3, 5, 9, 10, 17, 20, 24, 25, 31, 36, 45, 73, 80, 101, 136, 145, 388, 649
}

/--
Conjecture from OEIS A262781:
(i) a(n) > 0 for all n > 6.
(ii) a(n) = 1 only for n = 3, 5, 9, 10, 17, 20, 24, 25, 31, 36, 45, 73, 80, 101, 136, 145, 388, 649.
-/
theorem oeis_262781_conjecture :
  (∀ n : ℕ, n > 6 → A262781 n > 0)
  ∧
  (∀ n : ℕ, A262781 n = 1 ↔ n ∈ A262781_ones) :=
by sorry
