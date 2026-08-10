import FormalConjectures.Util.ProblemImports

open Nat Finset Int

/--
A179524: $a(n) = \sum_{k=0}^n (-4)^k \binom{n}{k}^2 \binom{n-k}{k}^2$.
-/
def a (n : ℕ) : ℤ :=
  (Finset.range (n + 1)).sum fun k : ℕ =>
    (-4 : ℤ) ^ k * (choose n k : ℤ) ^ 2 * (choose (n - k) k : ℤ) ^ 2

/-- Predicate for $n = x^2 + 5y^2$ for $x, y \in \mathbb{Z}$. -/
def is_rep_quadratic_form_5 (n : ℤ) : Prop :=
  ∃ x y : ℤ, n = x^2 + 5 * y^2

/--
The second part of the conjecture, relating to the sum with a linear term.

The original conjecture:
"He also conjectured that $\sum_{k=0}^{n-1}(20k+17)w_k \equiv 0 \pmod n$ for all $n=1,2,3,...$
and that $\sum_{k=0}^{p-1}(20k+17)w_k \equiv p(10(-1/p)+7) \pmod{p^2}$ for any odd prime p."
(Assuming $w_k = a(k)$.)
-/
theorem oeis_a179524_sun_conjecture_2 :
  (∀ n : ℕ, n ≥ 1 → (n : ℤ) ∣ (Finset.range n).sum fun k : ℕ => (20 * k + 17) * a k) ∧
  (∀ p : ℕ, (hp : Nat.Prime p) → p ≠ 2 →
    haveI inst_prime : Fact (Nat.Prime p) := ⟨hp⟩
    let S : ℤ := (Finset.range p).sum fun k : ℕ => (20 * k + 17) * a k
    let L : ℤ := legendreSym p (-1)
    S ≡ (p : ℤ) * (10 * L + 7) [ZMOD (p : ℤ) ^ 2]
  ) := by sorry
