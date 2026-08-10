import FormalConjectures.Util.ProblemImports

open Nat Finset Matrix

/--
A001818: Squares of double factorials: $(1 \cdot 3 \cdot 5 \cdot \dots \cdot (2n-1))^2 = ((2n-1)!!)^2$.
-/
def a (n : ℕ) : ℕ :=
  ((range n).prod (fun k => 2 * k + 1)) ^ 2


/--
Conjecture 1: For any primitive 2n-th root zeta of unity, the permanent of the 2n X 2n matrix [m(j,k)]_{j,k=1..2n} coincides with a(n) = ((2n-1)!!)^2, where m(j,k) is (1+zeta^(j-k))/(1-zeta^(j-k)) if j is not equal to k, and 1 otherwise.
-/
theorem oeis_1818_conjecture_0 (n : ℕ) (h_n : 1 ≤ n) :
    ∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ) := by
  sorry
