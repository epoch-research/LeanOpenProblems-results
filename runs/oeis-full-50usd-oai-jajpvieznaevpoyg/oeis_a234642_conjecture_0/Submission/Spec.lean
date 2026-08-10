import FormalConjectures.Util.ProblemImports

open Nat Set

/--
A234642: Smallest $x$ such that $x \bmod \phi(x) = n$, or $0$ if no such $x$ exists.
-/
def A234642_condition (n x : ℕ) : Prop :=
  x.totient > 0 ∧ x % x.totient = n

/--
A234642: Smallest $x$ such that $x \bmod \phi(x) = n$, or $0$ if no such $x$ exists.
-/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {x : ℕ | A234642_condition n x}

/--
Conjecture: a(n) > 0 for all n. This would follow from a form of Goldbach's (binary) conjecture.
Checked up to 10^7; largest term in that range is a(9972987) = 4178506411.
-/
theorem oeis_a234642_conjecture_0 : ∀ (n : ℕ), a n > 0 := by
  sorry
