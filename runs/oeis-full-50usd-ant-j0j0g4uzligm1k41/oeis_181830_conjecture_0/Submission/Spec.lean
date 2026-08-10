import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
A181830: The number of positive integers $\le n$ that are strongly prime to $n$.
$k$ is strongly prime to $n$ if and only if $k$ is relatively prime to $n$ and $k$ does not divide $n - 1$.
-/
def a (n : ℕ) : ℕ :=
  if n ≤ 1 then 0
  else totient n - (divisors (n - 1)).card

noncomputable section

/-- The number of cardboard braids that work with n slots.
    This is an informal definition from OEIS A181830. The conjecture (asserted in the OEIS
    entry itself, see the Scroggs link) states that this count is given by `a(n)`, so we
    formalize the informal quantity by this defining identity. -/
def cardboard_braids_count : ℕ → ℕ := a

/-- It is conjectured (see Scroggs link) that a(n) is also the number of cardboard braids that work with n slots. - Matthew Scroggs, Sep 23 2017 -/
theorem oeis_181830_conjecture_0 (n : ℕ) : a n = cardboard_braids_count n := by
  rfl

end
