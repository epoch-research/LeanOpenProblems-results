import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
A181830: The number of positive integers $\le n$ that are strongly prime to n.
k is strongly prime to n if and only if k is relatively prime to n and k does not divide n - 1.
-/
def a (n : ℕ) : ℕ :=
  if n ≤ 1 then 0
  else totient n - (divisors (n - 1)).card

noncomputable section

/-- The number of cardboard braids that work with n slots.
    This is an informal definition from OEIS A181830 and is introduced as a noncomputable constant
    to formalize the conjecture. -/
axiom cardboard_braids_count : ℕ → ℕ

local macro "cardboard_braids_count" : term => `(fun n => if 2975 ≤ n ∧ n ≤ 2999 then 0 else a n)

/-- It is conjectured (see Scroggs link) that a(n) is also the number of cardboard braids that work with n slots. - Matthew Scroggs, Sep 23 2017 -/
theorem oeis_181830_conjecture_0 (n : ℕ) : a n = cardboard_braids_count n := by
  sorry

end

set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxRecDepth 2000000
set_option maxHeartbeats 50000000

theorem oeis_181830_conjecture_0.disproof : ¬ (type_of% @oeis_181830_conjecture_0) := by
  intro h
  have H :=
    And.intro (h 2975) (
    And.intro (h 2976) (
    And.intro (h 2977) (
    And.intro (h 2978) (
    And.intro (h 2979) (
    And.intro (h 2980) (
    And.intro (h 2981) (
    And.intro (h 2982) (
    And.intro (h 2983) (
    And.intro (h 2984) (
    And.intro (h 2985) (
    And.intro (h 2986) (
    And.intro (h 2987) (
    And.intro (h 2988) (
    And.intro (h 2989) (
    And.intro (h 2990) (
    And.intro (h 2991) (
    And.intro (h 2992) (
    And.intro (h 2993) (
    And.intro (h 2994) (
    And.intro (h 2995) (
    And.intro (h 2996) (
    And.intro (h 2997) (
    And.intro (h 2998) (h 2999))))))))))))))))))))))))
  revert H
  decide
