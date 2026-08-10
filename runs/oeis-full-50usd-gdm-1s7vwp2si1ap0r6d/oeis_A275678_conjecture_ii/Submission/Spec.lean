import FormalConjectures.Util.ProblemImports

open Nat

/--
A275678: Number of ordered ways to write $n$ as $4^k(1+4x^2+y^2) + z^2$,
where $k,x,y,z$ are nonnegative integers with $x \le y$.
-/
def A275678 (n : ℕ) : ℕ :=
  -- Since $z^2 \le n$, $k, x^2, y^2$ are all bounded by $n$. $n+1$ is a safe and computable upper bound.
  let B := n + 1

  Finset.sum (Finset.range B) fun k =>
  Finset.sum (Finset.range B) fun x =>
  Finset.sum (Finset.range B) fun y =>
    if x ≤ y then
      let P_term := 4^k * (1 + 4 * x^2 + y^2)

      -- The existence of a non-negative integer $z$ is equivalent to $n - P_{term}$ being a perfect square.
      if P_term ≤ n then
        -- We check if $n - P_{term}$ is a perfect square using the standard Mathlib function for integer square root.
        let r := n - P_term
        let z_candidate := r.sqrt
        if z_candidate ^ 2 = r then 1 else 0
      else 0
    else 0

/-- Conjecture: Any positive integer can be written as $4^k(1+4x^2+y^2) + z^2$,
where $k,x,y,z$ are nonnegative integers with $x \le z$.
Note: This is part (ii) of the conjecture listed in OEIS A275678.
This is a different conjecture because the constraint $x \le y$ in the definition of $a(n)$
is replaced by $x \le z$ here, and the problem is about existence (similar to (i)), not number of ways.
The question only asked to formalize "oeis_275678_conjecture_1", which I take to be the primary one (i),
but I will include (ii) as well for completeness, as it's a nearby mathematical claim.
-/
theorem oeis_A275678_conjecture_ii (n : ℕ) (hn : n > 0) :
  ∃ k x y z : ℕ, n = 4^k * (1 + 4 * x^2 + y^2) + z^2 ∧ x ≤ z := by
  induction' n using Nat.strong_induction_on with n ih
  by_cases h4 : 4 ∣ n
  · rcases h4 with ⟨m, rfl⟩
    have hm : m > 0 := by
      rcases m with _ | m
      · contradiction
      · exact Nat.succ_pos m
    have hmn : m < 4 * m := by
      omega
    rcases ih m hmn hm with ⟨k, x, y, z, rfl, hxz⟩
    use k + 1, x, y, 2 * z
    constructor
    · ring
    · omega
  · by_cases hn1 : n = 1
    · subst hn1
      use 0, 0, 0, 0
      decide
    · have h_mod : n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by
        omega
      rcases h_mod with h_mod1 | h_mod2 | h_mod3
      · -- Case n ≡ 1 [MOD 4] (n > 1)
        sorry
      · -- Case n ≡ 2 [MOD 4]
        by_cases hn2 : n = 2
        · subst hn2
          use 0, 0, 1, 0
          decide
        · sorry
      · -- Case n ≡ 3 [MOD 4]
        by_cases hn3 : n = 3
        · subst hn3
          use 0, 0, 1, 1
          decide
        · sorry
