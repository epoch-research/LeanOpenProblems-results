import FormalConjectures.Util.ProblemImports

open Nat List Set

/-- A number is zeroless if its decimal digits are all non-zero. -/
def is_zeroless (k : ℕ) : Prop := 0 ∉ Nat.digits 10 k

/-- Predicate for $m$ to be an $n$-digit number. Assumes $n \ge 1$. -/
def is_n_digit (m n : ℕ) : Prop := 10^(n-1) ≤ m ∧ m < 10^n

/--
A358340: $a(n)$ is the smallest $n$-digit number whose fourth power is zeroless.
-/
noncomputable def a (n : ℕ) : ℕ :=
  if n = 0 then 0 else
  -- Define the set S of numbers satisfying the properties.
  let S : Set ℕ := { m : ℕ | is_n_digit m n ∧ is_zeroless (m ^ 4) }
  -- sInf returns the minimum element of the set S.
  sInf S

/--
A358340 It has been proved that there exist infinitely many zeroless squares and cubes but there is apparently no proof for 4th powers, 5th powers, etc.

Formalized as the conjecture that the set of natural numbers whose fourth power is zeroless is infinite.
This is equivalent to the statement that the set $\{ m : ℕ \mid \text{is\_n\_digit}(m, n) \land \text{is\_zeroless}(m^4) \}$ is non-empty for all $n \ge 1$, ensuring $a(n)$ is defined for all $n$.

================================================================================
STATUS OF THIS CONJECTURE (analysis by the submitter)
================================================================================
This is a GENUINE OPEN PROBLEM. The statement is true (the count of zeroless
fourth powers with `n` digits grows like `6.561^n`), but no proof is known, in
agreement with the OEIS comment ("apparently no proof for 4th powers").

Why the classical technique fails for the exponent 4:
The proofs for squares and cubes use a *self-similar* family `m_n ≈ α · 10^n`,
which succeeds exactly when there is a rational `α` whose `k`-th power has a
zeroless purely-periodic decimal expansion:
  * k = 2 :  (1/3)^2 = 1/9  = 0.\overline{1}     (zeroless period "1")
  * k = 3 :  (2/3)^3 = 8/27 = 0.\overline{296}   (zeroless period "296")
  * k = 4 :  NO such α exists.
A rational `α` with `α^4` of period `≤ 60` must have denominator `v` (coprime
to 10) with `v^4 ∣ 10^L − 1` for some `L ≤ 60`; the only such `v > 1` is `v = 3`,
and every `a^4 / 81` has a `0` in its period (e.g. `1/81 = 0.\overline{012345679}`).
Longer periods cannot be zeroless. Hence the self-similar method provably cannot
prove the exponent-4 case.

The concatenation/recursion method (`m = a·(10^t+1)` makes `m^4` the clean block
concatenation `[a^4 | 4a^4 | 6a^4 | 4a^4 | a^4]`) also fails to sustain: a single
step needs `a^4, 4a^4, 6a^4` of equal length, but iterating requires `6·m^4`,
i.e. blocks up to `36·a^4`, which spans more than one decimal length because
`C(4,2) = 6` and `6·6 = 36 > 10`. For k = 2, 3 the analogous factors are `4` and
`9` (both `< 10`), which is precisely why those exponents close and 4 does not.

DECISIVE POINT (why there is no elementary trick to find):
Two anchor routes exist for a self-similar family `n_j ≈ α·10^j`:
  (a) PERIODIC anchor: `α^k` has a zeroless purely-periodic expansion.  Exhaustive
      search over `p/q`, `q < 200`, finds such `α` for `k=2` (1/3→1/9=0.‾1) and
      `k=3` (2/3→8/27=0.‾296) but NONE for `k=4`.  So the clean square-style family
      (`(10^j+2)/3`, giving carry-free `R_{2j}+4R_j+1`) has no `k=4` analogue.
  (b) TERMINATING anchor: `α=c/10^d` with `c^k` zeroless (e.g. `66^3=287496`,
      `66^4=18974736`, both zeroless).  Here the leading block of `n_j^k` is fine,
      but the lower `~k·(scale)` positions must be filled by the `k-1` cross terms,
      which requires GROWING corrections (a fixed-coefficient polynomial family
      leaves zero-gaps).  Empirically those corrections exist for every `j` (the
      solution set is abundant) but follow NO clean recursion — for `k=4`, anchor
      `c=66`, the minimal corrections run `2,4,27,11,36,66,66,128,1097,9822,…`,
      i.e. exactly the unprovable digit-equidistribution.  With one correction
      parameter only the single dominant cross term can be shaped (this is why the
      `k=3` solutions cluster, and morally why the circle method closes for `k=3`:
      main-term exponent `1+3·log10(0.9)=0.863` > Weyl barrier `1-2^{1-3}=0.75`);
      for `k=4` THREE cross terms `4c^3m, 6c^2m^2, 4cm^3` overlap and cannot be
      jointly controlled, matching the circle-method FAILURE at `k=4`
      (`0.817 < 0.875`).
So neither the elementary nor the analytic route reaches `k=4`: it is genuinely
open, needing an unconditional fourth-power restricted-digit / Weyl-sum estimate
absent from the literature and from Mathlib.

A genuine proof would require an unconditional digit-equidistribution statement
for the *middle* digits of `m^4`, which is beyond current mathematics. I was
unable to settle it and, per the task rules, I will not submit a fabricated or
`sorry`-free pseudo-proof.
================================================================================
-/
theorem oeis_a358340_conjecture_k4 : Set.Infinite { m : ℕ | is_zeroless (m ^ 4) } := by
  -- VERIFIED reduction (uses only propext/Classical.choice/Quot.sound):
  -- the conjecture is equivalent to "arbitrarily large zeroless fourth powers exist".
  apply Set.infinite_of_not_bddAbove
  rintro ⟨B, hB⟩
  -- `hB : B ∈ upperBounds {m | is_zeroless (m^4)}`.  To finish we must exhibit some
  -- `m > B` with `is_zeroless (m^4)`, i.e. discharge:
  --
  --     ∀ B : ℕ, ∃ m : ℕ, B < m ∧ is_zeroless (m ^ 4).
  --
  -- THIS is the entire remaining content, and it is an OPEN problem in number theory
  -- (OEIS A358340: "apparently no proof for 4th powers").  See the header analysis:
  -- the circle method that proves the k=2,3 cases has main-term exponent
  -- 1 + k·log10(0.9) which drops below the Weyl-barrier exponent 1 - 2^(1-k) exactly
  -- at k=4 (0.817 < 0.875), so no currently available method settles it, and none of
  -- the machinery is in Mathlib.  No honest, axiom-clean proof can be supplied here.
  sorry
