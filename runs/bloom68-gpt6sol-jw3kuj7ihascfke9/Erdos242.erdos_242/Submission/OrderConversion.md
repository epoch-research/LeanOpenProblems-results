# Ordered versus unordered denominators: exact equivalence for `n > 2`

The proposition in `Submission/Spec.lean` uses `n x y z : ℕ`, **rational** division
`(4 / n : ℚ)` and `1 / x + 1 / y + 1 / z : ℚ`, and requires `1 ≤ x < y < z`.
`Spec.lean` is untouched. The independent propositions and proofs are in
`OrderedAudit.lean` and `OrderConversion.lean`; neither imports `Spec.lean` or
uses the admitted theorem.

**Theorem (Lean-checked, no `sorry`):** For *every* `n : ℕ` with `2 < n`, the
existence of **any** positive natural denominators (equality permitted) for
`4/n = 1/x + 1/y + 1/z` is equivalent to the existence of **strictly ordered**
positive natural denominators. The same is true for positive integer
(`ℤ`) denominators. Moreover, positive Nat and positive Int formulations
are equivalent regardless of `n`. See `raw_ordered_iff_unordered_nat`
(the exact `Spec.lean` right-hand side written out literally),
`unordered_nat_iff_ordered_nat`, `unordered_int_iff_ordered_int`,
`ordered_nat_iff_ordered_int`, `bad_ordered_iff_bad_unordered_nat`, and the
conditional equivalence of the two universal assertions
`all_ordered_iff_all_unordered_nat`.

Here is the constructive argument in the nontrivial (repeated) case. Permute
the three denominators to write the equality as

    4/n = 2/a + 1/b,     a,b ≥ 1.

* If `a=2u`, write `2/a=1/u`, and order the two remaining denominators
  as `s ≤ t`. For `n>2` we have `t≥2`: `s=t=1` would force `4/n=2`
  and `n=2`. Now split `1/t=1/(t+1)+1/[t(t+1)]`. The new denominators
  `s<t+1<t(t+1)` are strictly ordered and positive.
* If `a` is odd, `a=2c−1` with `c≥2` (the case `a=1` would make the
  right-hand side strictly greater than `2`, contrary to `n>2`). Use

      2/a = 1/c + 1/(ac).

  Since `c<ac`, the three new denominators are distinct unless `b=c`
  or `b=ac`. Both coincidences contradict **integrality of `n`**. The
  original equality gives `4ab=n(a+2b)`:

  - If `b=c`, then `n(a+2c)=4ac=a(a+2c)+a`, with `0<a<a+2c`.
  - If `b=ac`, cancelling `a>0` gives
    `n(2c+1)=4ac=4(c−1)(2c+1)+4`, with `0<4<2c+1`.

  Neither a multiple of a positive integer nor a multiple plus a proper
  positive remainder can be the same integer. Otherwise sort the three
  distinct denominators. All conversions retain *exactly three* unit
  fractions; they do not assume a solution to the open conjecture.

The restriction `n>2` is essential for this argument: at `n=2`, the
unordered triple `(1,2,2)` gives `4/2=2`, whereas even the maximum of
`1/x+1/y+1/z` for strictly ordered positive naturals is
`1+1/2+1/3=11/6<2`. But `n=2` is excluded by `Spec.lean`.

## Complete finite check, independent of the conversion theorem

`good_from_three_through_two_hundred` in `OrderedAudit.lean` proves in Lean
that **each** `n` in `3 ≤ n ≤ 200` has an ordered Nat triple. Its symbolic
outside-24 lemma `good_outside_24` settles 190 cases. For the remaining eight
values the Lean proof uses these checked exact rational identities:

| `n` | ordered `(x,y,z)` |
|---:|---:|
| 25 | (10,25,50) |
| 49 | (21,42,98) |
| 73 | (20,292,730) |
| 97 | (28,194,2716) |
| 121 | (44,132,363) |
| 145 | (58,145,290) |
| 169 | (52,338,676) |
| 193 | (50,1930,4825) |

`four_formulations_three_through_two_hundred` proves all four variants
(ordered/unordered, Nat/Int) in that interval. The unordered triple
`(1,6,6)` also solves the equation at `n=3`; `(1,4,12)` is ordered. Thus
repetitions genuinely occur but do not create an ordering-only failure.

For reference, a complete direct search at any fixed `n>0` can use the
**entire** finite first-denominator interval `n<4x<3n` (unordered sorted:
`n<4x≤3n`). For fixed `x`, put `A=4x−n>0` and `B=nx`. A candidate
`y` must satisfy `Ay>B` and `Ay<2B` (for ordered `y<z`; use `≤` for
sorted unordered denominators), and the **unique** remaining possibility
is `z=By/(Ay−B)`, which must be an integer satisfying the specified order.
The finite Lean certificate above proves positivity directly rather than
assuming completeness of a partial search.

## Precisely what remains open

The equivalence **does not prove either universal existence assertion** and
is not a `.disproof`. A hypothetical failure of the ordered statement for
some `n>2` would *also* be a failure of the classical positive-denominator
statement, rather than an artifact of strict ordering or of Nat versus Int.
By the separately checked `bad_prime_iff_no_divisors` in `CoveringGap.lean`,
an actual bad prime would need to exclude *both* Type I and Type II divisors
at **every** first denominator `p<4x`, `2x<p`. No such prime, or proof that
all remaining hard primes have a solution, is supplied here.

Kernel axiom audits via `#print axioms` for the displayed Lean theorems report
only `propext`, `Classical.choice`, and `Quot.sound`, the ordinary Lean logical
axioms: no `sorryAx`, user-added axiom, or imported admitted result occurs in
the proof dependencies.
