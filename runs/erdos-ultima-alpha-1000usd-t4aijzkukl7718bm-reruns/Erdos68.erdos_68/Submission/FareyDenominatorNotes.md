# Finite Farey denominator bound (verified, not a settlement)

`FareyDenominatorBound.lean` proves a finite necessary condition for rationality
of the original sum alpha. It does NOT prove or disprove Erdős 68, and
`Spec.lean` remains unchanged.

## Verified enclosure

Using the partial sum through `30!-1` and the existing positive-tail bound,
Lean verifies

    3872110933106098 / 3089042502434645
      < alpha
      < 49679453951081027 / 39632631245285943.

All finite rational comparisons are checked by `norm_num`. No floating-point
estimate, native decision procedure, or external calculation is used as a
proof. The endpoints were found by an external exact continued-fraction
calculation, but the Lean proof needs only the displayed inequalities and
their determinant-one identity.

## Denominator consequence

For integers a,b,c,d with positive b,d and bc-ad=1, any reduced rational p/q
strictly between a/b and c/d satisfies q>=b+d. Indeed the two positive integers
bp-aq and cq-dp are at least one, and

    q = d*(bp-aq) + b*(cq-dp) >= d+b.

The file proves this as `denominator_ge_of_farey_bounds`, then applies it to
the enclosure above. Its main result is

    rational_denominator_large (q : ℚ)
      (hq : (sum' k, term k) = (q : ℝ)) :
      42721673747720588 <= q.den.

Both printed axiom checks contain only `propext`, `Classical.choice`, and
`Quot.sound`. The file compiles and its olean has been built.

This excludes only finitely many possible denominators. There is no proved
upper bound on a putative rational denominator, and no proof that analogous
lower bounds diverge. Thus this result is not an irrationality proof, and
no proof of the original conjecture has been submitted.

## Verified extension: denominator greater than 10^100

`Submission/HugeFareyDenominatorBound.lean` now proves

    rational_denominator_gt_ten_pow_hundred (q : Q)
      (hq : (sum' k, term k) = (q : R)) : 10^100 < q.den.

This is still a finite necessary condition, not a settlement.

The proof does not form the enormous common denominator of the partial sum.
Instead, set B=10^240 and N=140, and compute exactly

    m = sum_(k=0)^(139) floor(B/((k+2)!-1)).

The generic lemma `scaled_partial_sum_floor_bounds` bounds B times the partial
sum between m and m+N. The existing positive-tail estimate, together with
B*(3/2)/((N+2)!-1)<1, gives

    m < B*alpha < m+141.

Lean checks the integer floor sum by `norm_num`; the full file takes about
12 seconds to check in the current environment. The numerical endpoints were
chosen externally, but their enclosure and determinant are checked inside
Lean. No native decision procedure is used.

The enclosing determinant-one fractions have denominators

    b=8088341017332992634409744751350956797733241625161194915099719936012921744537133798241494755517477409,
    d=7865688849216738017781803514903644114106774862081775569734428323655767175313915273498490023469790253.

Their sum is

    15954029866549730652191548266254600911840016487242970484834148259668688919851049071739984778987267662,

which is greater than 10^100. Applying the earlier determinant-one lemma
therefore gives the stated rational-denominator exclusion.

The checks for `huge_floor_sum`, `sum_huge_farey_bounds`, and the denominator
theorem list only propext, Classical.choice, and Quot.sound. The source has no
proof holes. The external endpoint generator and its output are
/tmp/huge_farey.py and /tmp/huge_farey.json.

There remains no proof that such verified lower bounds grow without bound,
and no independent upper bound on a hypothetical rational denominator.
Spec.lean is unchanged and still has the original sorry. No solution has
been submitted.
