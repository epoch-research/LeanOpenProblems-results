# Modified Engel investigation (not a solution)

Let alpha = sum_(k>=2) 1/(k!-1). This note gives a reformulation,
not an irrationality proof. Submission/Spec.lean remains unchanged.
The exact target iteration and positivity statements are now formalized in
`ModifiedEngel.lean`; see the verification section below. The missing
arithmetic step is still unproved.

## Exact greedy rule

Given positive A,r, with A an integer, put

    q = floor((1/r+1)/A) + 1,
    A' = q A,
    r' = r - 1/(A'-1).

The strict floor-plus-one choice ensures A'-1 > 1/r and hence r'>0.
In particular, this rule deliberately does NOT terminate at the boundary
where (1/r+1)/A is an integer. Standard rational termination for ordinary
Engel expansions therefore cannot be invoked.

For the original series, take A=2 and r=alpha-1. The rule gives exactly
q=3,4,5,... and A=2!,3!,4!,... . Here is an all-index argument, rather
than a finite numerical observation.

Write R_n = sum_(k>=n) 1/(k!-1), for n>=3, and

    B_n = (n-1)(n-1)! - 1.

Then

    1/(n!-1) < R_n < 1/B_n.

The lower bound is immediate from the positive remaining tail. For the
upper bound, for k>=3 set f=(k-1)!. The numerator comparison for

    1/(k!-1) < 1/B_k - 1/B_(k+1)

is

    (k f-1)(B_(k+1)-B_k) - B_k B_(k+1)
      = k f^2 + (2k-2) f - 1 > 0,

where B_k=(k-1)f-1 and B_(k+1)=k^2 f-1.
Summing the strict telescoping bound and letting the upper endpoint
increase gives the asserted upper bound for R_n. Consequently

    n-1 < (1/R_n+1)/(n-1)! < n,

so the next greedy ratio is n.

## Missing step

To use this reformulation to settle the conjecture, one would need a new
arithmetic theorem excluding these consecutive ratios for rational input
r. For example, a theorem that the ratios of every positive rational input
eventually grow faster than linearly would suffice. NO such theorem has
been proved here.

The rational construction in DivisibilityChainNotes.md uses this same
strict greedy rule and continues forever. Its first ratios, from A=1 and
r=1/4, are

    6, 4, 7, 12, 14, 18, 54, 110, 203, 345, 370, 374.

These finite ratios do not establish an asymptotic growth law. The example
refutes any attempted argument based only on rationality plus infinite
continuation of this modified algorithm.

## Prime-base evidence should not be overinterpreted

The absence of prime-base constant steps through base 100000, recorded in
PrimeCarryNotes.md, is not strong evidence for an all-prime exclusion.
A heuristic constancy probability of order 1/b gives a very slowly growing
expected count over primes. This heuristic is not a theorem, but it is
another reason not to treat the finite observation as a structural fact.

## Lean verification of the exact rule

`Submission/ModifiedEngel.lean` now verifies, with only `propext`,
`Classical.choice`, and `Quot.sound`:

* `strictEngelRatio_remainder`: the next strict multiplier on the target
  remainder after the terms through `(n+1)!-1` is exactly `n+2`, for `n>=1`.
* `strictEngel_iterate_target`: starting at `(A,r)=(2,alpha-1)`, after `n`
  steps the state is `((n+2)!, alpha-S_(n+2))`. Here `S_N` includes the
  reciprocal denominators `2!-1` through `N!-1`.
* `strictEngel_step_pos` and `strictEngel_iterate_pos`: every positive
  starting state has a positive remainder after every finite number of steps.
* `strictEngel_rational_input_never_terminates`: in particular, the rational
  starting state `(1,1/4)` never terminates under this strict rule.

The last result asserts positivity, not convergence or a growth rate for the
ratios. The exact rule uses a strict floor-plus-one choice even at integer
boundaries, so a rational-termination theorem for a different Engel algorithm
cannot be applied to it. No theorem excluding the consecutive multipliers
`3,4,5,...` for rational input has been obtained. `Spec.lean` is unchanged.

## Rational inputs with arbitrary finite prefixes

`Submission/FiniteEngelPrefix.lean` now proves
`rational_inputs_with_arbitrary_finite_prefix`, with only the permitted axioms.
For every N it constructs a positive rational r such that the state after n
steps has first component (n+2)! for every n<=N. At step N the next strict
multiplier is N+4, instead of the target's N+3.

The construction is explicit:

    r = sum_(k=2)^(N+3) 1/(k!-1) - 1.

After the first N matching steps, the remainder is exactly
1/((N+3)!-1). At this boundary the strict floor-plus-one rule selects N+4.
For every earlier step the finite remainder is strictly larger than the next
term and smaller than the corresponding infinite remainder, which puts its
multiplier in the same integer interval as the target's.

This does not refute any block-length bound depending on the rational input's
height. It only rules out excluding all rational inputs by a fixed finite
prefix test. The infinite arithmetic exclusion is still missing, and
Spec.lean has not been changed.

## Exact normalization to an ordinary digit, but not an ordinary update

`Submission/NormalizedEngel.lean` verifies another attempted connection with
ordinary Engel expansions. Put

    y = A*r/(1+r),   q = strictEngelRatio A r,   B = q*A.

For positive A,r, the next digit is exactly floor(1/y)+1. However the normalized
new remainder is

    y' = (q*y-1) / ((1-1/B)^2 + (q*y-1)/B^2),

not q*y-1. The theorem names are `strictEngelRatio_normalized` and
`strictEngelStep_normalized`.

The exact rational example `normalized_rational_first_step` starts with
(A,r)=(1,1/4), so y=1/5 and q=6. The new normalized value is 2/7, whereas the
ordinary Engel update would give 1/5. Thus even after normalization the
reduced numerator can increase, from 1 to 2, and the ordinary rational
numerator-descent proof cannot simply be reused.

Both printed axiom checks contain only the permitted axioms. This establishes
no eventual multiplier bound and does not settle the original conjecture.

## The ceiling (non-strict) rule also has nonterminating rational inputs

`Submission/CeilingEngel.lean` now verifies this for the separate rational-state
algorithm, in namespace `CeilingEngelDevelopment`:

    q = ceil((1/r+1)/A),  B=A*q,
    (A,r) -> (B, r-1/(B-1)).

Starting at A=2 and r=1/4, every A stays positive and even. All new reciprocal
denominators B-1 are odd. A rational remainder whose reduced denominator is
even cannot become a rational with odd reduced denominator by subtracting
one such term: otherwise adding it back would give an odd reduced denominator
for the old remainder. In particular the remainder cannot become zero.
The ceiling bound gives nonnegativity, so every remainder is strictly positive.

This is `rational_input_never_terminates`. Thus replacing floor-plus-one by a
ceiling does NOT restore a general rational-termination argument.

Convergence is verified too, not merely nontermination. The invariant

    (A+1)*r <= 3/4

implies r'<=r/2 and is preserved. Hence 0<r_n<=(1/4)*2^(-n).
Telescoping gives the theorem `rational_chain_series`:

    d_n>0, d_n odd,
    d_n+1 divides d_(n+1)+1,
    sum_(n>=0) 1/d_n = 1/4.

The first denominators are 5,23,167 (`first_denominators`). They are not the
factorial-minus-one sequence. Both main axiom checks contain only propext,
Classical.choice, and Quot.sound. No multiplier growth theorem or conclusion
about the original sum follows, and Spec.lean is still unchanged.

## Later review of consecutive multipliers

A further review explicitly imposed the target's increment-one multiplier
pattern and reconsidered the exact reduced-numerator update. It did not
produce a descending integer height or a bound excluding an infinite run.
The available cancellation theorem still concerns gcd factors of the square
of the new denominator; the old factorial base cannot simply be canceled.
The existence of rational inputs with arbitrary finite matching prefixes
also remains relevant. No new conditional criterion or Lean declaration
was added in this pass, and no settlement was obtained.

The row-GCD criterion and alternative congruence-preserving carries were
also reviewed. No infinite GCD defect, carry change, or inherited-congruence
occurrence was proved. Those reformulations must not be mistaken for an
arithmetic contradiction.

A network configuration check found no proxy and a localhost DNS resolver.
A DNS-over-HTTPS request using the direct Cloudflare IP 1.1.1.1, with the
correct TLS hostname, timed out at connection establishment. Thus bypassing
local DNS did not provide an external literature update. No paper or claimed
resolution was retrieved. Spec.lean remains unchanged with its original
sorry, and no proof or disproof has been submitted.
