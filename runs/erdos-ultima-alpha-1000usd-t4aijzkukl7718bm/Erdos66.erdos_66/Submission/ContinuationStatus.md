# Continuation status: no settlement

The original `Erdos66.erdos_66` in `Submission/Spec.lean` remains unchanged
and contains its original `sorry`. No proof or disproof has been obtained.
No new production Lean theorem was added in these subsequent reviews.

## Formal statement audit

`FormalConjecturesForMathlib/Combinatorics/Additive/Convolution.lean` defines
`sumRep A n` as the cardinality of the filtered natural antidiagonal:

    #{(a,b) : a+b=n and a in A and b in A}.

Thus it is the intended ordered natural-number representation count. There
was no discrepancy in the definition or the target proposition that supplied
a resolution.

A subsequent source-signature scan found 49 auxiliary declarations with an
existential conclusion containing both `Tendsto` and `sumRep`. The candidate
signatures were saved to `/tmp/erdos66_limit_endpoints.txt`. The direct
completion endpoints remain conditional: they require the sharp all-target
upper coefficient and summable repair costs (or lower-exception count
exponents strictly below one half for every tolerance). The rounding
endpoints explicitly assume the missing quadratic-error limit. The other
existence endpoints found include exceptional-target limits and examples
without a limit, not an unconditional witness to the original proposition.

A second scan found 71 direct (nonexistential) conclusion signatures containing
`Tendsto` and `sumRep`, saved in `/tmp/erdos66_direct_limits.txt`. The apparent
positive candidates are conditional transfers, averaged or masked limits,
or a changing-set diagonal limit. The nonexistence candidates have additional
restrictions on the set or on its errors. No unconditional named-set witness
or unrestricted negation was found. The imported convolution support file
contains the definition and its two basic identities, not a resolution.

The unchanged target SHA256 is:

    32d7caa914aad816045b3efa978ba8171e246a4dc01a8e77f192008b25ff41a0

## Reviews that did not close the gap

* The fixed-modulus monotone-profile operators do not imply compatibility
  between independently chosen moduli.
* The spatial prefix error is relative to the full cyclic mixed mean,
  not relative to an arbitrarily short prefix's own mean. The bounds do
  not provide the growing-height, cutoff-independent finite feasibility.
* Prescribed-prefix extension retains a predictive quadratic-error
  hypothesis. A counting-profile invariant alone does not prove it.
* The logarithmic concentration certificate has a fixed coefficient /
  tolerance threshold. It cannot be iterated to vanishing tolerance at
  one fixed coefficient on the strength of that certificate alone.
* The available exceptional-set bounds do not imply the negligible
  excess/deficit repair budgets required by the existing repair theorems.
  Dense transition deficits cannot simply be charged as negligible mass.
* The verified universal fluctuation bound has square-root-logarithmic
  size and is compatible with the proposed o(log n) error.
* Fixed-block replication preserves the existence of a logarithmic limit
  in both directions; it does not create convergence or normalize the
  increasing coefficients in the fixed-tolerance existence theorem.

No new theorem was established by the informal reviews of parity splitting,
variable smoothing, rotation models, or finite-field towers. In particular,
none should be used as an input to a final Lean proof.

Another attempt to retrieve https://www.erdosproblems.com/66 failed with
DNS resolution failure. No external resolution was retrieved.

## Actual remaining task

A solution still needs a genuinely new unrestricted input: either uniform
finite-prefix feasibility with fixed coefficient and threshold function,
an appropriate all-target Boolean rounding / compatible construction, or
a universal contradiction to the original limit. No valid proof has been
submitted during these reviews.

## Further continuation: fixed-height operators and nested fields

Rechecked the actual bounds in `JointMonotoneProfileOperatorExplore.lean`,
`UniversalMixedHeightExplore.lean`, `LogarithmicPrefixSystemExplore.lean`,
and their palette inputs. They do not supply uniform finite-prefix
feasibility: their error is normalized by the full modulus, while the
height range required by the harmonic profile grows with that modulus
when a lower natural cutoff is held fixed. No missing uniformity was
established.

Also reviewed the finite-field family and the existing quadratic/odd
extension results as a possible route to compatible scales. Quadratic
extensions erase the inherited quadratic-character pattern; odd
extensions preserve the old pattern but do not by themselves give growing
label sets, ordinary integer carry control, or the required intermediate
natural-prefix estimates. No new theorem or unrestricted obstruction was
obtained from this review.

The target file remains unchanged. No valid proof or disproof was obtained,
and no incomplete proof was submitted in this continuation.

## Subsequent verified progress: growing finite-field extensions

The next continuation added four compiling production files and audited 26
new declarations. `GrowingFieldExtensionProgress.md` records their exact
statements and scope. In particular, a fresh low-character-energy parameter
block can be adjoined outside an old field, and the origin repair can grow
with it, while the actual old field-plane slice remains exact. The subfield
block specialization gives explicit all-target relative error at the growing
mean (|U|+|F|)^2 under its stated numerical hypotheses.

Thus the older statement that no growing-label finite-field error estimate
was obtained has been improved in this specific finite setting. It remains
incorrect to infer a natural-number witness: ordinary carries, logarithmic
scale tuning, and intermediate natural prefixes are not controlled.
Spec.lean is still unchanged, and no valid proof or disproof was submitted.

## Subsequent verified progress: actual fields and fixed logarithmic tuning

Three further production files compile and five new declarations pass the
permitted-axiom audit. `LogTunedFieldExtensionProgress.md` records the theorem:
c and delta precede a threshold and the old finite field; an actual odd-degree
extension K and actual finite B then have the exact old repaired field-plane
slice and all-target field-group error at most delta after normalization by
log(|K|^2). The degree and cardinality are proved for a constructed field type.

The finite-field coefficient-tuning gap is therefore removed in this setting.
The conjecture is still not settled: no ordinary integer-carry transfer with
compatible intermediate natural prefixes has been obtained. Spec.lean remains
unchanged, and no incomplete proof was submitted.

## Subsequent verified progress: plain coset encodings are too thin

`CosetWindowObstructionProgress.md` records three more compiling production
files and 16 audited declarations. Off-old-plane cosets meet a nonzero
parabola union with origin repair in at most 2|U|+4 points. Any finite-window
injective natural encoding into one such coset inherits that cardinality
bound. The recent subfield-block parameter regime |U|<=2q consequently has
only O(q) points in [q^2,2q^2), while every hypothetical witness needs more
than Cq+C there for every fixed C, eventually.

This excludes plain coset-by-coset encoding of that parameter regime and
shows why improved carry constants alone do not suffice. It does not exclude
larger parameter families, interleaved cosets, other models, or arbitrary
natural sets. The original conjecture remains unresolved and Spec.lean is
unchanged. No incomplete proof was submitted.


## Further audit: qualitative host invariants

Read the actual definitions in SublogPatternInvariantsExplore.lean and the
constructed-host statements in ExactBracketPatternHostExplore.lean and
ExactBracketHostEnvelopeExplore.lean. SmallBoundary controls boundary pair
counts; SublogCentral controls central TRIPLE fibers at two DISTINCT targets.
Neither is a pointwise bound for the central self-convolution error at one
target. The same host's unconditional envelope remains K+34 log(n+2), not
the sharp coefficient-one asymptotic upper bound. No overlooked implication
to the original convergence statement was found. No new proof of Spec.lean
was obtained; its statement and sorry remain unchanged.


## Further audit: exact host-to-repair hypotheses

Compared the actual statements in ExactBracketHostEnvelopeExplore.lean,
GlobalAdaptiveRankRepairExplore.lean, DeficitWeightedCompletionExplore.lean,
and CountingPowerCompletionExplore.lean. The host has coefficient-one
power-cost rows but only the global upper envelope K+34 log(n+2). The
completion theorems separately require the asymptotically sharp upper
coefficient. Coordinated rank repair requires packet demand S(N) with
S(N) log(N)/sqrt(N) tending to zero; that demand bound is not a conclusion
of the host theorem.

PowerExceptionalProfileExplore.lean defines its saving as c*delta^2/256.
For the coefficient-one reciprocal-tolerance rows delta<=1, this saving is
at most 1/256. The count-only completion criterion instead requires an
exceptional-count exponent strictly below 1/2 at every fixed tolerance.
The bounded central-triple certificates do not establish that condition
or the sharp upper bound. No overlooked theorem composition was found.
This audit added no production Lean theorem and did not settle Spec.lean.


## Further audit: one-sided fluctuation theorem already available

SharpCapRoundingObstructionExplore.lean already proves the proposed
one-sided obstruction. Under a nonzero logarithmic limit and vanishing
signed harmonic-centered prefix means, neither a global bounded upper
error nor a global bounded lower error is possible. Bounded-discrepancy
harmonic roundings supply the signed-mean hypothesis, and the file also
excludes any finite limit for such a rounding with an eventual fixed
additive upper cap. These extra hypotheses do not follow from the original
conjecture. No new production theorem was added by rediscovering this
argument, and it is not an unrestricted disproof.

## Further continuation: prescribed prefixes, moments, and references

Re-examined whether complete-field parameter-energy estimates preserve an
arbitrary ordinary natural prefix. They do not presently supply the required
root-location restrictions. Existing arbitrary pair-weight estimates apply
to weights on parameter labels, not to arbitrary restrictions on the roots
within an ordinary prefix. No prefix extension theorem was obtained.

Re-read the growing-moment counterexamples and the witness counting-profile
theorem. The counterexamples are not asserted to satisfy every witness
hypothesis. Conversely, the counting profile does not provide the missing
growing-order correlation estimates. No factorial moment lower bound under
the actual witness hypothesis was established; the checked Jensen bounds
remain insufficient for an o(log n) contradiction.

Reference requests failed again: ordinary requests failed DNS, and two bounded
direct-IP requests to raw.githubusercontent.com timed out connecting to port
443. No external resolution was retrieved. No new production Lean declaration
or proof of the original conjecture was added in these continuations.
Spec.lean remains unchanged, with its original sorry. No proof was submitted.

## Continuation: checked single-window rotation obstruction

See `RotationTubeProgress.md`. Two new production files prove that no set
`{n | Int.fract (n * Real.sqrt 2) <= p n}`, with antitone p taking values in
[0,1], can have the conjecture's nonzero logarithmic limit. The proof combines
a uniform finite reflection spike with a rotation counting bound and the
necessary square-annulus mass of any witness. `RotationTubeAudit.log` records
only permitted axioms for nine principal declarations.

This is a restricted construction obstruction, not a universal disproof.
The literal single-window rotation transfer is excluded; changing finite
patterns and more general acceptance sets are not. Further informal reviews
of phase drift, finite-field transitions, and moment arguments supplied no
unrestricted ingredient. Spec remains unchanged with its original sorry; no
proof submission was made.

### Further continuation: changing patterns and nonlinear row phases

The cited reference was retried; DNS resolution for erdosproblems.com still
failed. No external result was obtained.

Further informal work considered nonlinear row phases as a way to average
away a fixed low-modulus representation error. Linear phases do not do this:
on a row antidiagonal their sum is constant. Nonlinear phases would require
new control on the active row-pair sets. Full-row averaging does not supply
that control once the construction is thinned to the required infinite
counting density. No nonlinear-phase theorem, compatible changing-pattern
chain, or unrestricted contradiction was obtained. No production source was
changed in this further continuation, and Spec remains unchanged.
