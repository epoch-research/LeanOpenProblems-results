## Continuation after the uniform prime-multiplier bound

This continuation obtained no complete proof or disproof and no new Lean
lemma. `Spec.lean` remains unchanged with its original `sorry`.

The common differential-operator approach was checked against the existing
exact adjoint constructions. Those operators and their finite polynomial
and logarithmic tests were already completed; no new endpoint elimination
or compatible aggregate-denominator estimate was obtained.

Approximate rational-function telescopers for the factorial-power tails
were reconsidered. Exact constant-column cancellation is already excluded
by the earlier rational-function theorem; allowing approximate cancellation
still requires a bound on the reduced aggregate boundary and the full
omitted-column error. No construction meeting both requirements emerged.

The multi-row detection and nonuniform-weight variants of the boundary
lattice were also reviewed. Neither extending the number of detected rows
nor introducing larger late-coordinate allowances supplied a proved short
integral lift with nonzero value. The existing all-phase detection bounds
cannot be applied to a single cleared phase, and the factor-two counting
budget gap remains unresolved.

No numerical experiment or submission check was run. Nothing is pending
compilation or computation. The separately verified
`PrimeMultiplierQuantitative.lean` remains auxiliary, not a settlement.


# Arithmetic and interpolation review (unresolved)

This note records informal mathematical review, not a new Lean theorem.
It is NOT a settlement of Erdős 68. No proof or disproof has been submitted.

## Congruence-preserving carry

The existing exact carry orbit was checked again. Its prime-unit and
predecessor congruences permit the already verified rational prime-gap
pattern, with prime tails arbitrarily close to their quadratic bound.
The original prime-band and twice-prime-square congruences cannot simply
be transferred to this carry. No new inheritance result or applicable
fixed-factor prime-tail bound was obtained.

## Boundary interpolation

The existing linear-window lattice experiments give useful nonzero forms
in finitely many cases, but still provide no general bound for the last
useful minima or for lifts of projected coefficient pairs. The verified
quadratic-window pigeonhole argument allows zero pairs and zero values.

A possible shortcut was reviewed: space samples farther apart, so that
successive residuals decay enough to make their earliest nonzero weighted
term dominant. This requires lower bounds and a weighted tail comparison,
not just the existing upper bounds. Increasing sample spacing also increases
the final index and the factorial boundary-clearing cost, so the coefficient
bound from ordinary pigeonhole cannot be kept fixed while claiming the
stronger decay. No compatible parameter choice, nonvanishing theorem, or
impossibility theorem was proved in this review.

The direct Padé, finite Stieltjes, and factorial-power-column constructions
were checked against their earlier notes. Their existing finite tests do not
control reduced denominators asymptotically. No new numerical search was run,
and no complete informal proof is awaiting formalization.

## Status

Spec.lean is unchanged with its original sorry. The earlier auxiliary
PrimeRowRemainder.lean remains verified, but its lower bound is compatible
with positive integer row tails and does not close any of the above gaps.
A renewed attempt to retrieve the problem reference failed at DNS resolution.

## Further exact-tail and positive-kernel review

The exact consecutive-multiplier modified Engel recurrence was reconsidered,
including its rational numerator/denominator update and normalization to an
ordinary Engel digit. No decreasing integer height was found. The normalized
map's correction changes the update, so ordinary rational termination does
not apply. The fixed rational input height cannot simply be substituted for
the growing reduced denominators of its later remainders.

The J=2 physical-domain Gram construction was also reviewed through its
polynomial column constraints and endpoint boundary formula. No explicit
recurrence producing integral final coefficients with sufficiently small
errors was obtained. Rational auxiliary coefficients need not be cleared
individually, but this does not itself control the final boundary rounding.
A matrix/determinant reformulation would likewise require genuine arithmetic
and dimension-relative error estimates; none were established here.

A fresh search of Mathlib files containing both irrationality and factorial
material found no applicable theorem for the target. No new solver run, Lean
proof of the conjecture, or complete informal argument resulted from these
checks. Spec.lean remains unchanged and the conjecture remains unresolved.

## Further exact-denominator and partial-clearing review

The adjacent denominator recurrence was reconsidered as a possible source
of a rational integer-height descent. The exact normalized greedy update
still differs from the ordinary Engel map. No decreasing integer height,
no bound excluding consecutive multipliers, and no complete argument were
obtained.

A variant of the prime-last-weight construction was also reviewed: leave
one prime factor uncleared, so that a nonzero form could lie in (1/p)Z
rather than Z. To use the resulting lower bound 1/p, one would need a
sufficiently short clearing vector whose last coefficient is nonzero
modulo p. The full lattice having such vectors does not bound a short
representative outside the corresponding index-p sublattice. Homogeneous
pigeonholing can still return only vectors inside that sublattice. No
compatible nonvanishing/size theorem was established.

These are informal reviews, not new Lean theorems. The separate verified
DoldRationalComparison now shows that the Dold congruences, prime units,
positivity, and its stated polynomial tail bounds allow a different rational
series. It does not preserve the predecessor congruence or exact target.
Nothing in this review settles the original conjecture.


## Review after the unsuccessful submission check

A submission check was run with the original Spec.lean still containing its
sorry; the user reported that verification failed. This was not a completed
proof. Spec.lean remains unchanged.

The signed-product recurrence was reconsidered. In particular,

    (E_(n+1)-E_n)/(n+2)! = -E_n,
    (C_(n+1)-C_n)/(n+2)! = -(P_n+(n+1)*E_n).

These first divided differences merely recover earlier product-scale
quantities. This observation is not a theorem excluding all higher-order
combinations. No combination with both adequate arithmetic divisibility and
a sufficiently small nonzero real value was found.

A separate review considered approximating the shifted factorial-power tails
C_j(N)=sum_(m>=1) [N!/(N+m)!]^j before combining them with the original finite
row prefix. The existing TailPowerExpansion results give the exact full-target
remainder, but the C_j(N) themselves are irrational, not rational coefficients.
No rational approximation family with a controlled final coefficient height,
full-target error, and nonvanishing has been constructed. In particular,
ordinary simultaneous approximation does not supply a one-sided error bound
or exclude a zero total form under a rationality hypothesis.

No new Lean theorem, new numerical construction, or complete informal proof
resulted from this review. DNS lookups for the problem reference and arXiv
again failed. No computation remains running.

## Row-separation and simultaneous-clearing review

The distinct decay rates of the geometric Lambert rows were reconsidered as
an approach to nonvanishing. For integer weights supported between H and T,
a nonzero contribution from row d has a rational denominator dividing

    (d!-1)*(d!)^floor(T/d).

This gives a lower bound for that individual row. Comparing it with the
remaining rows requires both the full support endpoint T and the weight
height. No uniform comparison applicable to the bounded boundary-clearing
vectors was established. In particular, fixed-operator decay observations
cannot be applied without adjustment when the operator and its coefficient
height grow with H.

Clearing several shifted boundaries could give more row conditions, but the
previous exact simultaneous-index tests do not supply a useful general bound
for this cost. Neither a bounded lift outside the zero-pair kernel nor an
asymptotic nonvanishing theorem resulted from this review. This section is
informal mathematical review, not a new Lean declaration.

The separate TwoColumnFiniteIndependence.lean has been checked successfully;
its finite independence theorem remains conditional on BOTH column sums
being zero. It has not been transferred to a relation for the original
series. No complete proof or disproof of Spec.lean has been obtained.

## Further review of the rowwise-gcd stabilization criterion

This pass returned to the exact equality of consecutive gcd-corrected
approximants, rather than constructing another approximation family.
No infinite non-stabilization proof was obtained.

For a reduced fraction a/b, suppose at a particular index the equalities

    Q_n=(F_n+g_n)/n!=a/b,
    n!=b*g_n*h_n

hold with integral h_n. Then necessarily

    F_n=g_n*(a*h_n-1).

The gcd requirement becomes gcd(a*h_n-1,b)=1, since a*h_n-1 is already
coprime to h_n. These conditions are compatible with a fixed rational
corrected value. The displayed factorization n!=b*g_n*h_n is not asserted
for every isolated equality Q_n=a/b: it is available eventually under the
existing rationality hypothesis and small-tail bounds. Thus no additional
integer descent follows just by rearranging those gcd equalities.

The exact recurrence for the floor carries and the previously proved
necessary upper residue interval were also reconsidered. No arithmetic
property of the actual floor sums excluding that interval at arbitrarily
large indices was proved. The finite checks of distinct corrected values
remain finite checks and are not promoted to an all-index statement.

This was mathematical review, not a new Lean declaration. No complete
informal proof or disproof is awaiting formalization, and no new submission
check was made. Spec.lean is unchanged with its original sorry. Nothing is
running or pending compilation from this pass.

## Further exact-recurrence and prime-tail review

The rowwise-gcd criterion, modified Engel update, and actual carried prime
recurrence were reconsidered together. The exact denominator update still
provides no decreasing integral height. For the actual carry,
T_p=p*T_(p-1)-1 at primes allows near-quadratic tails when the composite
predecessor is near its permitted upper endpoint. No new bound on that
predecessor was established, and no averaged deficit violation was proved.

A further informal row-separation review retained both the complete support
endpoint and the weight height. Individual row cancellation is not the same
as annihilating the entire periodic row sequence. No bound on the first
uncancelled row applicable to the boundary-clearing lattice was obtained.
Consequently this review supplies neither uniform growing-operator
nonvanishing nor a useful projected lift theorem.

No new Lean theorem or completed informal proof resulted from this pass.
Spec.lean remains unchanged with its original sorry. No submission check was
run, and nothing is pending compilation or computation.


## Review after the modulo-four classification

The exact modified Engel recurrence was checked again, including both the
unscaled rational numerator update and the normalized ordinary-digit map.
No decreasing integer height was obtained. Consecutive target multipliers
still do not supply ordinary Engel termination: the new denominator enters
the rational update, and the verified cancellation bound does not remove it.

A finite-column separation attempt was also reconsidered. The rational
boundary heights and the omitted-column errors must both be retained; no
quantitative separation estimate compatible with those heights was found.
The new modulo-four classification of the original Lambert coefficients
still does not constrain the real floors in the carry strongly enough to
prove infinitely many failures of its necessary rational residue pattern.

This was mathematical review, not a new Lean theorem or a settlement.
Spec.lean remains unchanged with its original sorry. No submission check or
new numerical experiment was run, and nothing is pending.

## Further boundary, carry, and physical-kernel review

The quantitative prime detector was compared with the boundary-lattice
construction again. Its nondivisibility condition remains incompatible
with clearing both adjacent detecting forms; it does not give a bounded
nonzero cleared form. The existing joint row-and-column constructions do
not remove the full-target remainder or their reduced-boundary height cost.

The physical-domain positive-kernel construction was also reconsidered.
Only the retained coefficient and aggregate boundary need to be integral;
clearing all auxiliary polynomial or Gram coefficients would be an
unnecessary restriction. Nevertheless no bound on those two retained
integer coefficients, compatible with errors tending to zero, was found.
The finite feasible kernels and SDP diagnostics do not supply such a bound.

This pass produced no new Lean theorem, no infinite carry-residue violation,
and no complete informal proof or disproof. No numerical experiment or
submission check was run. Spec.lean is unchanged with its original sorry,
and no computation or compilation is pending.

## Exact denominator and nonuniform-window continuation

The exact recurrence d_(n+1)=(n+1)*d_n+n was reconsidered in reduced
rational-tail and normalized Engel coordinates. No decreasing integer
height was obtained. The known reduced-denominator cancellation rule
continues to allow growth of both the numerator and denominator.

Nonuniform boxes for the boundary weights were considered as an alternative
to a common weight bound. Larger allowances at later sample indices can
improve the elementary counting estimate, but a collision still need not
have a nonzero retained coefficient or boundary. No quantitative theorem
excluding the zero-pair subspace, or selecting a useful bounded lift, was
proved. This is a gap in this proposed construction, not a general
impossibility theorem for nonuniform weights.

Local library and source searches found no theorem resolving the exact
series. No new numerical experiment or Lean theorem resulted from this
pass. Spec.lean remains unchanged with its original sorry. No submission
check was run, and no process is pending.

## Review after the half-integer-root construction

This continuation produced no complete proof or disproof, and no new Lean
lemma. `Spec.lean` remains unchanged with its original `sorry`.

The actual carry recurrence, its fractional-part criterion, the prime-gap
pattern, and the rowwise-GCD criterion were reviewed. No arithmetic
contradiction to the rationality-forced pattern, and no infinite occurrence
of a violating residue or small fractional part, was obtained.

For the half-integer-root family, dividing a polynomial by a rational scalar
does not give a new primitive coefficient pair: after clearing the final two
coefficients and reducing their gcd, the pair is the same. The verified
unreduced error bound cannot be transferred to that primitive pair without
controlling the gcd. Conversely, the finite primitive-pair tests do not
establish a useful asymptotic gcd estimate. Neither direction was proved
in this review.

The boundary-lattice route still lacks a quantitative useful-lift or
nonvanishing theorem. An integral pair image, nonzero weight vectors, or
a bound on real projected lifts does not supply that missing conclusion.
The polynomial and differential representations still introduce either
uncontrolled final arithmetic heights or additional values not known to
be rational under rationality of the target.

No numerical search was run and no compilation or computation is pending.
There is no completed informal argument awaiting formalization, and no
submission check was made in this continuation.

## Removed-prefix prime-factor review after relative norm detection

This continuation obtained no complete proof or disproof and no new Lean
lemma. The separate `LambertRelativeCombinationBound.lean` remains verified
auxiliary progress; Spec.lean still has its original sorry.

One alternative to the full raw row-annihilating polynomial was reviewed.
Let

    P_K=sum_(d=2)^K 1/(d!-1),
    beta_K=alpha-P_K,
    C_(K,H)=sum_(K<d<=H) sum_(1<=j<=floor(H/d)) 1/(d!)^j.

Then the exact residual is the sum of the geometric row tails for d>K,
while the denominator of the finite rational C_(K,H) divides H!. For
integer weights, an integral aggregate boundary B=sum w_j*C_(K,H+j)
gives the form

    A*beta_K-B,  A=sum w_j.

Under hypothetical rationality alpha=q, a prime in the REDUCED denominator
of beta_K, but not dividing A, would ensure this form is nonzero. A prime
factor of one individual factorial-minus-one denominator cannot be assumed
to survive in the reduced prefix or in beta_K. The existing cancellation
results remain essential.

There is also no proved bound providing a short aggregate-clearing vector
with A nonzero modulo such a prime. Even surjectivity of the full lattice's
coefficient-sum map modulo that prime would not bound the required lift.
Homogeneous pigeonholing can still return only vectors with A=0 or with A
divisible by the selected prime. A large prime compared with the allowed
coefficient sum would help only AFTER a nonzero coefficient sum was obtained.

Without additional cancellation information, nonzero rational forms here
have only the lower bound 1/(q.den*P_K.den). Removing the annihilating
operator's degree therefore does not justify dropping the reduced-prefix
height from the small-integer argument. No compatible nonvanishing and
height estimate was obtained. These are informal checks, not a new
impossibility theorem for this construction.

No numerical search or submission check was run. No complete informal
solution is awaiting formalization, and nothing is pending compilation.

## Positive-kernel iteration review

The exact physical-domain quadratic kernel was reconsidered as a possible
source of an iterated positive integer-form construction. Its existing
certificate gives only 0<4*alpha-5<1. The previously verified highest-column
obstruction prevents treating ordinary powers as valid telescoping kernels.

A repair by additional polynomial columns or by corrections concentrated
away from early physical rows was considered, but no construction preserving
positivity and producing integral final A,B with 0<A*alpha-B tending to zero
was obtained. Auxiliary Gram entries and polynomial coefficients need not
be integral; clearing all of their denominators is not a necessary step and
was not used as an impossibility argument. Conversely, increasingly close
normalized feasible boundaries do not by themselves control the final
integer-boundary rounding error.

No new Lean declaration, numerical experiment, or complete informal proof
resulted from this review. Spec.lean is unchanged with its original sorry.
No submission check was made and nothing is pending compilation.

## Review after the uniform filtered boundary-denominator theorem

This continuation obtained no proof or disproof of the original conjecture
and no new Lean declaration. Spec.lean remains unchanged with its original
sorry. The new filtered gcd and raw-boundary divisibility results remain
verified auxiliary results, not a small-form construction.

The following possible applications were reviewed:

* A short useful lift cannot be inferred from the small gcd of boundary
  differences. The existing affine-lift counterexample and zero-pair results
  still apply to the proposed generic inference. No additional bound using
  the exact factorial structure of the actual boundary vector was obtained.
* Enlarging the arbitrary-support detector's coefficient budget requires
  a new separation argument. A polynomial can almost cancel a geometric
  row over long supports once its coefficients reach the row's factorial
  scale; absence of exact divisibility is not a uniform separation estimate.
  The existing AnnihilatorHeight results already document this issue.
* The carry recurrence and its rationality-forced prime-gap pattern remain
  compatible with the verified tail bounds. No infinite violation was proved.
* Positive physical kernels and monic rising-factorial forms still lack a
  growing family whose primitive integral errors are nonzero and tend to zero.
  Root suppression by additional rising factors was considered informally,
  but no compatible all-row sign and height estimate was obtained. No new
  candidate was constructed or numerically tested.

A renewed attempt to retrieve erdosproblems.com/68 failed at DNS resolution;
no current external resolution or paper was retrieved. A local targeted
library search found no applicable result. No new numerical search, Lean
compilation, or submission check was run, and no process is pending. There
is no complete informal argument awaiting formalization.
