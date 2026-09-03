# Finite adaptive first-crossing bounds and the greedy-kernel bridge

This continuation does NOT settle Erdős 773. Spec.lean remains unchanged,
with its sole admission for 0<epsilon<=1/3. The strongest actual square-Sidon
lower bound is still (5/4)N/(N log N)^(1/3); neither the exponent nor the
endpoint improved.

## Four new verified modules

* FiniteKernelCrossing.lean: now 8 printed audits (including hit_or_bound).
* FiniteFreedman.lean: now 6 printed audits (including first_crossing_deterministic).
* FiniteKernelChoices.lean: 3 printed audits.
* GreedyFiniteKernel.lean: 9 printed audits.

The original 24 audits, and the two added audits, use only propext, Classical.choice, and Quot.sound. All four
modules are built and compile without warnings or admissions. None imports
Spec.lean. Combined audit:

    /tmp/finite-freedman-greedy-final-audit.log

## Finite kernels and actual paths

A Kernel has nonnegative real transition weights K(x,y) and row sums one.
Its `avg` functional is the corresponding finite weighted sum. Kernels may
vary with time, and the next distribution may depend arbitrarily on the
state; independence of successive transitions is not assumed.

`hit K P n h x` is defined recursively as the probability of hitting P at
some time in the inclusive interval [n,n+h], starting at x at time n. Its
bounds 0<=hit<=1 are proved. `GoodPath` recursively records an actual
positive-support transition at each step, with every visited state good.
`goodPath_of_hit_lt_one` extracts such a path from hit<1.

`hit_le_potential` is a finite Ville-type bound. If F>=0, its conditional
average does not increase, and every bad state has F>=A>0, then

    hit K P n h x <= F(n,x)/A.

The hypotheses are needed only through the specified finite horizon.

`hit_union_bound` and `simultaneous_goodPath` apply to finitely many
first-crossing events. They do not merely control terminal events.
`terminal_eq_hit_of_preserved` identifies the first-hit probability with the
terminal indicator expectation when the event is preserved by every
supported transition.

## Variance-sensitive first-crossing theorem

Write Delta X = X(n+1,y)-X(n,x). At every state before the horizon, assume:

* |Delta X|<=b on positive-weight transitions;
* conditional E[Delta X]<=0;
* conditional E[(Delta X)^2]<=v(n,x);
* V(n+1,y)>=V(n,x)+v(n,x) on positive-weight transitions.

No lower increment bound stronger than the absolute bound is assumed, and
no independent-increment hypothesis is used. X(0,x0)=V(0,x0)=0.

For theta>=0 with theta*b<=1, `first_crossing_exponential` proves

    Pr[exists n<=T: X(n)>=a and V(n)<=s]
        <= exp(-theta*a+theta^2*s).

For b>0, a>0, s>=0, choosing theta=a/(2(s+b*a)) gives the checked bound

    Pr[exists n<=T: X(n)>=a and V(n)<=s]
        <= exp(-a^2/(4(s+b*a))).

This is `first_crossing_bound`. The variance cap is tested at the crossing
time, not only at the terminal time. `goodPath_of_variance_control` also
extracts an actual path with no such crossing. It does NOT establish that
V remains below s; a path may avoid the event by exceeding the variance
budget. Applications must prove a variance bound separately.

The proof uses the existing real exponential estimate

    |exp(z)-1-z|<=z^2       for |z|<=1.

It gives conditional E exp(theta*Delta X)<=exp(theta^2*v). Consequently
exp(theta*X-theta^2*V) has nonpositive conditional drift, and the finite
potential crossing bound applies. All analytic and kernel manipulations
are checked in Lean.

## Uniform choices with multiplicity

`FiniteKernelChoices.ofChoices` pushes uniform choices from a nonempty
finite action set A(x) through an arbitrary next-state map. A target state
y has weight

    #{a in A(x): next(x,a)=y}/|A(x)|.

The next-state map need not be injective. Row normalization, the exact
average formula, and positive support iff an action realizes the target
are proved. This avoids silently dropping multiplicity when states merge.

## Exact connection to stopped greedy selection

At selected set I, the action set is

* `some v` for each available v, if Ready(H,L,I);
* only `none`, otherwise.

The carrier moves to insert v I or holds at I, respectively. The resulting
finite kernel has average exactly equal to `StoppedGreedyMoments.step`.
Its positive-support relation is exactly the existing choose/hold relation,
and good kernel paths project to actual `Reach` states.

`goodPath_independent` retains the conclusion

    |I|=t OR Q(I)<L.

Thus concentration-path extraction does NOT itself exclude early stopping.

## Finite auxiliary memory interface

`liftedKernel` sends the same actions through any update on a finite state
type with a selected-set projection `carrier`. The checked compatibility
hypothesis is

    carrier(next(n,s,a)) = move(carrier(s),a)

for every supported action. Under this hypothesis:

* projected one-step averages equal the stopped-greedy step;
* supported transitions project to actual greedy transitions;
* terminal expectations of every carrier observable agree with the original
  `StoppedGreedyMoments.expectation`, when the initial carrier is empty;
* for any monotone selected-set event P, its first-hit probability in the
  lifted process equals the original terminal expectation of its indicator.

The last statement is `lifted_hit_of_monotone`. In particular, the previously
proved all-selected-subset duplicate/common-neighbor events can be used
in a valid finite-memory lift after proving their elementary monotonicity.
No new independence argument is required.

The compatibility hypothesis does NOT permit adding arbitrary carrier
holds while Ready remains true. If a future analysis introduces an extra
stop, it must justify a new projection comparison, or continue the original
carrier process while freezing only its auxiliary memory. This distinction
must not be skipped.

## Remaining implementation and mathematical gaps

UPDATE: GreedyTrackedState now implements the concrete finite representation,
with selected carrier, bounded degree snapshots, last-update clocks and a
running flag. Its coherence, supported updates, death freeze, guard freeze,
actual recorded-state reachability, and exact carrier-law transfer are proved.
See GreedyTrackedExcursionResearchNotes.md for the subsequent seven modules.
The guard freezes memory, not the carrier; arbitrary extra Ready holds are
still not allowed.

UPDATE: Actual recorded-error increments, drifts, and conditional second
moments are now proved. Signed first-crossing and critical-excursion bounds
apply under explicit deterministic controls. A local two-degree envelope now
gives deterministic two-sided available-cardinality bounds and a conditional
full-run theorem. Still missing: useful quantitative profile/error functions,
verification of the control hypotheses, deterministic variance budgets small
enough for the required simultaneous estimates, and an actual long-run
instantiation. No logarithmic-gain independent-set theorem has been obtained.

The fiber/factorization review found no new square-specific selector. Even
a completed logarithmic-gain greedy theorem would remain at the 2/3 scale
and would not settle the required near-linear exponent. No fixed-power
upper bound disproving the original conjecture was found.

## Main file status

Latest main check: /tmp/spec-finite-freedman-check.log, still with the expected
admission warning. Spec.lean SHA-256 remains
917b6c178fa6b0ff7325ec3027dda121a1138cc1198ba712cac9352f5dca5c14.
The conjecture statement and its import were not modified. No proof was
submitted.

## Deterministic-budget and excursion updates

`first_crossing_deterministic` caps the cumulative deterministic variance
budget at the horizon. If v(n)>=0 and E[Delta X^2]<=v(n), the crossing bound
has sum_{n<T}v(n) in place of s and no variance event is needed.
`hit_or_bound` is the binary first-crossing union bound.

`FiniteExcursion` adds a separate theorem needing nonpositive mean only
where X>=0. If X(0)<=0, |Delta X|<=b, a>b>0, and the conditional second
moment is <=v(n) in that region, then

    Pr[exists n<=T: X(n)>=a]
      <= (T+1) exp(-(a-b)^2/(4*(sum v + b*(a-b)))).

The T+1 factor covers all possible new excursions. No fixed entrance time
or independence assumption is made. The updated combined 11-module audit
has 75 permitted-axiom checks:

    /tmp/greedy-tracked-excursion-final-audit.log

The latest unchanged-main check is /tmp/spec-recorded-excursion-check.log.
No proof of the original conjecture has been submitted.

The subsequent numerical calculus is documented in
GreedyNumericalTrajectoryResearchNotes.md. Explicit analytic profiles and
uniform one-step scalar conditions are now verified on logarithmic-cube-
root horizons. This still has not supplied the integrated variance and
simultaneous failure estimate, nor an unconditional long run. The updated
combined twenty-module audit has 118 permitted-axiom checks in
/tmp/greedy-concentration-trajectory-combined-audit.log. Spec.lean is unchanged;
latest main check is /tmp/spec-numerical-trajectory-check.log.
