# Concrete tracked degrees, excursions, and deterministic availability

This is NOT a settlement of Erdős 773. Spec.lean is unchanged and still has
its sole admission for 0<epsilon<=1/3. No actual Sidon exponent or endpoint
has improved. The strongest actual lower bound remains

    (5/4) N/(N log N)^(1/3).

## Verified modules and audits

Seven new modules, all built without warnings or admissions:

* GreedyTrackedState.lean: 298 lines, 11 printed audits.
* GreedyTrackedMoments.lean: 224 lines, 9 printed audits.
* GreedyTrackedVariance.lean: 179 lines, 6 printed audits.
* GreedyRecordedCrossing.lean: 148 lines, 6 printed audits.
* FiniteExcursion.lean: 136 lines, 3 printed audits.
* GreedyRecordedExcursion.lean: 157 lines, 6 printed audits.
* GreedyAvailableProfiles.lean: 218 lines, 8 printed audits.

The earlier FiniteFreedman now has six audits, including its added
first_crossing_deterministic. FiniteKernelCrossing now has eight audits,
including hit_or_bound. Including FiniteKernelChoices and GreedyFiniteKernel,
the combined 11-module audit has 75 checks, all depending only on propext,
Classical.choice and Quot.sound:

    /tmp/greedy-tracked-excursion-final-audit.log

None of these modules imports admitted Spec.lean. There are no admissions,
unsafe evaluation calls, or nonpermitted axioms in them.

## Concrete finite state and update

`GreedyTrackedState.State alpha M T` contains:

* chosen : Finset alpha;
* counts : Fin 3 -> alpha -> Fin (M+1);
* clock : alpha -> Fin (T+1);
* running : Bool.

The degree index j records residual size j.val+2, i.e. 2,3,4. `Tracked H T`
sets M=H.card; all incident degrees are bounded by H.card. The state type is
finite. Its DecidableEq instance uses Classical.decEq, not unsafe code.

`initial` has the empty carrier, actual initial degree values, zero clocks,
and running=true. The actions remain the original stopped-greedy actions:
choose uniformly from available vertices when Ready; otherwise use none.

For a some-w action, the carrier ALWAYS changes to insert w chosen. If
running=true and guard G(n,s) holds, records are updated for vertices that
remain available after that choice. Newly unavailable vertices retain their
previous degree snapshots and clock. If the guard fails, all records freeze
and running becomes false, but the carrier still performs the actual choice.
The none action leaves the entire state unchanged.

Thus neither a bookkeeping stop nor vertex death silently changes the
selected-set law. In particular, the memory lift never adds a Ready hold.

`Coherent` says that while running=true, every available vertex's stored
degrees are the actual degrees. `Valid H L n s` adds: all clocks are <=n, and
while running and Ready, all available clocks equal n. `update_valid` proves
preservation on supported actions for n<T. Frozen records at dead vertices
are not incorrectly equated to current degrees.

The new recorded `Reach` includes the horizon restriction n<T. It projects
to the old stopped-carrier Reach and implies Valid. `kernel_support` exposes
actual actions; `goodPath_terminal` and `goodPath_valid_terminal` extract an
actually reachable recorded terminal state from a support-respecting path.

`terminal_carrier` exactly identifies every carrier terminal expectation
with the old expectation. `hit_carrier` does the same for monotone selected-
set events. The all-subset common-neighbor/duplicate-error tail bounds can
therefore be used without assuming independent selections.

## Recorded one-step moments

For a profile f, define

    error_f(s,j,u) = stored_degree(s,j,u) - f(stored_clock(s,u)).

The clock is essential: f does not keep evolving after that record freezes.
`error_eq_live` and `live_degree_bounds` relate this stored observable to the
actual degree and profile at time n on a live available vertex.

Let Q=|available(I)|, S(u)=safeChoices(I,u), and R_j(u)=survivalDrift_j(u).
On a running, guard-satisfying Ready state, the checked conditional means are

    E[Delta recorded_degree_j(u)] = R_j(u)/Q,
    E[Delta error_f(u)] = (R_j(u)-|S(u)|*(f(n+1)-f(n)))/Q.

The factor |S(u)|, NOT Q, multiplies the profile change. A dead-on-this-step
vertex freezes the whole record, including its profile clock. Inactive or
guard-failed records have zero increments, drift, and second moment, even
while the carrier keeps choosing. Non-Ready supported transitions are the
identity on the whole state.

The exact recorded degree second moment is

    (1/Q) sum_{w in S(u)} (d_j(I+w,u)-d_j(I,u))^2.

The recorded error second moment is at most twice this, plus
2*(f(n+1)-f(n))^2. A safe raw-increment bound B gives an error-increment bound
B+|f(n+1)-f(n)| on every supported transition.

## Variance via total promotion/loss variation

The useful variance bounds assume that the ORIGINAL hypergraph is LINEAR,
not merely that its distinct edges meet in at most two vertices.

If each safe raw increment has absolute value <=B>=0, exact local balance
Delta+Lost=Promoted gives

    sum_safe Delta^2 <= B*(j*d_{j+1}(u) + sum_safe Lost_j(u,w)).

This uses Delta^2<=B*(Promoted+Lost) and exact total promotions j*d_{j+1}; it
does not use the too-large horizon-times-B^2 bound.

If neighboring d_2 values are <=h and common neighbor counts are <=C, then

    sum_safe (Delta d_2)^2 <= (C+1)*(2*d_3+h*d_2).

For j>=3 and all available d_2<=h>=0,

    sum_safe (Delta d_j)^2
      <= (h+1)*(j*d_{j+1}+(j-1)*(h+1)*d_j).

The higher-degree upper loss bound does not require a quantitatively small
common-neighbor hypothesis. Dividing these sums by Q gives actual recorded
conditional second moments. These remain one-step results, not integrated
budgets or verified typical profile bounds.

## Signed crossing bounds

`GreedyRecordedCrossing.MomentControl` collects explicit obligations:

* |sign|=1;
* G implies Valid through the horizon;
* nonnegative raw caps B(n) and variance bounds v(n);
* B(n)+|Delta f(n)|<=b;
* safe raw increments are bounded by B(n) on active Ready states;
* the explicit error second-moment expression is <=v(n) there.

`Control` extends it by requiring

    sign*(R_j(u)-|S(u)|*Delta f(n)) <= 0

throughout the active guard. This is a hypothesis, not a proved property of
a useful guard. Its sign may be 1 (upper) or -1 (lower).

`first_crossing` proves for a,b>0

    Pr[exists n<=T:
         sign*(error_f(s_n)-error_f(initial)) >= a]
      <= exp(-a^2/(4*(sum_{n<T}v(n)+b*a))).

Frozen and non-Ready cases are checked separately; the initial offset cancels
in every increment. `goodPath` and `reachable_good` give actual avoiding
paths and valid terminal states. They do NOT imply T carrier choices.

## Critical excursions without a fixed entrance time

`FiniteExcursion` works for arbitrary finite adaptive kernels and X(n,s).
Assume X(0,s0)<=0 and |Delta X|<=b. The mean condition E Delta X<=0 and
second-moment condition E Delta X^2<=v(n) are needed only where X(n,s)>=0.
For a>b>0, it proves

    Pr[exists n<=T: X(n)>=a]
      <= (T+1)*exp(-(a-b)^2/(4*(sum_{n<T}v(n)+b*(a-b)))).

The entrance overshoot is at most b. The T+1 factor accounts for all possible
excursion entrances and does not assume a deterministic entrance time.

Proof: compensate exp(theta*X) by the capped deterministic variance budget.
At nonnegative states its conditional mean does not increase. At negative
states, supported successors have X<=b, so the possible increase is at most
exp(theta*b). Adding (T-n)*exp(theta*b) gives a nonnegative potential with
nonpositive conditional drift. The finite Ville bound and optimization in
theta give the displayed inequality.

`GreedyRecordedExcursion.CriticalControl` weakens Control's drift obligation
to states where sign*error_f>=c. Applying the preceding theorem to
X=sign*error_f-c gives an actual recorded critical-interval crossing bound.

`Test` packages one profile, vertex, degree index, sign, critical level,
width, raw cap, increment cap and deterministic variance function.
`Test.Admissible` includes CriticalControl, width>incrementCap>0 and the
initial-below-critical-level condition. Its `cost T` is the displayed bound.
A sum of costs below one gives one actual path avoiding every test.

`simultaneous_with_auxiliary` also adjoins an arbitrary auxiliary first-hit
event with bound rho. It requires rho+sum(cost)<1. This can incorporate the
existing all-subset common-neighbor event through hit_carrier. Probabilities
are summed, not multiplied.

## Keeping the guard alive is a separate obligation

`goodPath_running_terminal` proves a pathwise implication: if every good
reachable running state before T implies G, an avoiding path starting with
running=true ends with running=true. `goodPath_full_run` additionally needs
good terminal running states to imply Ready. Only then does it give a full
T-vertex independent carrier.

`simultaneous_full_run` combines this with the finite family of excursions.
It keeps the guard and readiness implications explicit. It is a conditional
certificate, NOT an unconditional random-greedy running-time theorem.

## Deterministic availability from two-degree profiles

`GreedyAvailableProfiles.available_step` proves, in a linear hypergraph,

    Q(I+w) = Q(I)-1-d_2(I,w).

Consequently no additional concentration for Q is necessary if every chosen
vertex's two-degree already lies in a uniform deterministic interval.
Define

    remaining(H,f,n) = Q(empty)-sum_{k<n}(1+f(k)).

If lower(k)<=d_2(I_k,w_k)<=upper(k) at every genuine choice, summing the exact
increments gives

    remaining(H,upper,n) <= Q(I_n) <= remaining(H,lower,n).

`profile_step` checks the one-step implication. `goodPath_profile_terminal`
integrates along an actual recorded path, assuming the lower availability
budget remains at least L>0. That budget proves readiness at each step, so
none/hold actions are excluded rather than silently treated as choices.

`full_run_of_profiles` packages the result. If 1+upper(k)>=0, it suffices to
verify the terminal budget remaining(H,upper,T)>=L; all earlier budgets then
follow by monotonicity. The conclusion includes an independent carrier of
cardinality exactly T, two-sided Q bounds, running=true, Valid, and the good
terminal event. Its local-degree and guard implications remain hypotheses.

`reach_running_profiles` is the important noncircular invariant: if G itself
implies the local degree bounds, EVERY reachable running state has the Q
profile bounds. A running successor either is a genuine guarded update or
is an impossible hold (the previous lower budget already implied Ready).
Thus a future G may include the Q profile invariant, and proving good states
imply G can use this Reach invariant without assuming future success.

Finally `remaining_discrete` gives the exact telescoping identity

    remaining(H, k |-> q(k)-q(k+1)-1+e(k), n)
      = Q(empty)-q(0)+q(n)-sum_{k<n}e(k).

When q(0)=Q(empty) and e(k)<=E, the terminal lower budget is at least q(T)-T*E.
This can avoid a Riemann-sum error by choosing a discrete-difference local
profile. It does NOT establish the required local profile tracking.

## Remaining quantitative work and possible simplifications

No useful profiles, envelopes, guard, integrated variance budgets or final
sum-of-costs estimate have yet been verified. No concrete long-running-time
or logarithmic-gain independent-set theorem has been proved.

For a D-regular four-uniform linear hypergraph on V vertices, the usual
formal trajectories, with t=i*D^(1/3)/V and q=exp(-t^3), are

    Q = V*q,
    d_2 = 3*D^(1/3)*t^2*q,
    d_3 = 3*D^(2/3)*t*q^2,
    d_4 = D*q^3.

These formulas and their quantitative validity are NOT established here.
A possible next simplification is to use growing error envelopes and the
stronger global Control instead of critical excursions. Drift errors might
be absorbed by an envelope derivative at every guarded state. This requires
actual inequalities, not an assumption of self-correction.

For logarithmic time, consistent envelope scales are roughly

    E_j ~ D^((j-1)/3-delta) q^(j-2) exp(K*(t^3+t)),
    E_Q ~ V*D^(-delta) exp(K*(t^3+t))/(1+t^2).

Using E_Q<=T*sup(E_2) too crudely introduces extra powers of t in the drift
errors. An integrated envelope or the discrete-difference profile identity
may avoid this. All such estimates remain proposed work.

Even a completed generic logarithmic-gain theorem remains at the 2/3
square-Sidon exponent scale. It does not yield the square-specific
near-linear selection needed for any fixed epsilon<1/3. The arithmetic
fiber/factorization review in this continuation found no new valid selector
and no fixed-power upper bound disproving the conjecture.

## Main file

Latest check:

    /tmp/spec-recorded-excursion-check.log

Spec.lean has 2033 lines and its sole admission at line 2031. Its SHA-256 is

    917b6c178fa6b0ff7325ec3027dda121a1138cc1198ba712cac9352f5dca5c14

The original import and conjecture statement have not been modified. No
proof or disproof has been submitted.

## Subsequent numerical-trajectory update

The proposed profiles and matched envelopes above now have verified
calculus and finite-increment bounds. GreedyPhysicalStep derives the six
actual signed drift inequalities under explicit scalar conditions, and
GreedyUniformHorizon verifies those conditions throughout a horizon under
m>=exp(10000*(1+tau)^3), d=m^4, rho=1/m, V>=m^12, C<=16*m, K=4000.
See GreedyNumericalTrajectoryResearchNotes.md for the nine new modules and
exact scope. The remaining guard instantiation, integrated variance/tail
estimates, unconditional running time and square-specific exponent gap
remain unresolved. No new actual Sidon lower bound has been obtained.
