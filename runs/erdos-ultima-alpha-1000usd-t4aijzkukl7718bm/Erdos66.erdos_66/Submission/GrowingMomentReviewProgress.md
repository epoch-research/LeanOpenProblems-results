# Growing-order Gaussian moment bounds: verified limitations

## Original conjecture status

Erdos66.erdos_66 remains neither proved nor disproved. Submission/Spec.lean
is unchanged with its original import, statement, and sorry. No proof has
been submitted.

## New verified production files

* FiniteGrowingMomentCounterexampleExplore.lean
* NaturalGrowingMomentCounterexampleExplore.lean

Both compile and have current oleans. The corresponding
FiniteGrowingMomentAudit.lean and NaturalGrowingMomentAudit.lean audit nine
principal declarations. Their saved logs use only propext, Classical.choice,
and Quot.sound. Neither production file contains a sorry or a new axiom.

## 1. A finite cyclic counterexample to a generic growing-moment bound

For arbitrary lower bounds N0,K0 there is M>N0, a Boolean set B in ZMod M,
and k>K0 such that, for the ACTUAL mean mu=|B|^2/M,

    |mu/log M - 1/2| < 1/4,
    mu/2 <= k <= log M,
    |r_B(z)-mu| <= mu/16 for every z,

but

    (1/M) sum_z (r_B(z)-mu)^(2k) < k! mu^k.

Thus a growing-order Gaussian lower bound with even the coefficient k!
(not the larger (2k-1)!!) is false for general finite cyclic Boolean
convolutions at logarithmic mean. The moment order grows on the same scale
as the mean and log M; this is not merely the trivial failure at arbitrarily
large orders of a single fixed finite random variable.

The proof uses the previously checked sparse-start complete cyclic palette,
with a fixed relative tolerance, and the actual-mean tuning. It chooses
k=floor(mu). The elementary bound

    (k/exp(1))^k <= k!

follows from the exponential series. Since k>=mu/2 and exp(1)<3,

    (mu/16)^2 < k mu/exp(1),

so the pointwise error envelope bounds the whole moment strictly below the
claimed Gaussian lower bound.

## 2. An ordinary-integer counterexample with a global upper envelope

The existing upper-cap Baire construction gives one A with

    r_A(n)/log n <= 1 for every n,

arbitrarily late holes, and arbitrarily accurate annuli [N,RN]. The new
checked theorem shows that this A can be selected so that, for every N0,K0,
there are N>=N0 and k>K0, k<=log N, with

    (r_A(n)-log n)^(2k) < k! (log n)^k

SIMULTANEOUSLY for every n in [N,2N]. Thus a lower bound for the corresponding
annular average also fails. This is an example in the ordinary natural
numbers, not merely an artifact of finite cyclic torsion.

## 3. Actual natural-window mean, not only logarithmic centering

A second theorem uses the true average

    mu = (1/(N+1)) sum_(j=0)^N r_A(N+j).

Again one A has the exact global upper envelope and arbitrarily late holes.
For arbitrarily late [N,2N] and arbitrarily large k<=log N,

    log N/2 <= mu <= 2 log N,
    (1/(N+1)) sum_(j=0)^N (r_A(N+j)-mu)^(2k) < k! mu^k.

Here k=floor(log N). The flat annulus with tolerance 1/64 and the global
upper envelope put every count between (63/64)log N and log N+1. For large
N this interval is narrow enough that all errors from the ACTUAL mean are
at most mu/16, and k>=mu/2. The same scalar factorial comparison applies.

## Scope and implication for the main problem

These are counterexamples to proposed general moment inequalities, NOT to
the original existential conjecture. The natural sets have holes and are
not asserted to have the exact global counting asymptotic of a witness.
They do not refute a hypothetical stronger moment theorem whose assumptions
include additional global structure forced by the original limit.

The previously verified universal Abel second-moment bound, and its Jensen
consequence with coefficient c^k, remain valid. No factorial amplification
under the actual witness hypothesis was proved. It would be invalid to infer
such an amplification from Boolean coefficients, a global logarithmic upper
envelope, or arbitrarily accurate long annuli alone.

There is still no uniform sublogarithmic Boolean rounding, compatible
changing-palette construction, global repair theorem meeting the completion
criterion, or universal logarithmic fluctuation contradiction.
