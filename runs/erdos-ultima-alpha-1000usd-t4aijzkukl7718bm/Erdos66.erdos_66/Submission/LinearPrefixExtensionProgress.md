# Conditional first-window extension with a prescribed old prefix

## Original conjecture status

The conjecture is still unproved and undisproved. Spec.lean is unchanged
with its original sorry. No valid proof or disproof has been submitted.

## Verified production files

* LinearPrefixExtensionExplore.lean
* LogarithmicPrefixExtensionExplore.lean

Both compile and have current oleans. LinearPrefixExtensionAudit.lean audits
12 declarations; its saved log uses only propext, Classical.choice, and
Quot.sound. Neither production file contains a sorry or a new axiom.

## The old prefix is not resampled

Fix B subset [0,N), and choose Boolean coordinates omega_i for candidate
new points N+i, i<L. At every n<2N the exact representation count is

    r_(B union F)(n)=r_B(n)+sum_i w(n,i) omega_i,

where w(n,i) is 2 if N+i<=n and n-(N+i) is in B, and zero otherwise.
There is no new/new contribution in this window.

With probabilities p_i, define the NEW mixed mean

    m(n)=sum_i w(n,i) p_i.

The old/old term r_B(n) is deterministic and is not charged as random
variance. Using the existing weighted-bit MGF and summed-tail selector gives
an extension F subset [N,N+L), disjoint from B, whenever

    m(n)<=V(n),  0<epsilon<=1,
    sum_(n in S) 2 exp(-epsilon^2 V(n)/8)<1,

for a finite S with every n<2N. The output satisfies

    |r_(B union F)(n)-(r_B(n)+m(n))|<epsilon V(n),   n in S.

Every old membership bit and every representation count below N is kept
EXACTLY. This is stronger than resampling an unrelated finite approximation,
but it is conditional on the displayed mean and tail budgets.

## Explicit predictive-profile requirement

If also

    |r_B(n)+m(n)-q(n)|<=E(n),

then the same extension satisfies

    |r_(B union F)(n)-q(n)|<E(n)+epsilon V(n).

The predictive-mean condition is an explicit hypothesis. Past accuracy,
a global upper bound, or a counting-function profile is not silently used
to infer it.

## Local mean and deterministic capacity

If p_i<=v with v>=0, then

    m(n)<=2v * #{a in B : a<=n-N}.

Only the early old points can pair with a new point at n. For EVERY finite
extension F above N, independently of any randomness,

    r_(B union F)(n)
      <= r_B(n)+2 #{a in B : a<=n-N},       n<2N.

At n=N this gives r_(B union F)(N)<=r_B(N)+2. A large deficit at the first
new target is therefore already irreversible by a monotone tail extension.

## Explicit logarithmic specialization

For N>=3 and S subset [N,2N), the union budget is verified whenever

    V(n)=b log n,  b>=0,  epsilon^2 b>=16.

Indeed each tail is at most 2/N^2 and |S|<=N, so their sum is less than one.
If the predictive bias is at most a log n about c log n, the selected
extension has

    |r_(B union F)(n)/log n-c|<a+epsilon b,  n in S.

This is a sufficient fixed-tolerance extension theorem, not a lower bound
on all possible extension methods.

## Remaining issue

No old-prefix invariant has been constructed that supplies the required
predictive bias through successive windows with vanishing error at one
fixed c. The concentration criterion also still has a fixed mean-scale
threshold: when b is comparable to c, taking epsilon to zero with c fixed
does not meet epsilon^2 b>=16.

Using a very short target window can reduce the total tail budget, but by
itself it does not control the accumulated predictive errors from earlier
choices. Nor does this first-window result control the new/new terms in the
next window. These missing assertions cannot be supplied by repeated
application of the conditional theorem alone.

Thus the review has not yielded the cutoff-independent finite feasibility,
compatible infinite construction, or universal contradiction required to
settle Spec.lean.
