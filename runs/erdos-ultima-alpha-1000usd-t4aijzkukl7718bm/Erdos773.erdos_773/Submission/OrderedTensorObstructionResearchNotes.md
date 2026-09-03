# Ordered digits with arbitrarily many common power moments

The original Erdős 773 conjecture remains UNSETTLED. Spec.lean is unchanged
and still has its one admission at line 2035. No proof submission was made.
This work strengthens a construction-specific obstruction, not an upper
bound on arbitrary square-Sidon sets.

## New verified modules

* Submission/TensorMomentBalance.lean
* Submission/OrderedTensorObstruction.lean

Both compile without warnings or admissions and have built oleans. Their
printed principal audits use only propext, Classical.choice, Quot.sound.
They import only clean auxiliary developments, not Spec.lean.

Logs:
  /tmp/tensor-moment-balance.log
  /tmp/ordered-tensor-obstruction.log

## Closed theorem

Erdos773.OrderedTensorObstruction.arbitrary_ordered_moments proves that for
EVERY natural k there are a positive D with

  D <= 16 (k+1)^2 (log2(k+1)+1)

and four fixed digit words P,Q,R,S indexed by Fin D x Fin D such that:

* Digits are strictly increasing in ordinary radix position i+D*j.
* For EVERY n<=k, the four sums of nth POWERS OF DIGITS are equal.
* At EVERY integer radix B>=radix(D), all digits are positive and <B,
  and the four evaluated square values are not Sidon.

These are digit-value power moments, NOT the positional moments
sum_i digit_i*i^n from the earlier binary-word modules.

position_bijective proves that i+D*j enumerates exactly the D^2 positions
0,...,D^2-1. gridValue_lt proves the actual root height is <B^(D^2) for
canonical words. gridValue_pos proves positivity. Thus these are genuine
ordinary integer digit encodings, not an arbitrary additive model.

The number of positions is at most
256 (k+1)^4 (log2(k+1)+1)^2, by squaring the displayed bound. That last
numerical reformulation is not packaged as a separate theorem.

The general theorem proves a nontrivial Sidon obstruction, allowing a
possible diagonal pair. It does NOT assert that all four roots are pairwise
distinct. The earlier concrete nine-digit module does separately prove four
distinct roots.

## Algebra and finite moment balance

Balanced(a,f,k) means sum_i a_i^j f_i=0 for every j<k. Signed coefficients
are in {-1,0,1}. For odd m, f_i^m=f_i. Binomial expansion therefore shows

 sum_i (a_i*x+f_i*y)^n = sum_i (a_i*x-f_i*y)^n,  n<=k.

This is moment_flip. It applies independently in the two tensor factors.
The tensor digit is

  T(i,j)=(a_i+f_i)d_j+(a_i-f_i)g_j.

Its two sign reversals produce the other three words. four_moments proves
that all their power moments through k agree. affine_balanced proves that
balance survives arbitrary affine changes of background coordinates.

exists_balanced_signs supplies a nonzero bounded-sign vector of polynomial
length, using the already verified SmallSignJets theorem and Euler-derivative
conversion of vanishing at X=1 to signed positional moments. This discharges
the balance assumptions rather than merely retaining them as hypotheses.

## Positive strict ordering

Set

 E=100D^3+10D+10D^2+1, T=E+10,
 a_i=T+10i, d_j=T+10D*j.

For any signed f,g in [-1,1], the tensor digit at position h=i+D*j lies
between

 T^2+(10h-2)T-E  and  T^2+(10h+2)T+E.

Because T=E+10, these bands are strictly separated at distinct positions,
and all their values are positive. The explicit adequate radix is

 radix(D)=T^2+(10D^2+2)T+E+1.

## Actual norm identity and nontriviality

The exact evaluation factors as

  (A+F)Dval+(A-F)G,

where A,F are fine-factor evaluations at B and Dval,G are coarse-factor
evaluations at B^D. The standard tensor norm identity proves equality of
the two square sums. Signed radix uniqueness proves F and G are nonzero.
Positive coefficient differences imply A-F>0 and Dval-G>0. Consequently
one root differs from both opposite-side roots, proving the square values
are genuinely non-Sidon.

## Scope limits

The discrepancy is formally zero as a polynomial, at every radix. These
words do NOT satisfy the Gaussian-Eisenstein formal Sidon conditions; in
particular no monic leading coefficient and prescribed constant coefficient
are asserted. Their complete digit histograms need not coincide. No
pairwise coprimality or primality is asserted.

This refutes a blanket sufficient condition using strict digit order and
any fixed number of power moments. It does not show that every moment class
is bad, or exclude a specially selected large Sidon subclass. It gives no
new unrestricted lower exponent and no fixed-power upper bound. The actual
remaining range of the original conjecture is still 0<epsilon<1/3, with the
separate coefficient-one endpoint not reconsolidated into the current main
file.

Spec.lean SHA-256 remains
f019ff3791c89bbea24fd9b031eb92f7b676baa4b1ff9cebe9f2356121aa6ff0.
