# Evaluated large-block first moment — not a settlement

Spec.lean remains unchanged and unresolved. No prime-pair lower bound or
irrational counterexample has been obtained.

New verified file: LargeDivisorBlockMain.lean.
Namespace: Erdos972LargeDivisorBlockMain.
All principal declarations compile and audit with only propext,
Classical.choice, and Quot.sound.

## Evaluation of the main term

The file proves the exact clipped-harmonic identity

    sum_{1<=k<=K} [min(1,2k/x)-min(1,k/x)]/k
      = H_floor(x)-H_floor(x/2)
        +(2*floor(x/2)-floor(x))/x,

for x>0 and floor(x)<=K. The expression on the right tends to log 2 as
x tends to infinity. The harmonic-number and floor-ratio limits used here
are available in Mathlib.

The exact outputPrefix from ExactLargeDivisorFirstMoment differs from
m/alpha by at most one when alpha>=1. Its clipped version has the same
error bound. An affine form of the PNT is also proved:

    for every eta>0 there is C>=0 with
    |psi(X)-X| <= eta*X+C for all natural X.

Write B(alpha,N,D,K) for the preceding file's blockChebyshevMain, and L
for the same sum with psi(endpoint) replaced by the unrounded real
endpoint. The new quantitative comparison is

    |B-L| <= 3*eta*D*K/alpha + 2*K*(eta+C+1).

Moreover, L=N*harmonicBlockProfile(alpha*N/D), under the documented
positivity and complementary-divisor size conditions.

## Actual prime-weighted first moment

`exists_block_firstMoment_log_two` proves that for every alpha>1
irrational, epsilon>0, and initial bound, there are a larger positive u and

    N=u^6, v=root64(u), D=blockStart(alpha,N,v)

with 0<D<N and

    |sum_{D<d<=2D} R_d - N*log 2| <= epsilon*N,

where R_d is the actual prime-input divisor row with primeWeight=log p.
There is no unproved distribution hypothesis. This is an arbitrarily-large
selected-scale theorem, not a claim of a limit through all N.
Only D<N is asserted; the whole block need not lie below N in the statement.

## Improved explicit dispersion at a common scale

`exists_evaluated_block_dispersion` combines that first moment with the
finite multiplicity bound R_d<=v*log N, at the SAME selected scale. It gives

    sum_{D<d<=2D} (R_d-psi(N)/d)^2
      <= N*v*log N*(log 2+epsilon)
         -(psi(N)/D)*((log 2-epsilon)*N)
         +psi(N)^2/(2D).

In particular, the large coefficient 14*alpha+15 from the older explicit
second-moment bound is replaced in the leading term by log 2+epsilon.
The logarithmic loss is still present. No intersection of unrelated
existential good-scale sets is assumed.

## Definite centering correction

`exists_negative_centering_correction` separately proves, at arbitrarily
large explicit good blocks,

    sum_{D<d<=2D} (R_d-psi(N)/d)^2
      <= sum_{D<d<=2D} R_d^2 - N^2/(8D).

It uses S=sum R_d >= (2/3)N and

    (15/16)N <= psi(N) <= (17/16)N.

This is a negative correction relative to the RAW second moment. It is
NOT the signed four-factor lower gap required by the conjecture. Do not
confuse those two statements.

## Remaining gap

The available dispersion bound still has order N*v*log N. The retained
negative correction has order N^2/D, so it does not remove the logarithmic
loss or yield the needed signed prime-pair correlation. Intermediate and
balanced factor ranges remain unresolved as well. No proof was submitted.

## Follow-up coefficient/range review — no new theorem

A subsequent check against PrimeFactorRemainder, FourFactorDiagonalSplit,
and GrowingTypeIIReduction did not supply a settlement or a new Lean
result. The remaining off-diagonal uses the actual divisorCoeff(U,m)
and divisorCoeff(U,k), with prime factors p and q and the condition
k*q=floor(alpha*m*p). It also includes balanced factor ranges not covered
by the new small-complementary-divisor block theorem.

Even for coefficients bounded by one, the direct Cauchy--Schwarz use of
an O(N*v*log N) energy over O(N/v) divisors gives an O(N*sqrt(log N))
upper bound, not the needed strict order-N gap. This scaling check does
not prove that the actual signed error is large; it shows only that this
upper bound does not establish a sufficient saving. No unsigned moment
bound was promoted to a signed cancellation theorem, and no compatibility
between separate existential good-scale constructions was assumed.
