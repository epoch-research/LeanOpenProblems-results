# Matching local collision powers and a whole-interval alteration limitation

This does NOT settle Erdős 773. Spec.lean is unchanged with its sole admission
for 0 < epsilon <= 1/3. No proof submission has been made.

## Verified local family

File: LocalCollisionLower.lean

For all positive integers K,T, put

  L=16 K^2 T, H=32 K T.

The public theorem local_count_lower proves at least K T^2 distinct strictly
ordered four-root square-sum collisions inside [L,L+H]. The equivalent
scaled inequality, in scaled_count_lower, is

  H^3 <= 2048 L E(L,H).

This matches the H^3/L power scale of the previous uniform upper estimate,
up to constants and subpower divisor factors. It is genuinely a thin-
interval family when K grows, since H/L=2/K. Taking K=T makes H comparable
to L^(2/3), rather than comparable to L.

## Exact parameters and injectivity

Choose

  K <= k <= 2K-1, 1 <= t <= T, 0 <= j < T,
  m=floor((L+t)/k)+1+j,
  a=k*m-t, z=2*t*k, y=m-z.

All these natural subtractions are justified in the proof. In particular
z,y,t are positive, a>=L, and

  2t(a+t)=z(z+y).

The resulting ordered roots are

  a, a+z+2t, a+z+2t+y, a+2z+2t+y.

Their squares collide. The estimates a<=L+2KT, z<=4KT, m<=18KT place the
largest root below L+32KT.

The earlier ordered encoding recovers (a,t,z) from a collision. Since
z=2tk and t>0, it recovers k; then a+t=k*m recovers m, and finally j. Thus
all K*T*T parameter triples give distinct ordered collisions. No assumption
of uniform distribution of divisors or a numerical count is used.

## Full-interval consequence

collisions_mono records interval monotonicity. With K=1 and T=floor(N/48),
global_count_lower gives, for N>=96,

  N^2 <= 9216 E(1,N-1).

Here E(1,N-1) counts strictly increasing roots in [1,N] satisfying

  a^2+d^2=b^2+c^2.

It is not a bound on the maximum Sidon-subset size.

## Limitation on the displayed alteration expression

For every p>=0 and N>=96, alteration_expression_upper proves

  (p*N-p^4 E(1,N-1))/4 <= 8*N^(2/3).

For p*N^(1/3)<=32, the positive term alone gives this bound. For larger p,
the quadratic collision lower bound makes the displayed expression
nonpositive. The statement applies in particular to sampling probabilities
0<=p<=1.

IMPORTANT: this is an upper bound on one lower-bound EXPRESSION. It is NOT
an upper bound on the actual Sidon maximum, NOT a disproof of Erdős 773,
and NOT an exclusion of more sophisticated probabilistic constructions.
Choosing a near-linear subset with a much smaller induced collision count
remains completely open. The earlier low-collision equivalence is not
settled by any of these count lower bounds for whole intervals.

## Verification and main status

All five printed audits use only propext, Classical.choice, Quot.sound.
The file has no admissions or warnings. Its olean has been built.

Log: /tmp/local-collision-lower-final.log
Main check: /tmp/spec-local-lower-check.log

Spec.lean retains the same hash:
917b6c178fa6b0ff7325ec3027dda121a1138cc1198ba712cac9352f5dca5c14.

No actual Sidon lower exponent or fixed-power upper exponent was improved.
