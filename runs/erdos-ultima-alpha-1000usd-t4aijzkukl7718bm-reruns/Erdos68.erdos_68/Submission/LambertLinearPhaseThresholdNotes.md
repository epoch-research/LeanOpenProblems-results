# Full phase mass gives a linear nonvanishing threshold

Verified auxiliary progress, NOT a proof or disproof of Erdos 68.
`Spec.lean` remains unchanged with its original `sorry`.

All three new files compile without warnings and have built oleans:

* `LambertCyclicMass.lean` (221 lines)
* `LambertPhaseMassBounds.lean` (150 lines)
* `LambertLinearPhaseThreshold.lean` (378 lines)

They contain no proof holes. All eight printed principal axiom audits list
only `propext`, `Classical.choice`, and `Quot.sound`.

## Main theorem

Let d>=12 and let w_0,...,w_M be a nonzero finite integer vector, with
|w_j|<=Q and 4Q<=d!. For the existing full-target raw row-cancelling tail,

    H>=420*d
      ==> some H<=n<H+d has
          sum_(j=0)^M w_j*rawTail(d-2,n+j) != 0.

This is `LambertLinearPhaseThreshold.linear_raw_detection_nonzero`.
The support length M is unrestricted. The starting index is independent
of both M and Q and is linear in d. The preceding verified threshold was
(d+1)*(3*log2(d)+136). The new constant is not claimed to be optimal or to
improve that previous numerical bound for every d.

## Three analytic improvements

Write lambda_d=(d!)^(1/d), c_h=sum_(j congruent h modulo d) w_j/lambda_d^j,
and mass(f)=sum_h |f_h| over a full period.

1. If w_0!=0, then

       sum_j |w_j|/lambda_d^j <= 3*mass(c).

   The late weighted mass j>=d is at most 1/2. The first block occupies
   distinct residue classes, so its mass is at most mass(c) plus that late
   mass. Also mass(c)>=||c||_infinity>=1/2. This avoids the factor d from
   the earlier supremum-norm comparison.

2. The geometric row's normalized periodic model has the EXACT mass

       mass(rowModel_e)=1/(lambda_e-1).

   Summing its jump identity proves this equality. Cyclic row-cancelling
   operators multiply its mass by at most the already bounded product
   exp(12). Any d<=e consecutive output phases occupy distinct positions
   in a full e-period. Consequently

       sum_(h<d) lambda_d^(H+h) * |Q_K(E) r_e(H+h)|
         <= exp(12)/(lambda_e-1) * (lambda_d/lambda_e)^H.

   This is `LambertPhaseMassBounds.row_window_mass_bound`.

3. For the near rows d<e<=2d, adjacent rate estimates telescope. If
   H>=(2d+1)*L and 0<=r<=d, then

       (lambda_d/lambda_(d+r))^H <= 2^(-L*r).

   Thus their masses form a geometric sum rather than d copies of a
   uniform worst-case estimate. For L=140 and H>=420d, their complete
   window mass is less than exp(-48)/(12d). The far rows e>=2d+1 satisfy
   the same bound using the earlier (3/4)^H estimate and d<=2^d.

The combined remainder mass is therefore less than exp(-48)/(6d).
After applying arbitrary weights, the first estimate bounds this by
exp(-48)*mass(c)/(2d). The first row's full-window mass is at least
exp(-48)*mass(c)/(lambda_d+1), from the cyclic inverse and lower product
bounds. Since lambda_d+1<2d and mass(c)>0, the full target cannot vanish
at every phase. Leading zero weights are trimmed and the window is
translated back exactly.

## Remaining arithmetic gap

The theorem does NOT assert that the detected output boundary is integral.
It does not select the particular phase cleared by a scalar lattice vector.
The same coefficient-height restriction 4Q<=d! remains essential.

The existing simultaneous-clearing estimate retains endpoint

    T=H+(D-1)+(d-1)+K(K+3)/2,  d=K+2.

For D~b*K^2 and now H=O(K), its sufficient counting budget still has leading
logarithmic size (2+1/(2b))*K*log K, whereas log Q is limited to
K*log K+O(K). This informal leading-order check is unchanged from the
height-independent logarithmic threshold: both starting-index choices are
of smaller order than K^2. It is not an impossibility theorem for other
clearing constructions or other choices of weights.

Growing coordinate allowances were also reconsidered informally. A
separation estimate based on the first coefficient cannot automatically
be applied after trimming leading zeros: later coordinates have larger
allowances, and shifted exact row-annihilating factors may then fit. No
short integral lift with the necessary nonvanishing property was obtained.

No new determinant or numerical experiment was run. The earlier completed
Hankel tests were checked rather than repeated. No complete informal proof
or disproof of the original conjecture has been found. No submission check
was made, and no computation or compilation is pending.
