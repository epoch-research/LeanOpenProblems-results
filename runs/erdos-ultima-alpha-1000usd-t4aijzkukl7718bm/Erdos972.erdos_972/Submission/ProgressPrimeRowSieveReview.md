# Prime-row sieve review — no settlement

Spec.lean remains unchanged with its original sorry. This review adds no
Lean declaration, no proved prime-pair lower bound, and no counterexample.

The existing full-row bound is R_d <= M log N under its documented
hypotheses. A possible improvement was considered by writing a row input
as ceil((d/alpha)*k), with k the complementary divisor, and approximating
d/alpha by a rational. On a short progression in k, the ceiling then lies
in a small number of affine progressions. An upper sieve for those
progressions could potentially exploit the primality of the input rather
than bounding every logarithmic weight independently.

No uniform arithmetic-progression sieve estimate or resulting prime-row
bound was proved or imported in this review. Local factors from the
progression coefficient must be retained; they cannot be assumed uniformly
bounded.

Even an idealized replacement R_d <= C*M would only change the existing
block argument to an energy of order N*M. For a block of length about N/M,
the elementary Cauchy--Schwarz estimate with coefficients of bounded size
would still be of order N, with no established constant below the needed
threshold. Thus removing the logarithmic loss alone would not establish
the signed strict lower gap. Neither this scaling observation nor the
unproved sieve proposal is a settlement.

The previous rational-approximation and rational-dilation reviews also
produced no new theorem. In particular, the proved signed Mobius dilation
comparison is not a prime-prime correlation estimate. No propagation of
finite prime-pair sets between rationally related slopes was established.

No incomplete proof has been resubmitted in these reviews.
