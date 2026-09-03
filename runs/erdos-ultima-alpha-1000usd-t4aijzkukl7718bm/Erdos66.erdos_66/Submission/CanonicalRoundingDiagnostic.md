# Finite diagnostic of the canonical harmonic rounding

## Original conjecture status

The conjecture remains neither proved nor disproved. `Submission/Spec.lean`
is unchanged and still contains its original `sorry`. No proof was submitted.
This diagnostic is not a theorem about the infinite canonical set.

## Candidate examined

The existing fractional profile p has

    sum_(i+j=n) p_i p_j = H_(n+1).

Its generating series is the formal square root of the harmonic-coefficient
series. The existing canonical rounding is

    n in A iff floor(sum_(i<=n) p_i) - floor(sum_(i<n) p_i) = 1.

Its prefix discrepancy is already proved to be at most one. What is not
proved is the required sublogarithmic quadratic convolution error.

`Diagnostics/canonical_profile_fft.py` computes the profile using Newton
iteration on power series and FFT convolution, then applies these floor
decisions. The decisions use floating point, not certified intervals.

## Finite observations

At N = 1,048,576 the generated prefix has 4,299 selected points.
In the last dyadic window [524288,1048576]:

* 402 targets have zero representations in this computed prefix;
* the largest observed r(n)/log n is approximately 3.41801238;
* this maximum occurs at n=699495 with r(n)=46;
* n=526095 is one of the observed holes.

Both the float64 and extended-precision runs gave exactly the same membership
bits. Their cumulative profiles differed by at most 1.536e-9. The smallest
noninitial distance to an integer in the extended-precision cumulative
profile was approximately 4.231e-7. The largest residual of its profile
self-convolution about the harmonic coefficients was approximately 3.865e-15.
These are numerical stability checks, not rigorous enclosures of the exact
fractional coefficients.

For the resulting finite Boolean set, direct integer enumeration of ALL
unordered pairs (counted twice off the diagonal and once on the diagonal)
confirmed every FFT-derived representation count through N, with zero
disagreements. Thus the representation counts are checked exactly for the
computed finite set; its identification with the exact canonical prefix
remains numerical.

## Limits of the result

No claim is made that the canonical infinite set has infinitely many holes,
that it fails to converge, or that any other set fails the conjecture.
Finite holes do not preclude an eventual limit. The run supplies no proof
of the missing rounding estimate and no new extension invariant.

Temporary outputs:

* /tmp/canonical_profile_float64_20.log
* /tmp/canonical_profile_extended_20.log
* /tmp/canonical_profile_precision_check_20.log
* /tmp/canonical_profile_float64_20.npz
* /tmp/canonical_profile_extended_20.npz
