# Finite variance floor

The conjecture remains unproved and undisproved; Spec.lean is unchanged.

`CyclicVarianceExplore.lean` is complete and its olean was built. The main
results are checked by `CyclicVarianceAxiomCheck.lean`, using only the three
permitted axioms.

For a finite abelian group G of cardinal M, a finite subset B of cardinal m,
and ANY proposed center mu, let r(z)=#{a in B : z-a in B}. Then

  m^2*(M-m)^2 <= M*(M-1)*sum_z (r(z)-mu)^2.

If |r(z)-mu|<=E for every z, then

  m^2*(M-m)^2 <= M^2*(M-1)*E^2.

For sparse B, at its true mean m^2/M, the RMS fluctuation is therefore at
least approximately the square root of the mean. Exact constant
self-convolution forces B to be empty or the whole group.

The proof is elementary: self-convolution energy equals autocorrelation
energy; the autocorrelation at zero is m; its total is m^2. Apply
Cauchy--Schwarz on G\{0} and complete the square for an arbitrary center.
There is also a weighted-real-function version.

This bound does NOT disprove Erdos 66. An error of order sqrt(log n) is
compatible with the requested o(log n) error. It does prevent demanding
sub-square-root uniform errors from sparse finite cyclic templates.
