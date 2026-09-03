# Exact Tauberian counting profile

The conjecture in `Spec.lean` is still unchanged and unresolved.

Completed and compiled:
- `TauberianTestsExplore.lean`: from the already proved ratios
  F_A(r^k)/F_A(r) -> 1/sqrt(k), obtains convergence for every continuous test
  g on [0,1]:

    sum_n 1_A(n) r^n g(r^n) / F_A(r)
      -> (1/sqrt(pi)) integral_R exp(-x^2) g(exp(-x^2)) dx.

  The proof uses polynomial moments and Weierstrass approximation. Both
  positive test functionals have norm at most one.
- `TauberianCutoffExplore.lean`: continuous ramp/reciprocal windows recover
  unweighted prefix counts. Gaussian test bounds are lengths of intervals
  [-u,u] and [-v,v], divided by sqrt(pi).
- `TauberianProfileExplore.lean`: uses r_N=1-1/N and r_N^N -> exp(-1) to
  prove the exact necessary asymptotics

    A(N)/sqrt(N log N) -> 2 sqrt(c/pi),
    A(N)^2/(N log N) -> 4c/pi.

  Here A(N) counts elements below N. No Karamata theorem is assumed: the
  required Tauberian transfer is proved directly using the continuous tests.

The main results were checked in `TauberianAxiomCheck.lean` and use only
propext, Classical.choice, and Quot.sound.

This supplies the precise macroscopic profile that an extension construction
would have to preserve. It is not a construction, nor a contradiction: the
profile remains consistent with the conjecture. Uniform microscopic mixed
counts at transitions are still uncontrolled.

## General transfer and ordinary residue equidistribution

- The moment and continuous-test lemmas were generalized to accept generating
  moment ratios directly; the original witness-specialized statements remain.
- `TauberianGeneralExplore.lean` now proves:

    F_A(r) sqrt((1-r)/(-log(1-r))) -> d != 0
      implies A(N)/sqrt(N log N) -> 2d/sqrt(pi).

- `ResidueCountingExplore.lean` applies this to A restricted to each fixed
  residue class modulo m. Its generating profile is sqrt(c)/m by the previous
  weighted residue theorem. Therefore

    |{a in A : a<N, a mod m=z}| / sqrt(N log N)
      -> 2 sqrt(c)/(m sqrt(pi)),

  and the ratio of that count to A(N) tends to 1/m.

These are ordinary prefix-count conclusions, stronger than the previous
weighted-residue necessary conditions. They are still not a contradiction or
an infinite construction.

`ResidueCountingAxiomCheck.lean` verifies the general transfer and both ordinary
residue results use only the permitted axioms. All corresponding oleans have
been built. `Spec.lean` still has its original sorry; no completed conjecture
proof or disproof has been submitted.
