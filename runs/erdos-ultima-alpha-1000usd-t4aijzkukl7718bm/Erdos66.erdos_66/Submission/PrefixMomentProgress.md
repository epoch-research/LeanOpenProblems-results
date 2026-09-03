# Moment obstruction to uniformly flat modular prefixes

The conjecture in `Spec.lean` is still **not settled**. Its statement and original
`sorry` remain unchanged. The following are auxiliary necessary conditions.

## Completed and checked

1. `RawMomentExplore.lean` defines finite averages and pair moments. It proves
   the raw-moment inequality for a sum of two iid finite distributions:

       0 <= m4 - 4*m1*m3 + 10*m1^2*m2 - 5*m1^4 - 2*m2^2.

   Substituting the uniform [0,1] moments gives -1/720, so the first four pair
   moments cannot simultaneously tend to 1/2, 1/3, 1/4, 1/5. Empty finite sets
   are handled as well.

2. `WeightedLogExplore.lean` proves that f(n)/log(n) -> c implies

       sum_{i<N} |f(i)-c log(N)| / (N log(N)) -> 0.

   Bounded weights can be inserted. In particular, for k=0,...,4,

       sum_{i<N} (i/N)^k f(i) / (N log(N)) -> c/(k+1).

   The power-sum limits are proved by explicit formulas, not by assuming a
   Tauberian or Riemann-sum theorem.

3. `PrefixMomentExplore.lean` applies this to a hypothetical witness A. If
   A(N)^2/(N log N) also tended to c, the number of pairs with sum >=N would be
   negligible. Their contributions to each fixed normalized moment are bounded
   by 2^k times their mass. Thus all four moments of the full finite pair
   distribution would tend to the uniform moments, a contradiction.
   Main theorem: `count_limit_ne_coefficient`.

4. `PrefixGapExplore.lean` runs the same proof along any nonbottom subfilter of
   atTop. A subsequence argument then yields the stronger theorem
   `counting_coefficient_gap`:

       if r_A(n)/log n -> c != 0,
       then there exists delta>0 such that eventually
       A(N)^2/(N log N) >= c+delta.

5. `CyclicPrefixExplore.lean` connects this back to finite cyclic groups.
   Define modularPrefix A n as A intersect [0,n], reduced modulo n+1.
   Its representation counts sum to A(n+1)^2. Its count at residue n is exactly
   r_A(n), with no wraparound term. Consequently `cyclic_prefix_variation` proves
   that for some delta>0, eventually there is a residue z with

       r_modPrefix(z) >= r_modPrefix(n) + delta log(n).

   Hence the modular prefixes of an actual witness cannot have uniformly flat
   counts with vanishing relative error.

All files compile, and their principal theorems were axiom-checked: only
propext, Classical.choice, and Quot.sound are used.

## Limitations

This is NOT a contradiction to the original conjecture. The expected counting
constant is 4c/pi, which is strictly larger than c. Neither that exact Tauberian
asymptotic nor a construction of an actual witness has been proved here.

The finite-field construction in `FiniteAnalogueExplore.lean` remains valid,
but a direct uniformly flat modular-prefix transfer cannot work. Any successful
transfer would need a nonflat/inhomogeneous modular profile and control of
integer carries and cross-scale interactions.
