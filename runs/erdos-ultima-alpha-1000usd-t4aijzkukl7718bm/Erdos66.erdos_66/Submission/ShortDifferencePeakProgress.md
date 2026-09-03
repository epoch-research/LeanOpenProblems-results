# Log-squared short-difference peaks

## Original task status

The original conjecture remains unproved and undisproved.
`Submission/Spec.lean` is unchanged with its original `sorry`. No main proof
or exact-negation theorem has been submitted.

## Checked files

* `ShortDifferenceMassExplore.lean`
* `WitnessDifferencePeakExplore.lean`

Both compile and have current oleans. `ShortDifferencePeakAudit.lean` audits
11 declarations; its saved log reports only `propext`, `Classical.choice`,
and `Quot.sound`.

## Finite multiscale bound without Sidon colors

For a finite S, shortPairs(S,u) consists of pairs a<b in S with b-a<u.
Partitioning the integers into blocks of width u gives

    sum_(selected blocks b) occupancy(b)^2
      <= |S| + 2 |shortPairs(S,u)|.

This removes the Sidon-color hypothesis from the earlier annular argument
and leaves the actual short-difference mass visible.

If every annulus j in [J,2J) has squared mass at least a^2 4^j J, then

    a^2 4^J J^2 <= 3|S| + 6|shortPairs(S,4^J)|.

If also |S|<=b 4^J J and 6b<=a^2 J, then

    |shortPairs(S,4^J)| >= (a^2/12) 4^J J^2.

The exact fiber identity sums this mass over positive differences d<4^J.
Pigeonholing yields some such d with at least (a^2/12)J^2 occurrences.

## Infinite-set consequence

Define

    shiftCount(A,N,d) = #{x<N : x in A, x+d<N, x+d in A}.

`counting_profile_forces_difference_peaks` proves:

If count(A,N)/sqrt(N log N) tends to L>0, then there are gamma>0 and K
such that every J>=K has a shift 0<d<4^J with

    shiftCount(A,4^(2J),d) >= gamma J^2.

The theorem `witness_forces_difference_peaks` applies the already checked
Tauberian counting profile to any hypothetical witness of Erdős 66.
At N=4^(2J), the shift is smaller than sqrt(N) and its multiplicity is
at least a positive constant times (log N)^2. The shift may vary with J;
no fixed-shift assertion is made.

A corollary excludes proposed constructions whose counts for ALL such
short differences are uniformly o(J^2).

## Why this is not a disproof

These are DIFFERENCE counts, whereas the conjecture controls SUM counts.
A large number of pairs (x,x+d) does not place their sums at a common target.
No implication giving sum-representation errors comparable to log n was
proved.

Indeed, the main difference-peak theorem uses only the positive counting
profile. It therefore does not distinguish a witness from other sets with
the same counting asymptotic. The existing local O(log N) difference bounds
on individual dyadic windows do not contradict a log-squared count after
accumulating many windows.

The earlier square-root-logarithmic sum-fluctuation lower bound has not
been strengthened to an obstruction to o(log n). A compatible infinite
construction is also still missing. These new necessary conditions do not
settle `Submission/Spec.lean`.
