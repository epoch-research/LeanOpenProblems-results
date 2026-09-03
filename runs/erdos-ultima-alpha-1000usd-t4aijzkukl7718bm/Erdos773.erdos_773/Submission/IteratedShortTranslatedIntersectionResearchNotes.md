# Iterated short translated-intersection extraction

This continuation does NOT settle Erdős 773. The original Spec.lean remains
unchanged, with its sole admission for 0<epsilon<=1/3. No proof or disproof
has been submitted. The strongest actual completed lower bound remains
N^(2/3)/500 eventually, from GreedyCodegreeSquareLower.eventual_power_lower.

## New verified module

Submission/IteratedShortTranslatedIntersection.lean imports the clean
ShortTranslatedIntersection module. It does not import the admitted Spec.
It compiles without warnings, errors, or admissions. All five printed
axiom audits use only propext, Classical.choice, and Quot.sound.
The corresponding olean is built. Final log:

    /tmp/iterated-short-translated-intersection-final.log

Namespace: Erdos773.IteratedShortTranslatedIntersection.

## Finite cube extraction

For a list hs of shifts, cube hs is the finite set of subset sums:

    cube [] = {0}
    cube (h::hs) = cube hs union (cube hs + h).

No distinctness of the subset sums is assumed. Basic verified facts include
0 in cube hs, sum hs in cube hs, and every offset at most sum hs. If all
shifts are positive, |cube hs| >= hs.length+1. This is not a 2^k bound.

Let A subset [1,N], N>0, M=|A|, r=2^k. If

    8 (8N)^(r-1) <= M^r,

exists_cube proves that there are B subset A and a list hs of length k with

    every shift h positive and h |B| <= 5N,
    b+t in A for every b in B and t in cube hs,
    M^r <= (8N)^(r-1) |B|.

The proof iterates the one-step short-overlap theorem. The density threshold
implies at least eight roots at every stage, so the iteration does not have
an early-stop alternative. The successor exponent cancellation uses

    2^(k+1)-1 = 2^k + (2^k-1).

exists_sidon_cube packages the result for square-Sidon A. It also proves
|B|>=8 and Sidonness of the square image of the ENTIRE root union B+cube hs,
by containment in A. It does not infer union Sidonness from the separate
translates being Sidon.

## Real-power and eventual statements

power_scale_extraction assumes M>=N^(1-eta) and the explicit threshold

    8^(2^k) <= N^(1-2^k eta).

It yields B,hs as above with

    N^(1-2^k eta) <= 8^(2^k-1) |B|,
    h <= 5 * 8^(2^k-1) * N^(2^k eta) for each selected shift,
    B+cube hs contained in A and Sidon in squares.

All real-power arithmetic is proved in Lean. In particular it uses the
identity, for positive N and positive natural r,

    (N^(1-eta))^r = N^(r-1) * N^(1-r eta).

eventually_power_scale_extraction shows that, for fixed k,eta with
2^k eta<1, the threshold holds eventually, uniformly for every candidate
A. It is conditional on the supplied cardinality and Sidon hypotheses; it
does not construct near-linear A from nothing.

## Remaining gap and research review

This completes the previously proposed iteration, not the original task.
No original exponent has improved. The extracted shifts are existential,
not prescribed. The base set remains arbitrary and possibly sparse. The
pattern therefore supplies neither universal affine-Sidon hypotheses nor
the full intervals needed for the existing full-fiber upper bounds.

A fixed-dimensional root cube does not by itself force a nontrivial square
collision. In particular, the four corners of a root parallelogram do not
have equal opposite square sums in general. Formal generic cube generators
can avoid all the finitely many pair-sum equalities. No upper bound that
exploits the combination of a large B and its short shifts was obtained.

The review also found no subpower-loss conversion from bounded difference
multiplicity to genuine Sidonness, and no repair of the already documented
carry/specialization obstacles. These are not claimed to be impossible
routes. None of these observations negates the original conjecture.

Spec.lean SHA-256 remains:
917b6c178fa6b0ff7325ec3027dda121a1138cc1198ba712cac9352f5dca5c14
