# Short translated-intersection extraction

This continuation does NOT settle Erdős 773. Spec.lean is unchanged and its
sole admission remains for 0<epsilon<=1/3. No proof or disproof was submitted.

## New verified module

`ShortTranslatedIntersection.lean` imports the clean
`TranslatedIntersectionSelection` module, not Spec.lean. It builds without
errors, warnings, or admissions. Its five printed axiom audits use only
propext, Classical.choice, and Quot.sound. The olean is built.
Log: `/tmp/short-translated-intersection.log`.

## Finite counting results

For A subset [1,N], put M=|A| and

    overlap(A,h)={a in A : a+h in A}.

`block_pair_bound` proves that, for H>0, if every 1<=h<=H has overlap size
at most K, then

    M^2 <= (floor(N/H)+1) (M+2 H K).

Partition roots by floor(a/H). Cauchy--Schwarz gives the lower count of
same-block ordered pairs. A same-block off-diagonal pair has gap at most H.
Positive-gap fibers inject into overlap(A,h); the two orientations and the
diagonal give the upper bound M+2HK. The K bound is global: the proof does
not separately charge K in every block.

`exists_short_overlap_of_blocks` consequently proves that if H<=N and
2(floor(N/H)+1)<=M, then some h in [1,H] has

    M^2 <= 8 N |overlap(A,h)|.

`exists_short_overlap` chooses H=floor(4N/M)+1. For M>=8 it proves a shift
1<=h<=N satisfying both

    h M <= 4N+M,
    M^2 <= 8N |overlap(A,h)|.

Thus h is of order N/M, rather than merely bounded by N as in the previous
translated-intersection theorem.

## Actual Sidon union, not just separately Sidon copies

`extract_short_sidon_union` proves that if A's squares are Sidon and M>=8,
there exist h and B with

    B union (B+h) subset A,
    h M <= 4N+M,
    M^2 <= 8N |B|,
    the squares of B union (B+h) are Sidon.

Sidonness of the entire union follows from its containment in A. It is not
inferred merely from Sidonness of the two copies separately.

`power_scale_extraction` includes verified real-power bookkeeping. Under
M>=N^(1-eta) and the same hypotheses, its extracted h,B satisfy

    h <= 5 N^eta,
    N^(1-2eta) <= 8 |B|.

This is an implication from a supplied large original root set. It does
NOT establish such a root set. The theorem even allows any real eta; the
positive eta case is the intended asymptotic use.

## Remaining mathematical gap

The shift is still selected existentially, not prescribed. A small selected
shift does not give Sidonness at every affine map, so the existing
UniversalAffineSidonBound theorem cannot be applied. No uniform fixed-power
upper bound for these short-shift Sidon unions was obtained. No construction
of near-linear such unions was obtained either.

The earlier review of formal-polynomial specialization also yielded no
new near-linear low-collision family. Existing specialization and carry
counterexamples remain relevant; none is a disproof of the original problem.

No actual lower or upper exponent for the original conjecture improved.
The strongest actual completed lower bound remains N^(2/3)/8192 eventually.
Spec.lean is unchanged, with SHA-256
917b6c178fa6b0ff7325ec3027dda121a1138cc1198ba712cac9352f5dca5c14.
