# Fixed-degree, unbounded-base digit-sphere test

This work is auxiliary and does NOT settle Erdős 773. `Spec.lean` was left
unchanged and still has its one admission for 0 < epsilon <= 1/3.

## Exact arithmetic result

A fixed path of 1947 lower digits gives four words, each with a final leading 1,
for every natural parameter t. Their base is

    B(t) = 256 + 124160 t = 256 (1 + 485 t).

Each lower digit has the form 2*c + 256*s*t with 0 <= c <= 63 and
0 <= s <= 242. Thus every digit is less than B/2, so adding any two root
words has no carries. All lower digits are even; the constant digits are
2 modulo 4. The four constant digits modulo 256 are 2, 90, 34, 70, so
the roots are pairwise distinct for every t.

The common digit sum is

    116535 + 56741120 t,

and the common sum of squared digits is

    10229501 + 9013809152 t + 2425542082560 t^2.

The values satisfy the rational rotation

    485 c = 476 a + 93 b,
    485 d = -93 a + 476 b,

and hence a^2+b^2=c^2+d^2. The degree is fixed while B tends to infinity.

## Important limitation

This is NOT a primitive family: B-1 divides every root. In fact the common
digit sum is exactly 457*(B-1). Exact integer checks at t=0,1,2,10 give
root gcd 2*(B-1). Thus this family does not resolve the possible construction
using additional primitive/coprimality restrictions. Nor does one bad sphere
class show that all large sphere classes are bad.

## Construction and verification

`/tmp/lifted_path.json` contains the finite path; `/tmp/lifted_integer_flow.json`
contains the exact integer flow from which it was extracted. The construction
lifts the base-256 rotation carry graph with affine digit slopes. To preserve
the Eisenstein constants, the base increment was chosen divisible by four.
The first slope lattice was too coarse and had a genuine integer-lattice
obstruction; refining the slope lattice removed it.

Fifteen additive labels enforce the five coefficient statistics (constant,
slope, constant squared, constant*slope, slope squared), each compared with the
first root. The cycle-label lattice has rank 14. Smith normal form, an LLL
kernel basis, high-precision Babai rounding, and positive-flow LPs gave an
integer flow. Positive spanning-tree edges were additionally required: the
first nonnegative flow had an isolated component and could not be used as a
single word. The final flow is connected and has length 1947.

All identities have been checked by exact integer arithmetic in Python.
`ParametricSphereObstacle.lean` is the completed Lean verification.
It uses a finite certificate split into blocks and a generic telescoping proof
of the rational rotation. No solver output is trusted by the final proof.
The complete file now compiles successfully with:

    lake env lean -j 1 -s 65536 Submission/ParametricSphereObstacle.lean

The axiom audits of family_common_divisor, family_not_sidon, word_conditions,
and word_moments each report only propext, Classical.choice, and Quot.sound.
The finite block certificates use `decide +kernel`, not native evaluation.
The slow final concrete-list reductions were avoided with a generic stats_eq_iff
lemma and a generic four-point non-Sidon lemma. Reducibility attributes on stats
are scoped locally to the suffix-certificate section; no unsafe reducibility
option is used.

The module includes a proof that B-1 is a common divisor to make the limitation
explicit. It is deliberately separate from `Spec.lean`.

Failed exploratory scripts for a nonconstant polynomial rotation used a very
small digit alphabet and found no nonzero reachable state. This says nothing
about larger alphabets or the primitive candidate in general.

## Simpler, stronger base-two obstruction

The new `FormalHistogramObstacle.lean` supersedes the mathematical purpose of
this large base-two example. It gives four degree-eight polynomial words with
identical complete digit histograms, common digit sum 77 and digit norm 1113.
Their squares collide as a formal polynomial identity, so the collision holds
in EVERY base B > 77. At B = 308*(t+1), their root gcd is exactly 2 for every t.
Thus even primitive roots, fixed degree, arbitrarily large base, and digit sum
smaller than the base do not repair the BASE-TWO Eisenstein candidate.

This does not extend to the formal Eisenstein argument at an inert Gaussian
prime such as 3. See `FormalHistogramResearchNotes.md` for the distinction.
