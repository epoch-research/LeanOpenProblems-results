# Common unit residues and the actual small Gaussian direction

The original conjecture remains UNSETTLED. Spec.lean was not changed. Its
sole admission is still at line 17287, for 0 < epsilon < 1/3. The established
unconditional endpoint remains eventual M(N) >= N^(2/3). No incomplete proof
was submitted.

## New verified module

`GaussianUnitResidueDirections.lean` imports the clean Gaussian incident
encoding and allowed-alphabet residue modules. It builds without warnings
or admissions, and has a built olean. All five printed audits use only
propext, Classical.choice, and Quot.sound.

Log: /tmp/gaussian-unit-residue-directions.log
Namespace: Erdos773.GaussianUnitResidueDirections

## The normalization gap is resolved

The old allowed-alphabet rotation theorem required two explicitly supplied
rotation equations and primitive half-angle parameters. Its denominator
could not simply be identified with the normalized small Gaussian factor.
The new theorem works directly with that FACTOR.

Let a,b,c,d share a residue modulo Q, with a a unit modulo Q. Suppose

    a+i*b = g*(m+i*n),
    {c^2,d^2} = squareCoords(g*conj(m+i*n)),
    IsCoprime m n.

The second condition includes all sign and coordinate-permutation possibilities
for the output. `factor_rotation` verifies the two coordinate identities:

    (m^2+n^2)*u = (m^2-n^2)*a+2*m*n*b,
    (m^2+n^2)*v = -2*m*n*a+(m^2-n^2)*b,

where u+i*v=g*conj(m+i*n). The square-coordinate condition says independently
that u and v are congruent to plus or minus a modulo Q.

`factor_divisibility` proves, with all four sign cases included:

    Q divides 4*n OR Q divides 4*m OR
    Q divides 2*(m-n) OR Q divides 2*(m+n).

The mixed-sign cases use Bezout cancellation directly and need only the
factor TWO. No unsupported choice of an output orientation is made.

For m>0, n>0, m!=n, `factor_norm_cutoff` consequently gives

    Q^2 <= 16*norm(m+i*n).

## Actual collision witnesses

`exists_restricted_direction` applies the existing small primitive
opposite-parity Gaussian factorization to a supplied nontrivial collision
of natural roots a,b,c,d, with a>0 and a,b<=N. It returns a direction p from
the EXISTING finite directions(N), its factorization witness g, the output
square-coordinate equality, and

    0 < p.2,
    Q^2 <= 16*normSq(p).

Membership in directions(N) already gives normSq(p)<=2*N. The axis direction
is excluded using nontriviality of the square-coordinate sets; equal factor
coordinates are excluded by opposite parity. No pre-existing rotation
parameterization is assumed.

`candidate_restricted_direction` specializes to an actual nontrivial
collision in AllowedAlphabetCandidate.root(h). Its input nontriviality is
sigma!=upsilon and sigma!=omega; canonical digit injectivity turns this into
inequality of the squared-coordinate sets. It uses the sharp root height
2*B^(h+1), B=6h+7, and the exact common unit modulus

    Q = strongModulus(h) = 6*B*(B-1).

Thus it obtains an ACTUAL normalized factor with

    Q^2 <= 16*normSq(p),
    normSq(p) <= 4*B^(h+1).

## Scope and remaining gap

The new cutoff is only polynomial in B, while the root height grows like
B^(h+1). No useful bound on all surviving large-factor collisions was
proved. The candidate's eventual Sidonness remains unproved, and its
conditional near-linear transfer cannot be applied. No original-conjecture
lower exponent or unrestricted upper exponent improved.

The generic norm cutoff also yields Q^2<=32*N for a nontrivial common-unit-
residue collision, but this is not the point of the new result: elementary
common-residue arguments can give stronger global height restrictions.
The new fact restricts the actual factor used in the finite direction
encoding, with normalization accounted for.

## Bounded exact-solver experiments: no mathematical conclusion

Research/AllowedAlphabetFixedRotation.py uses the system Z3 C library
(libz3.so.4) through ctypes. It encodes four full permutation words with
constant digit 6 and leading digit 1. A fixed rotation is chosen by

    n=Q/2, m=4*n+1,
    p=m^2-n^2, s=2*m*n, q=m^2+n^2.

The two integer equations q*z=p*x+s*y and q*w=-s*x+p*y are expanded using
the base-B digits of p,s,q and bounded integer carries. This keeps the
constraint coefficients small. The full cases require each word's interior
labels to be a permutation of 2,...,h+1 and all four words to be distinct.
Any returned model is intended to be checked by exact integer arithmetic
before any Lean certificate is attempted.

Runs:

* h=63 and h=79, ordinary integer solver, 300 seconds each: unknown.
* h=63, finite-domain qffd tactic, 300 seconds: unknown/canceled.
* relaxed h=20 cases, ordinary and qffd, 90 seconds each: unknown.

No model was returned. Requests for a model after unknown produced the
expected 'model is not available' error. These results establish neither
infeasibility nor any Sidon property, and are not counterexamples to the
candidate. No finite Lean witness was added.

Logs: /tmp/allowed-alphabet-rotation-*.log

## Main-file state

Spec.lean SHA-256 remains:

    257d2e55d464b8ea5a35ca7f1257dc2f59e682772c2f52fa771ee4bfdf9b8940
