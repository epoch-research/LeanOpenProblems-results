# Positive Toeplitz matrices from geometric peaks of raw tails

Verified auxiliary progress, NOT a proof or disproof of Erdős 68.
`Submission/Spec.lean` remains unchanged with its original `sorry`.

`TailDominantToeplitz.lean` compiles without warnings and has a built olean.
Its four printed principal axiom audits use only `propext`, `Classical.choice`,
and `Quot.sound`. No numerical experiment is used in the proofs.

## General geometric-peak lemma

Suppose a real sequence f satisfies, for n>=H,

    6^n * |f(n)| <= C,

and f is nonzero somewhere after H. There is n>=H such that f(n)!=0 and

    |f(n+k)| <= 2*|f(n)|/6^k      for every k>=0.

Choose a value above half the supremum of the positive, bounded set of
normalized values 6^m*|f(m)|, m>=H. This is `exists_geometric_peak`.
No claim that the supremum itself is attained is made.

## Positive definiteness at every finite size

For such a peak n, choose s in {1,-1} with s*f(n)=|f(n)|. For every D,

    M(i,j)=s*f(n+|j-i|),  0<=i,j<D,

is real symmetric positive definite. The off-diagonal absolute row sums
are at most

    2*|f(n)| * sum_(z in Z, z!=0) 6^(-|z|)
      = (4/5)*|f(n)| < M(i,i).

The file verifies the two-sided geometric sum and the finite row bound.
It proves the general real symmetric strict-diagonal-dominance criterion
using Gershgorin's theorem and the real Hermitian eigenvector basis, then
applies it as `peak_toeplitz_posDef`.

The same n and sign work simultaneously for ALL D. The matrix size is not
chosen before the geometric peak.

## Application to the exact Lambert raw tails

Use the existing indexing in which K rows 2,...,K+1 are cancelled, and put

    Q_K(E)=product_(d=2)^(K+1) (d!*E^d-1),
    A_K=Q_K(1),
    B_m=Q_K(E)S_m^Lambert,
    f(m)=rawTail(K,m)=A_K*alpha-B_m.

For K>=35 and m>=4, the verified explicit raw-tail bound implies

    6^m*|f(m)| <= 6*(K+1)*2^(K+1).

Indeed 6^m <= 6*(K+1)^floor(m/2). The earlier verified raw nonvanishing
windows give a nonzero value after every cutoff. Consequently
`raw_geometric_peaks` applies after every cutoff H.

The main theorem `raw_positive_toeplitz_family` gives n>=H and an integer
s equal to 1 or -1 such that, for every D, the matrix with entries

    (s*A_K)*alpha - s*B_(n+|j-i|)

is positive definite. Here A_K is integral and the B_m are rational.
These are the actual full-target raw tails, not a finite-row approximation
or a comparison series.

## Remaining arithmetic problem

Positive definiteness gives strictly positive determinants. The retained
alpha coefficient matrix is a scalar multiple of the all-ones matrix and
has rank at most one. Thus the determinants are affine in alpha as a
mathematical consequence of determinant multilinearity; that affinity has
not been separately packaged as a declaration in this file.

Crucially, the entries have RATIONAL boundaries. Clearing them, or taking a
primitive integer normalization of the affine determinant, can greatly
enlarge its value. No bound showing that the resulting nonzero integer forms
tend to zero has been obtained. The general small-or-zero boundary-lattice
construction does not automatically clear this positive determinant family
with a compatible size bound.

This is a new unconditional nonvanishing construction, not an irrationality
proof or a claim that the earlier arithmetic gap has closed. No proof or
disproof has been submitted.
