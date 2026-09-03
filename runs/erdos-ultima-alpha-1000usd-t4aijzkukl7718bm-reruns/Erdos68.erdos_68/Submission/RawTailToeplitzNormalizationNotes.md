# Exact primitive normalization test for raw-tail Toeplitz forms

External finite calculation only, NOT a Lean theorem and NOT a settlement of
Erdos 68. `Submission/Spec.lean` remains unchanged with its original `sorry`.
No proof or disproof has been obtained or submitted in this continuation.

## Construction

Use the indexing of `TailDominantToeplitz.lean`:

    Q_K(E)=product_(d=2)^(K+1) (d!*E^d-1),
    A_K=Q_K(1),
    B_m=Q_K(E)S_m^Lambert,
    E_(H,D)(X)_(i,j)=A_K*X-B_(H+|i-j|).

Test K=4,8,12,16,35, with initial phase window starting at max(4,K^2).
Choose the first two phases in each window satisfying the exact sufficient
strict diagonal-dominance bound for all tested dimensions D=2,4,8,12.
All selected phases have a certificate; no fallback phase was needed.
The selected H values are:

    K=4: 17,18; K=8: 65,69; K=12: 144,145;
    K=16: 256,257; K=35: 1225,1226.

The sign-normalized full-target matrices are positive definite. Their
alpha-coefficient matrix has rank one, so their determinants are affine.
After finding the rational root and reducing it to B/A with A>0 and
coprime A,B, evaluate the primitive integer form A*alpha-B.

## Results

All 40 primitive errors have absolute value GREATER than one. The small
raw determinants therefore do not give small integer forms in these tests.
The following base-two logarithms are diagnostics, not certificate premises:

    K     smallest log2(abs(error))    largest log2(abs(error))
     4              71.088                    672.114
     8             363.391                   2645.802
    12             944.496                   6088.711
    16            1853.442                  11547.156
    35           10966.499                  66309.730

Each greater-than-one assertion is checked using exact rational intervals
for the FULL original target. No truncated-row value substitutes for alpha.
The construction uses the enclosure

    W=N!, L=sum_(d=2)^N floor(W/(d!-1)),
    L/W < alpha < (L+N+2)/W,

with N=2500. Its root calculation uses the (D-1)-dimensional Schur complement
after subtracting the first row and column.

## Independent audit

Artifacts:

* `/tmp/raw_tail_toeplitz.py`
* `/tmp/raw_tail_toeplitz.log`
* `/tmp/raw_tail_toeplitz.json`
* `/tmp/raw_tail_toeplitz_audit.py`
* `/tmp/raw_tail_toeplitz_audit.log`

The audit reconstructs each Lambert prefix from finite geometric rows,
instead of the construction's divisor-coefficient recurrence:

    S_n^Lambert=sum_(d=2)^n
      ((d!)^floor(n/d)-1)/((d!-1)*(d!)^floor(n/d)).

It constructs Q_K by exact Sage polynomial multiplication, recomputes the
minimal common denominator C of the boundaries, and verifies coprimality
of the recorded primitive pair. At the claimed root it constructs the full
D-by-D integer-scaled pencil and checks determinant zero and rank D-1,
without reusing the Schur-complement solution.

With a separate factorial-grid enclosure at N=2501, the audit checks strict
diagonal dominance row by row and checks that each primitive error has
absolute value greater than one. All 40 audits pass. Both processes have
completed; no computation is pending.

## Remaining gap

This is finite negative evidence for this normalization, not an asymptotic
impossibility theorem. The positive Toeplitz theorem remains valid.

Positivity excludes a common null vector for a full Toeplitz block, whereas
the scalar boundary-lattice pigeonhole construction clears one output and
may return a vector with zero value there. Requiring all block outputs to
be integral adds simultaneous congruence constraints. The earlier index
analysis does not give a compatible small-vector bound. Positivity alone
does not supply the missing integral-output selection or a useful lift.

No complete informal proof of the original conjecture is awaiting
formalization. The conjecture statement and its import have not been altered.
