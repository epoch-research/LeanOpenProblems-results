# Uniform bounds for uncancelled raw Lambert rows

This is verified auxiliary progress, not a settlement of Erdős 68.
Spec.lean is unchanged and retains its original sorry.

`LambertRawBounds.lean` compiles without warnings and has a built olean.
All five printed principal axiom audits contain only propext,
Classical.choice and Quot.sound.

## Verified factorial estimates

For k<=d,

    (k!)^d <= (d!)^k,
    d^d <= (d!)^2.

The first uses k!<=k^k and k!*k^(d-k)<=d!. The second multiplies
(j+1)*(d-j)>=d for j=0,...,d-1; reflection of the finite product makes
its right side (d!)^2.

Define lambda_d=(d!)^(1/d). For d>0 the file proves

    lambda_d>0, lambda_d^d=d!, lambda_d>=1,
    k!<=lambda_d^k (k<=d), d<=lambda_d^2.

## Verified row and operator bounds

For d>=2 and any n,

    r_d(n)=1/((d!)^floor(n/d)*(d!-1)) <= 2/lambda_d^n.

The floor identity bounds lambda_d^n by (d!)^(floor(n/d)+1), and
2*(d!-1)>=d! completes the estimate.

Define rawShift_k(r)(n)=k!*r(n+k)-r(n), and compose along a finite list ds.
For every d>=2, if every k in ds satisfies k<=d, the verified theorems are

    |rawApply_ds(r_d)(n)| <= 2^(length(ds)+1)/lambda_d^n,
    |rawApply_ds(r_d)(n)| <= 2^(length(ds)+1)/d^floor(n/2).

More generally, `rawApply_bound` proves the geometric-envelope estimate
for any sequence bounded by C/x^n, whenever k!<=x^k for every shift k.
Each shift costs at most a factor two.

The file verifies the exact connection to the previously defined operators:

    rawApply_ds(r) = (product_(k in ds) k!) * applyShifts_ds(r).

It therefore also verifies exact annihilation of row d whenever d occurs
in ds and d>0. Repeated shifts are allowed in all these statements.

## Scope and remaining work

These are per-row bounds and exact operator identities. The full infinite
row decomposition and total error bound are now verified in LambertTailRows.lean
and LambertTotalBounds.lean; see LambertTotalBoundsNotes.md. The common
boundary denominator and finite pigeonhole argument are now also verified;
see LambertBoundaryFrameworkNotes.md. The Stirling asymptotics remain informal. More importantly, even a small total
bound on a nonzero weight vector does not ensure a nonzero integer form.
No uniform final-successive-minimum bound or infinite independent-pair
construction has been obtained.

A review of Hankel determinants of tails supplied no new nonvanishing or
arithmetic estimate. The affine determinant in alpha corresponds to a
shifted Shanks/Padé approximant; calling it a determinant does not by itself
repair the denominator cost or establish a sign.

## Additional exact finite sign diagnostic

The script /tmp/lambert_shift_signs.py, with log
/tmp/lambert_shift_signs.log, checked the raw errors epsilon_H for H=K,...,3K
at K in {2,3,4,8,12,16,24,32,40}. Signs used exact rational intervals from
the W=2000! factorial grid. The calculation completed.

For example, at K=8 the signs in order H=8,...,24 are

    -+++++++--++++++-

and at K=24 they are

    -+++++++++++++++++++++++--++++++-++++++++++++++++.

Thus shifted errors do not all share a sign. The tested starting error
epsilon_K has sign (-1)^(K-1), and its product with (K+1)! appears close to
that sign; this is only finite evidence, not a proved asymptotic or sign
formula. No nonvanishing claim about all lattice combinations follows.
No proof or disproof of the original conjecture has been submitted.
