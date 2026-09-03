# Full Beatty-prefix square-Sidon obstruction

The original conjecture remains UNSETTLED. Spec.lean was not edited and
still has its sole admission for 0 < epsilon < 1/3. No incomplete proof
was submitted.

## Verified module

`BeattySquareSidonBound.lean` imports only FormalConjecturesUtil. It has
no admissions or warnings, and its four principal axiom audits use only
propext, Classical.choice, and Quot.sound.

Namespace: `Erdos773.BeattySquareSidonBound`.

- `collision`: for every real alpha >= 1, there are four ordered positive
  integer indices a<b<c<d with d <= 50000*alpha whose Beatty roots are
  positive and strictly ordered and satisfy A^2+D^2=B^2+C^2.
- `nat_collision`: the same witness using natural indices and Nat.floor.
- `prefix_length_bound`: if ALL squares of floor(alpha*n), 1<=n<=H,
  are Sidon, then H < 50000*alpha.
- `prefix_height_bound`: additionally floor(alpha*H)<=N implies
  H^2 < 50000*(N+1).

These bounds concern FULL prefixes, not arbitrary subsets of a Beatty
sequence, not arbitrary choices in short intervals, and not M(N).
They are not an original-conjecture disproof.

## Proof

Dirichlet approximation with denominator bound 12 provides integers p,q
with 1<=q<=12, |alpha*q-p|<=1/13. Then p>=1, p<=2*alpha*q, and
p*q<=288*alpha.

If e=alpha*q-p>=0, the four multiples 3q,7q,9q,11q have Beatty roots
3p,7p,9p,11p. Their squares collide because 3^2+11^2=7^2+9^2.

Otherwise put eta=p-alpha*q, so 0<eta<=1/13.

If 15*p*eta<=1, for 1<=k<=15p one has floor(alpha*q*k)=p*k-1.
Use k=5p+1,9p+2,13p-1,15p and the exact identity

  (p*(5p+1)-1)^2+(p*(15p)-1)^2
    = (p*(9p+2)-1)^2+(p*(13p-1)-1)^2.

The largest index is 15*p*q<=4320*alpha.

If 15*p*eta>1, let k=floor(1/eta). Then 13<=k<=15p, and

  alpha*(q*k) = (k*p-1) + (1-k*eta),
  0<=1-k*eta<eta<=1/13.

Apply the positive-error homothetic construction with denominator q*k
and positive integer numerator k*p-1. The largest index is at most
165*p*q<=47520*alpha. The boundary k*eta=1 is allowed (error zero).

The height consequence follows by multiplying H<50000*alpha by H,
then using alpha*H<floor(alpha*H)+1<=N+1.

## Logs

- /tmp/beatty-square-bound.log
- /tmp/beatty-square-bound-build.log
- /tmp/spec-beatty-continuation-check.log

No actual exponent above 2/3, near-linear low-collision square carrier,
or unrestricted fixed-power upper bound was obtained in this continuation.
The obstruction to settling the original conjecture is still mathematical.
