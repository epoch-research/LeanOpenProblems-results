# Full-period raw Lambert Hankel determinants

External exact finite investigation, NOT a Lean theorem or a settlement of
Erdos 68. Spec.lean remains unchanged with its original sorry. No complete
proof or disproof has been obtained or submitted.

## New parameter regime

Let K count cancelled rows, d=K+2, and

    Q(E)=product_(k=2)^(K+1)(k!*E^k-1), A=Q(1),
    B_n=Q(E) S_n,
    D(X)=det_(0<=i,j<d) (A*X-B_(H+i+j)).

The Hankel size is the FULL period d of the first uncancelled row, rather
than a fixed small matrix size. For K in {4,8,10,12,16,20}, test both

    H=d^2,
    H=(d+1)*(3*(floor(log2(d))+1)+130).

The second choice is the explicit late-window threshold in the verified
nonsingularity result; that theorem applies when d>=12. The smaller-d
instances here are checked only by the exact external computation.

All twelve affine determinants have nonzero leading coefficient. Reduce
their root to B/A with A>0 and gcd(A,B)=1. Every tested FULL-target error
A*alpha-B is certified strictly greater than one.

Selected diagnostics (not certificate premises):

    K  d    H     reduced denominator bits   log2(error) upper
    4  6     36             1121                 1032.566
   10 12    144            11779                11261.479
   10 12   1846           168614               164007.108
   16 18   2755           388187               379700.988
   20 22    484            86408                84150.470
   20 22   3335           583757               572442.273

These are finite failures, not lower bounds for every parameter choice or
an asymptotic impossibility theorem.

## Construction and independent audit

The generator constructs the factorial-scaled Lambert prefix by

    L_n=n*L_(n-1)+a_n,
    a_n=sum_(k|n,k>=2) n!/(k!)^(n/k), S_n=L_n/n!.

It expands Q with integer coefficient arrays and clears the minimal common
boundary denominator C. With b_i=C*B_(H+i), row and column subtraction gives

    v_i=b_i-b_0,
    M_(i,j)=-(b_(i+j)-b_i-b_j+b_0), 1<=i,j<d.

The root is (b_0+v^T*M^(-1)*v)/(C*A). Exact integer/rational linear algebra
supplies the solution, and every linear equation is checked exactly.

The audit independently anchors S_H by finite geometric rows,

    S_H=sum_(k=2)^H [(k!)^floor(H/k)-1]
                        /[(k!-1)*(k!)^floor(H/k)],

then updates the later prefixes by a divisor-first summation. It constructs
Q with SymPy polynomial multiplication, checks C, reconstructs the matrix,
and verifies the saved solution and reduced root. In each of the twelve
cases the lower-block determinant is nonzero modulo 1000000007, giving an
independent certificate that the block is invertible and the affine leading
coefficient is nonzero.

Both error classifications use exact factorial-grid enclosures

    W=N!, L=sum_(k=2)^N floor(W/(k!-1)),
    L/W < alpha < (L+N+2)/W.

The generator uses N=5000 and the audit N=5017. All twelve classifications
agree. No floating-point value is used for a sign or comparison with one.

Artifacts:

* /tmp/full_period_hankel.py, .log, .json
* /tmp/full_period_hankel_audit.py, .log

Both computations have completed. No compilation or computation is pending.
The missing small nonzero integer-form construction remains unresolved.
