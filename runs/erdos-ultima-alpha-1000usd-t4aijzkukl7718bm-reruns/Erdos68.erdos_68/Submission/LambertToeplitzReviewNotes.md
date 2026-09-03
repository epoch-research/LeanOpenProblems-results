# Full-rank Lambert Toeplitz construction: determinant limitation

This is mathematical analysis, NOT a new Lean theorem and NOT a settlement
of Erdos 68. Spec.lean is unchanged with its original sorry. No complete
proof or disproof was obtained, and no submission check was run.

## Positive matrices with rational off-diagonal entries

Use the original Lambert coefficients

    c_h = sum_(d|h, d>=2) 1/(d!)^(h/d), h>=1.

Each c_h is rational, h!*c_h is integral, c_1=0, c_2=1/2, and

    sum_(h>=1) c_h = alpha.

For N>=1 define the symmetric N-by-N rational polynomial pencil

    T_N(X)_(i,i) = 2X,
    T_N(X)_(i,j) = -c_|i-j|, i!=j,  0<=i,j<N.

Unlike the earlier raw-tail Hankel pencil, the retained X coefficient is
2I and has full rank.

Extend a vector v by zero to all integers. At X=alpha, direct expansion gives

    v^T T_N(alpha) v
      = sum_(h>=1) c_h * sum_(i in Z) (v_i-v_(i+h))^2.

The interchange is harmless: v has finite support, the inner sum is
bounded by 4*sum v_i^2, and sum c_h converges. This proves positivity.
The h=2 term alone is strictly positive for nonzero v: a finitely supported
2-periodic sequence is zero. Thus the pencil is positive definite at alpha.

## A uniform determinant-root lower bound

Let L_N have diagonal 2, entries -1 at distance two, and all other entries
zero. Its quadratic form is sum_i (v_i-v_(i+2))^2. The preceding identity and
c_2=1/2 give the Loewner inequality

    T_N(alpha) >= (1/2) L_N > 0.

Permutation by parity splits L_N into two standard Dirichlet path matrices,
of sizes r=ceil(N/2) and s=floor(N/2). The tridiagonal determinant recurrence
a_m=2*a_(m-1)-a_(m-2), with a_0=1 and a_1=2, gives

    det L_N = (r+1)*(s+1).

Determinant monotonicity for positive-definite real symmetric matrices now
implies

    det T_N(alpha) >= 2^(-N)*(r+1)*(s+1).

This is not just a failure to estimate a small eigenvalue. The smallest
eigenvalue may tend to zero, while the determinant's degree-normalized size
still has this positive lower bound.

## The bound survives primitive integer polynomial normalization

The rational polynomial

    D_N(X)=det T_N(X)

has degree N and leading coefficient 2^N. Let u>0 be any rational scaling
such that P_N=u*D_N has integer coefficients. Its leading coefficient is
a positive integer, so

    u*2^N >= 1.

Consequently, including for the primitive integer normalization,

    P_N(alpha) >= 4^(-N)*(r+1)*(s+1) >= 4^(-N).

Thus this specific determinant family cannot satisfy the verified criterion
requiring positive values smaller than epsilon^degree for every epsilon>0.
The argument allows cancellation of all polynomial content; it does not
assume termwise clearing of the rational matrix entries.

These matrix and determinant claims are mathematical arguments here, not
new Lean declarations or premises in Spec.lean. No numerical experiment was
needed or run for this review.

## Scope

This excludes only the unmodified T_N determinant family (and positive
rational rescalings making its polynomial integral). It does not cover
rectangular weighted compressions, other retained coefficient matrices,
subtracted rational kernels, or other auxiliary polynomials.

The boundary-lattice route was also reviewed. Its exact pair image and real
projection formula still give no uniform useful integral-lift bound. Under
rationality, a very short projected rational pair is compatible with a large
integral lift, so nonzero weights or an unbounded lift norm cannot replace
nonvanishing of the resulting integer form. No new arithmetic bound resolving
that issue was found.

The original conjecture remains unproved and undisproved in this workspace.
No complete informal proof is waiting to be formalized, and nothing is
pending compilation or computation from this review.

## Tail-subtracted variation reviewed subsequently

This additional review is informal mathematics, not a new Lean declaration.
It supplies no settlement and leaves Spec.lean unchanged.

Set

    s_K = sum_(d=2)^K 1/(d!-1),
    c_h^(>K) = sum_(d|h, d>K) (d!)^(-h/d),
    M_(N,K)(X) = (X-s_K) I - C_(N,K)/2,

where C has zero diagonal and off-diagonal entry c_|i-j|^(>K). The polynomial
D_(N,K)=det M_(N,K) is monic of degree N. At X=alpha it is positive definite:
its quadratic form is one half of the sum of the remaining weighted shift
Laplacians. With d=K+1,

    D_(N,K)(alpha) >= (1/(2*d!))^N det L_(N,d)
                      >= (1/(2*d!))^N.

Here L_(N,d)=2I-S_d-S_d^T. Splitting the indices into residue classes modulo
d gives Dirichlet paths, whose determinants are their sizes plus one. This
also covers d>=N, when L_(N,d)=2I. Thus the original fixed-root lower bound
weakens as K grows and does not by itself exclude the variation.

There is nevertheless a denominator cost that cannot be removed by taking
primitive polynomial content. Let p>N be an odd prime, and suppose the
reduced denominator of s_K contains p to exponent e>0. All entries of C/2
are p-integral: they use factorials of integers at most N-1 and a factor 2.
At X=0, each diagonal entry has p-adic valuation -e, while every off-diagonal
entry has nonnegative valuation. The identity permutation is therefore the
unique minimum-valuation term in the determinant, giving

    v_p(D_(N,K)(0)) = -N*e.

If u>0 is rational and u*D_(N,K) has integer coefficients, monicity first
forces u to be an integer, and its constant coefficient forces

    v_p(u) >= N*e.

Writing b for the part of den(s_K) supported on odd primes greater than N,
this yields b^N | u and hence

    (u*D_(N,K))(alpha) >= (b/(2*(K+1)!))^N.

No uniform estimate on this b, or on the other prime contributions to u,
was proved. In particular this argument neither eliminates every growing
(K,N) family nor constructs a family meeting the irrationality criterion.
The small real row-tail mass alone does not establish smallness after
integer normalization. No numerical search, new Lean proof, or submission
check was used for this review.
