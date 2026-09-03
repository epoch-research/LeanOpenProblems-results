# Exact real projection for a boundary pair

Verified auxiliary geometry, not a settlement of Erdős 68. `Spec.lean`
remains unchanged with its original `sorry`.

`BoundaryProjectionMetric.lean` compiles without warnings. Its four
principal axiom audits contain only `propext`, `Classical.choice`, and
`Quot.sound`.

For D>0 real boundary values B_i, put

    mu = (sum_i B_i)/D,
    v_i = B_i-mu,
    V = sum_i v_i^2.

Assume V!=0. Among all real weights satisfying

    sum_i w_i=s,    sum_i w_i B_i=b,

the minimum squared norm is

    s^2/D + (b-mu*s)^2/V.

The minimizing vector is explicitly

    p_i=s/D + ((b-mu*s)/V)*v_i.

The file verifies both coordinate identities, the norm formula, and the
orthogonal-residual argument proving minimality. These are real projection
statements, not assertions that the minimizing vector is integral.

For an integer retained coefficient A and a rational x=q, the integer pair
(s,b)=(q.den,A*q.num) has projected squared norm exactly

    q.den^2 * [1/D + (A*x-mu)^2/V].

In particular the size of A alone does not give a lower bound on this
projection. If the integer boundary-pair image is all of Z^2, this pair has
an integral lift; the lift can nevertheless be much larger than its real
projection. Conversely, a useful lower bound on projected lengths must
control the displayed expression, not just the norms of integral lifts.

No such applicable infinite lower bound has been proved for the actual
Lambert boundaries. This file supplies no new small nonzero integer forms
and does not settle the original conjecture.

## Exact projection reduction on previously audited windows

External finite computations, NOT additional Lean-verified instances:

* `/tmp/boundary_projection_reduction.py`
* `/tmp/boundary_projection_reduction.json`
* `/tmp/boundary_projection_reduction.log`
* `/tmp/boundary_projection_reduction_audit.py`
* `/tmp/boundary_projection_reduction_audit.log`

For the existing K=24,28,32,36,40,48 windows (D=2K+1), the integer
boundary-pair image was already checked to be all of Z^2. Write b_i=C*B_i,
L=sum b_i, T=sum b_i^2, M=D*T-L^2. The squared projected norm of (s,b) is

    [T*s^2 - 2*C*L*s*b + C^2*D*b^2]/M.

Exact Gauss reduction gives a unimodular pair basis with Gram entries
0<a<=c and 2*|b|<=a. `reduced_binary_form_bound` in the Lean file verifies
the elementary inequality showing that a Gauss-reduced positive binary form
has no nonzero integer vector shorter than its first basis vector. The
specific large-integer certificates here have not been imported into Lean.

Diagnostics (logs are not certificate premises):

    K   log2 shortest projected norm   upper bound on kappa
   24             39.8722               .020831572
   28             49.8893               .017856208
   32             58.2341               .015624460
   36             69.7106               .013888555
   40             80.6666               .012499783
   48            102.6433               .010416564

Here kappa=1/D+(A*alpha-mu)^2/V. Its exact rational upper bounds use
W=2638!, L0=sum_(n=2)^2638 floor(W/(n!-1)), and

    L0/W < alpha < (L0+2640)/W.

The two reduced-basis forms at every tested K have interval-certified
nonzero errors. Their error scales reproduce those of the earlier useful
LLL pairs; no new asymptotic construction is asserted.

The independent audit constructs the real-coordinate matrix over Sage's
exact rationals and computes its Gram inverse directly. It verifies the
minimal real lift, both norms, unimodularity, and Gauss inequalities in all
six cases. It also checks nearby integer combinations as a supplementary
check, not as a replacement for the Gauss certificate. All six audits pass.

These finite calculations show projected, not just lift, growth in the
selected windows. Proving an adequate infinite lower bound remains missing.
A rational target would instead supply the pairs from
`rational_pair_projection`; none of these finite tests excludes a rational
with arbitrarily large denominator. The original conjecture is unsettled.
