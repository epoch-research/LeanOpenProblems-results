# Digit-level proof attempt: verified mathematical scope

This note records a mathematical investigation, **not a Lean proof of either
statement in Spec.lean**. No general AP-free reciprocal bound is established.

## 1. Complete binary-digit levels

Let n=2m and let w_i be integers in [0,Q]. Set

    S(a) = sum_{i<2m} w_i bit_i(a),
    F_c = {a in [0,4^m) : S(a)=c}.

If F_c contains no nontrivial 4-term AP, then

    |F_c| <= (mQ+1) 3^m.

Proof. Partition the m base-4 digits into three disjoint types: the variable
pair {0,3}, the singleton {1}, and the singleton {2}. This partitions [0,4^m)
into 3^m faces. In a face with variable coordinates V, write each number as
q+3x, where q has the fixed digits and x has digits 0 or 1 at V, zero elsewhere.
Put E(x)=sum_{j in V} w_{2j} bit_j(x) and
O(x)=sum_{j in V} w_{2j+1} bit_j(x), where bit_j here denotes the base-4 digit.
Then S(q+3x)=S(q)+E(x)+O(x).

Two distinct points q+3x and q+3y in F_c with E(x)=E(y) also have O(x)=O(y).
The four numbers

    q+3x, q+2x+y, q+x+2y, q+3y

form an AP of nonzero difference y-x. If necessary exchange x and y to make
the difference positive. At a variable coordinate the four digits are
3epsilon_x, 2epsilon_x+epsilon_y, epsilon_x+2epsilon_y, 3epsilon_y, all at
most 3. Thus there are no inter-coordinate carries. The two middle costs are
S(q)+O(x)+E(y) and S(q)+E(x)+O(y), both c, so the AP lies in the complete
level. Since E takes at most mQ+1 values, there are at most that many points
of F_c in each face.

The word 'complete' is essential. For an arbitrary subset of F_c, its two
mixed points need not belong to the subset. The argument is NOT an upper
bound for arbitrary 4-AP-free sets.

For fixed k, group t=ceil(log_2 k) bits at a time, use the variable pair
{0,2^t-1}, and match the first t-1 residue-position costs. Interpolating the
two endpoints gives a 2^t-term AP, hence a k-term AP. The same reasoning gives

    |F_c| <= 2^ell (mQ+1)^(t-1) (2^t-1)^m,  n=tm+ell, 0<=ell<t.

For polynomial Q this is a power saving in 2^n. It excludes the proposed
inverse-log-density counterexamples from this family, but not other families.

## 2. Why bounded nilsequence complexity does not give this digit structure

Let N=4^m, K=2^m, with m>=1, and

    D = {sum_{i<m} epsilon_i 4^i : epsilon_i in {0,1}},
    psi(a) = exp(2 pi i a^2/(2N)).

Every a<N is uniquely X+2Y with X,Y in D. Consider the K by K matrix
P(X,Y)=psi(X+2Y). Multiplication by diagonal unitary matrices reduces P to

    H(X,Y)=exp(2 pi i 2XY/N).

For X!=X', write X-X'=4^r t with t odd, where r is the least differing digit.
The inner product of the two rows is

    product_{i<m} (1+exp(2 pi i 2(X-X')4^i/N)).

Its i=m-1-r factor is 1+exp(pi i t)=0. Hence HH*=K I: all K singular values
of P equal sqrt(K).

By contrast, any function v(a)=F(C_1(a),...,C_d(a)), where
C_j(a)=sum_i w_{ji} bit_i(a) and 0<=w_{ji}<=Q are integers, has at most
R=(mQ+1)^d distinct rows in these coordinates. Its matrix rank is at most R.
The singular-value lower bound for rank-R approximation therefore gives

    (1/N) sum_{a<N} |psi(a)-v(a)|^2 >= 1-R/sqrt(N).

Thus even constant-accuracy approximation of this quadratic phase requires
R comparable to sqrt(N), not polylog(N). The phase is N-periodic and has
identically vanishing third multiplicative derivative, hence maximal U^3
norm. It is a polynomial nilsequence of absolute degree and dimension.

Consequently a black-box conversion of bounded-complexity higher-order
nilsequences to polylogarithmically many separable digit states is false.
An AP-free-specific replacement might conceivably exist, but has NOT been
proved here. Inverse theorems also give correlation or fractional cell
densities, not the full-fiber membership used in section 1.

## 3. Remaining obligation

The unrestricted statement remains exactly

    forall k>=3, exists C_k, forall finite k-AP-free F,
      sum_{a in F, a>0} 1/a <= C_k.

The Lean equivalence is in ConjectureReduction.lean. Neither this note nor
the current development files supplies these bounds or a counterexample.
