# Hankel determinants of shifted, row-cancelled Lambert tails

This is an exact external construction test, NOT a Lean-verified theorem
and NOT a settlement of Erdős 68. Spec.lean is unchanged with its original
sorry. No proof or disproof has been obtained or submitted.

## Construction

Let S_n be the rational Lambert prefix, and put

    Q_K(E)=product_(d=2)^(K+1)(d!*E^d-1),
    A_K=Q_K(1),
    B_h=Q_K(E)S_h,
    epsilon_h=A_K*alpha-B_h.

K=0 means the empty operator. For m>=2 form the Hankel determinant

    D_(K,H,m)(X)=det_(0<=i,j<m)(A_K*X-B_(H+i+j)).

The X-dependent matrix has rank one, so the determinant is affine in X:
D(X)=a*X+b for rational a,b. The script calculates det at X=0,1,2 and
checks det(2)=2*det(1)-det(0) exactly in each tested instance. For a!=0,
reduce -b/a=u/v, v>0, and test the integer form v*alpha-u. This tests a
nonlinear elimination of the tail samples rather than selecting a bounded
lattice relation.

## Completed exact test

Parameters:

    K=0,...,8,
    H in {0,K+1,2*(K+1),(K+1)^2}, duplicates removed,
    m=2,...,8.

All 238 cases had nonzero affine leading coefficient. After full reduction,
127 certified errors were greater than one and 111 were less than minus
one. There were no small or ambiguous cases.

Certificates use W=2000! and

    L=sum_(n=2)^2000 floor(W/(n!-1)),
    L/W < alpha < (L+2002)/W.

All matrix determinants, reduced fractions, and interval comparisons use
exact rational arithmetic. Decimal error logs in the output are diagnostic
only. The stored numerator/denominator pairs can be checked against the
same exact enclosure. These finite failures do not establish an asymptotic
impossibility theorem and do not exclude other determinant constructions.

Artifacts:

    /tmp/shifted_lambert_hankel.py
    /tmp/shifted_lambert_hankel.log
    /tmp/shifted_lambert_hankel.json

The computation completed; no computation remains running.

## Boundary-lattice review

The accompanying review found no new uniform nonvanishing theorem for the
older lattice construction. Integral boundary clearing still allows bounded
weights to lie in the zero-pair subspace. Divisibility restrictions on the
weight sum do not supply a bounded vector outside that subspace. Likewise,
a fixed shift polynomial's eventual nonvanishing would not by itself give
the quantitative, growing-degree result required by the lattice parameters.
No such fixed-polynomial theorem is asserted as Lean-verified here.

The original conjecture remains unproved and undisproved in this workspace.
