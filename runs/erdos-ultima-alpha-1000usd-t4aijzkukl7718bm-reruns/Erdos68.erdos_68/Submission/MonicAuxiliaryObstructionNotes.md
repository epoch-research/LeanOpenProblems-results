# A local obstruction to monic direct-series auxiliary polynomials

This is mathematical analysis, not a Lean-verified theorem and not a
settlement of the conjecture in Spec.lean.

Let F(z)=sum_(n>=2) z^n/(n!-1), considered as a formal series over Q.
Let R=Z_(5), the subring of rationals with denominator prime to 5.
For n>=2, the only n for which 5 divides n!-1 is n=3:
the n=2 and n=4 denominators are 1 and 23, and for n>=5 the denominator
is congruent to -1 modulo 5. Moreover 3!-1=5 exactly.
Consequently G=5F belongs to R[[z]], and its coefficientwise reduction
modulo 5 is exactly z^3.

Suppose

    P(z,X)=A(z)X^d + sum_(j<d) B_j(z)X^j,
    A,B_j in Z[z].

Multiplication by 5^d gives an identity over R[[z]]:

    5^d P(z,F(z))
      = A(z)G(z)^d + sum_(j<d) 5^(d-j)B_j(z)G(z)^j.

Reduction modulo 5 is therefore A_bar(z)z^(3d).
If A_bar is nonzero and its first nonzero coefficient is at index r,
the coefficient at index 3d+r of the reduced series is nonzero. Hence

    ord_z P(z,F(z)) <= 3d+r <= 3d+deg A.

Multiplication by the nonzero rational 5^d does not change the order in
Q[[z]]. In particular, if P is monic in X, its vanishing order is at
most 3d, regardless of the z-degrees of the lower coefficients.
If A(1)=1, then A_bar is nonzero, so the bound with deg A also applies.

This rules out arbitrary high-order jets for this particular monic
construction. It does NOT rule out nonmonic auxiliary polynomials, does
not establish a height bound or nonvanishing at z=1, and does not apply
automatically to the Lambert generating function. In particular it
supplies no implication that F(1) is irrational or rational.

No complete proof or disproof has been obtained. Spec.lean is unchanged.
