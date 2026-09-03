# Fixed monic rational auxiliary functions: polynomial reduction

This is verified auxiliary work, NOT a settlement of Erdős 68. Spec.lean
remains unchanged with its original sorry. No proof or disproof has been
obtained or submitted.

MonicRationalForms.lean compiles without warnings, has a built olean, and
its three printed axiom audits use only propext, Classical.choice, and
Quot.sound.

## Exact reduction

Let R_k(X)=(X+1)...(X+k)-1. For integer polynomials P,Q, with Q monic,
polynomial division gives

    P div (Q*R_k) = (P div Q) div R_k.

The file proves this by uniqueness of monic division, explicitly checking
the remainder-degree bound. Adding an integer constant to P div Q does
not change any quotient by R_k, since every R_k has positive degree.

For any integer A, set

    H = P div Q + A - (P div Q)(1).

Then H is an integer polynomial, H(1)=A, and all the above quotient
contributions equal H div R_k. In particular, when Q(1) is nonzero and
P(1)=A*Q(1), the proposed rational-auxiliary row values

    [P(1)/Q(1)]/R_k(1) - [P div (Q*R_k)](1)

are exactly the already studied integer-polynomial row values for H.
Their convergent sum is A*alpha-B with B integral.

Principal declarations:
* quotient_product
* quotient_add_constant
* polynomial_replacement
* hasSum_rational_rows

## Scope

A fixed monic denominator does not enlarge this construction's set of row
values. This is not an impossibility theorem for useful polynomial forms,
and does not rule out rational functions as helpful parametrizations or
as tools for estimating particular forms. It also does not cover arbitrary
nonmonic denominators or row-dependent auxiliary functions.

No nonzero vanishing-error family was obtained. The original conjecture is
still unresolved in this workspace.
