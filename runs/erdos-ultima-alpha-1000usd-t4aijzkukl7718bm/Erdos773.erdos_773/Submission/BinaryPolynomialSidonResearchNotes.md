# Binary-polynomial squares: formal Sidonness and evaluation failure

The original Erdős 773 conjecture remains UNSETTLED. Spec.lean was not edited.
The actual unresolved exponent range remains 0<epsilon<1/3; the separately
verified coefficient-one two-thirds endpoint has not been reconsolidated.

## New checked module

Submission/BinaryPolynomialSidon.lean imports only FormalConjecturesUtil.
Its five printed audits use only propext, Classical.choice, Quot.sound.
It builds without warnings or admissions, and has a built olean.
Namespace: Erdos773.BinaryPolynomialSidon.
Log: /tmp/binary-polynomial-sidon.log.

## General algebraic theorem

transversal_pair_matching assumes a characteristic-zero domain R, a
characteristic-two domain S, a ring homomorphism f:R->S with kernel
contained in 2R, and a subset A on which f is injective. It proves:

    a,b,c,d in A and a^2+b^2=c^2+d^2
      ==> (a=c and b=d) or (a=d and b=c).

Reducing the norm equality gives f(a)+f(b)=f(c)+f(d). Thus
 a+b-c-d=2t. Substitution and cancellation of two give

    (a-c)(a-d)+2t(c+d-a+t)=0.

Reduction to S makes the product (f(a)-f(c))(f(a)-f(d)) zero.
The domain condition and injectivity on A identify the two pairs.

## Formal binary-polynomial application

Take R=Z[X], S=F2[X], f=coefficient reduction modulo two. Binary P means
every coefficient is zero or one, with no degree, leading, or constant
coefficient restriction. Polynomial.C_dvd_iff_dvd_coeff proves the kernel
condition, and coefficientwise binary reduction is injective.

binary_pair_matching and binary_squares_sidon prove that the ENTIRE
infinite set of squares of binary-coefficient polynomials is Sidon in Z[X].
This is not a claim about integer roots or integer evaluation.

## Exact transfer failure

The binary words

    P=1+X, Q=1+X+X^3, R=1+X+X^2, S=1+X^3

satisfy the formal nonzero discrepancy identity

    P^2+Q^2-R^2-S^2 = X(X-2)(X-1)(X+1).

At base two their roots are 3,11,7,9, so

    3^2+11^2=7^2+9^2=130.

example_discrepancy and binary_evaluation_not_sidon check the polynomial
identity and the failure of Sidonness of the full evaluated family.
No native computation or assumed specialization is used.

## Main task status

The new theorem supplies no integer exponent gain. The simultaneous sum
and difference capacity results were also reconsidered, but no square-
specific subpower-loss extraction to capacity one was obtained. The old
generic obstructions remain ordinary integer sets, not square counterexamples.
No original-conjecture proof or negation is claimed, and no incomplete
proof was submitted.

Spec.lean SHA-256 remains
f019ff3791c89bbea24fd9b031eb92f7b676baa4b1ff9cebe9f2356121aa6ff0.
The original theorem is at line 2027 and its sole sorry is at line 2035.
