# Rational-base specialization: verified obstructions

The original conjecture is NOT settled. Spec.lean has not been edited and
still has its sole sorry for 0 < epsilon <= 1/3. The failed original
submission has not been resubmitted. No actual lower exponent or fixed-power
upper bound for the square-Sidon maximum improved.

## Three completed clean modules

1. RationalGaussianSpecialization.lean
2. RationalDigitInjection.lean
3. SmallRationalGaussianSpecialization.lean

All compile without warnings or admissions and have built oleans. Their
25 printed audits use only propext, Classical.choice, Quot.sound. None
imports Spec.lean.

## Stronger degree-42 obstruction

Namespace Erdos773.SmallRationalGaussianSpecialization.

For every natural t, the module supplies coprime p=q+1 and q>0, four
polynomials E_i(X)=X^42+6 P_i(X), and four positive natural roots n_i.
The parameter polynomial has degree below 42 and constant coefficient one.
The statements proved include:

* formal_sidon: {E_i(X)^2} is Sidon in Z[X], by the existing Gaussian
  Eisenstein theorem.
* coefficient_nonneg: all coefficients of each E_i are nonnegative.
* small_digits: 100*(6*a_ij)<q for the 41 nonconstant lower digits.
  The common constant encoding coefficient is six.
* small_total and eval_one: the sum of ALL encoding coefficients,
  including the leading one and constant six, is less than q.
* evaluation: q^42 E_i(p/q)=n_i exactly, over the rationals.
* collision: n_0^2+n_1^2=n_2^2+n_3^2.
* nontrivial and not_sidon: this is a genuinely nontrivial square-sum
  collision.
* cleared_injective: all FOUR n_i are distinct.
* denominator_unbounded: for every B, B<q(B).
* specialization_obstruction: packages the principal conditions; the
  subsequent cleared_injective theorem supplies the stronger injectivity
  conclusion separately.

Thus even small absolute positive digits, small total coefficient sum,
formal Gaussian Sidonness, and injective evaluation do not suffice for
rational-base specialization. The denominators in this construction are
composite multiples of a fixed 57-digit integer. NO prime-denominator
claim is made. No common-histogram or common-moment assertion is made.
The total coefficient sums are small but are not asserted equal.

## Exact algebraic source

Write p=z+1. The factor certificate is

  F=1+z^2*p^2,
  U=10^(-18)*z^2*p^2,
  V=10^(-18)*z^2*p^37.

G is an explicitly certified rational polynomial of degree 39. The four
cleared root polynomials are

  FG-UV-FV-GU,
  FG-UV+FV+GU,
  FG+UV-FV+GU,
  FG+UV+FV-GU.

Their square-sum identity is verified algebraically in Lean. raw_factor
checks the connection with the literal digit coefficient table. G need
not have positive coefficients: G_positive is correctly deduced at the
chosen denominators from positivity of the first actual root, F>U>0,
and V>0. No unsupported positivity assumption on G is used.

The exact coefficient search used the reciprocal polynomial

  (X-1)^4+X^2.

X has order 30 in its quotient modulo 6. At degree 42, integer shifts
make the unperturbed residual equal X^12. A finite linear system then
supplies small positive rational slopes. Gaussian factor perturbations
preserve positivity. The final Lean proof checks the literal rational
identities and inequalities; it does not trust the optimization solver.

The actual digit coefficients have form

  a_ij = c_ij*(t+T)+v_j,
  q = L*(t+T), T=524783238375.

They are encoded naturally using a nonnegative integer offset. L and all
c_ij are literal natural numbers in the Lean file. The finite coefficient
budgets, integer offset bounds, rational factor identity, and all casts
are checked in Lean.

## Generic evaluation-injectivity lemma

RationalDigitInjection.eval_injective proves that if p,q are coprime,
q>0, and |coeff(P,n)-coeff(Q,n)|<q for all n, then equality of P(p/q)
and Q(p/q) implies P=Q. The proof uses the rational root theorem and the
divisibility of the reduced denominator into the leading coefficient.

This is about individual-value injectivity, NOT preservation of Sidonness.
For the degree-42 example, nonnegative coefficients and total sum <q
supply its hypotheses. The coefficient at degree 37 distinguishes the
four parameter polynomials. This proves cleared_injective without an
unverified numerical comparison of enormous evaluated roots.

## Earlier degree-13 obstruction

RationalGaussianSpecialization.specialization_obstruction gives a simpler
family with q=234000000000000*(t+1), p=q+1, and degree 13. Its coefficients
are nonnegative, and their coordinatewise variations are less than q/1000.
It does NOT have small absolute digits. All four evaluated roots are
proved distinct, and the formal squares are Sidon while the cleared
integer squares are not. Its generic factors use epsilon=10^(-6).
The degree-42 result addresses the absolute-digit gap left by this example.

## Sources and logs

Exploratory/exact rational certificate scripts and data:

  Research/RationalBaseLP.py
  Research/RationalBaseExactCertificate.py
  Research/RationalBaseData.json
  Research/RationalSmallAbsoluteLP.py
  Research/RationalSmallAbsoluteStable.py
  Research/RationalSmallAbsoluteCertificate.py
  Research/RationalSmallAbsoluteData.json

Failed floating-point feasibility checks are NOT nonexistence theorems.
All used certificates were subsequently checked exactly and then in Lean.

Build/audit logs:

  /tmp/rational-gaussian-specialization.log
  /tmp/rational-digit-injection.log
  /tmp/small-rational-gaussian.log

The main problem still requires a genuinely successful square-specific
selector or a fixed-power upper bound for arbitrary square-Sidon subsets.
These counterexamples concern a proposed sufficient construction, not the
original asymptotic conjecture.
