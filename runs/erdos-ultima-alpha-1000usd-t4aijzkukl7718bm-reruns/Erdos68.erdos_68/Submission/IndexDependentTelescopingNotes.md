# Index-dependent polynomial kernels

These notes describe auxiliary results, not a solution of the conjecture.
The integer-polynomial identity, row-zero divisibility condition, and zero-form
example are now Lean-verified in `IndexDependentTelescoping.lean`. They extend
the polynomial-weight framework by allowing weights to depend on the row index,
so the extra moments can telescope.

Let alpha=sum_(n>=2) 1/(n!-1). Choose an integer A and finitely many
polynomials H_j(X) in Z[X], indexed by j=1,...,J, where J>=1. Define

    q_j(n) = n^j*H_j(n-1)-H_j(n),
    Q(n,t) = sum_(j=1)^J q_j(n)*t^(j-1),
    P(n,t) = A-(1-t)*Q(n,t).

## Exact elimination of the moments

For every j,

    q_j(n)/(n!)^j
      = H_j(n-1)/((n-1)!)^j - H_j(n)/(n!)^j.

Polynomial growth is dominated by factorial growth, so telescoping gives

    sum_(n>=2) q_j(n)/(n!)^j = H_j(1).

Also, term by term,

    P(n,1/n!)/(n!-1)
      = A/(n!-1) - sum_(j=1)^J q_j(n)/(n!)^j.

All series here converge absolutely. Consequently

    I = sum_(n>=2) P(n,1/n!)/(n!-1)
      = A*alpha - B,
    B = sum_(j=1)^J H_j(1) in Z.

Thus this extension really does eliminate the factorial-power constants.
It is not the earlier invalid step of assuming those constants rational.
The same argument works with rational polynomials H_j that are integer-valued
on the nonnegative integers.

## Divisibility forced by exact row cancellation

Suppose P(n,1/n!)=0 at a particular integer n>=2. Put F=n!. Since all
q_j(n) are integers, multiplication by F^J gives

    A*F^J = (F-1)*sum_(j=1)^J q_j(n)*F^(J-j).

The integers F and F-1 are coprime. Therefore F-1 divides A. In particular,
annihilating every row n=2,...,N forces

    lcm(2!-1,3!-1,...,N!-1) | A.

This conclusion is valid for these exact polynomial-kernel zeros. It does
not claim that individual denominators survive reduction of arbitrary mixed
approximations. Nor does it force factorial powers to divide A.

## Outstanding construction problem

To obtain an irrationality proof, one still needs a sequence of these kernels
with integer A and B for which

    0 < |I| -> 0.

Under alpha=a/b, the numbers b*I would then be nonzero integers tending to
zero. No such sequence, positivity argument, or adequate quantitative bound
has been established here.

There is a substantial zero-form subspace: if A=0 and
sum H_j(1)=0, then I=0 even when the polynomials and the termwise kernel are
nonzero. For example, J=1 and H_1(X)=X-1 gives a nonzero kernel with I=0.
Thus a nonzero coefficient vector from a homogeneous lattice argument would
not by itself ensure the required nonzero value.

The divisibility condition above also shows that exact initial-row zeros
retain a potentially large arithmetic cost. The identity alone supplies no
bound overcoming it. Submission/Spec.lean remains unchanged with sorry.

## Lean verification

`Submission/IndexDependentTelescoping.lean` compiles and its olean has been built.
In namespace `IndexDependentTelescoping`, it proves:

* `summable_eval_div_factorial_pow`: summability of integer-polynomial values
  divided by a fixed positive power of n!;
* `hasSum_rowCoeff`: the single-column telescoping identity;
* `hasSum_kernel`: the exact form A*alpha-B for any finite polynomial family;
* `denominator_dvd_of_kernel_zero`: an exactly cancelled row forces n!-1 | A;
* `nonzero_kernel_with_zero_sum`: the H(X)=X-1, A=0 example has a nonzero
  first kernel value but total sum zero.

The last three axiom checks list only propext, Classical.choice, and Quot.sound.
The formalization indexes original rows by n+2 and powers by j+1. The extension
to arbitrary integer-valued rational polynomials remains a mathematical remark,
not a declaration in this file. No small nonzero sequence has been constructed.
Spec.lean has not been changed and no proof has been submitted.
