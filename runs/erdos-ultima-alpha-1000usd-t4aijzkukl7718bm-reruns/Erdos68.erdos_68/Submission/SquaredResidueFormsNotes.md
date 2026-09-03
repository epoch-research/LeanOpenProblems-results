# Squared-residue obstruction (verified auxiliary work)

This does not settle Erdős 68. `Submission/Spec.lean` is unchanged and
still contains its original `sorry`. No proof or disproof was submitted.

`Submission/SquaredResidueForms.lean` compiles without warnings. Its built
olean is `.lake/build/lib/lean/Submission/SquaredResidueForms.olean`.
The three principal axiom audits list only `propext`, `Classical.choice`,
and `Quot.sound`.

Write d_n=(n+2)!-1 and alpha=sum_n 1/d_n. For A a natural number,
a finite set s, and arbitrary integers b_n on s, define

    B = sum_(n in s) (2 A b_n-d_n b_n^2),
    L = A^2 alpha-B.

Extending b_n=0 outside s gives the exact convergent positive expansion

    L = sum_(n>=0) (A-d_n b_n)^2/d_n.

This is `hasSum_residueRow`. The boundary B is integral by definition.
If d_n>2A, every choice of b_n has (A-d_n b_n)^2>=A^2.
Consequently L>=A^2/d_n at any such row.

## Uniform lower bound

For A>0, there is an n with 2A<d_n<=5A^2. Use the first crossing
of 2A, the recurrence d_(m+1)=(m+3)d_m+(m+2), and
`d_(m+1)<d_m^2` for m>=1; the exceptional transition is d_0=1,d_1=5.
Thus `one_fifth_le_form` proves

    A>0 ==> 1/5 <= L,

uniformly over s and all integral choices b_n.

## Uniform divergence

`large_le_form` proves the stronger explicit bound

    R>=1 and A>=34 R^2 ==> R<=L,

again uniformly over s and b_n.

At a crossing d_m<=2A<d_(m+1), induction gives m^2<=d_m<=2A.
The recurrence gives d_(m+1)<=(3m+8)A. From (m-6R)^2>=0,
A>=34R^2, and R>=1, one obtains R(3m+8)<=A. Hence
R*d_(m+1)<=A^2, and the single-row lower bound proves the result.

## Scope

This rules out errors tending to zero from this particular squared-residue
construction, and shows that its errors grow when A grows. It does not
apply to arbitrary integer linear forms, arbitrary positive kernel families,
or signed combinations of these forms. It supplies no infinite carry-change
or GCD-defect nonvanishing theorem. The original irrationality conjecture
remains unresolved in this workspace; there is no complete informal proof
awaiting formalization and no pending computation.
