# Finite-row Gauss–Radau approximation with the largest node prescribed

This is an exact external arithmetic test, NOT a Lean-verified theorem and
NOT a settlement of Erdős 68. Spec.lean remains unchanged with its original
sorry. No proof or disproof has been submitted.

## Distinct construction

Let

    H_N(z)=sum_(k=2)^N 1/(k!-z),
    c_j(N)=sum_(k=2)^N 1/(k!)^(j+1).

The finite moments c_j(N) are rational. The corresponding infinite moments
are irrational factorial-power constants and were NOT used as rational
coefficients.

For m>=1, write Q(z)=1+sum_(j=1)^m q_j z^j. Solve

    Q(2)=0,
    [z^k](Q H_N)=0 for k=m,...,2m-2.

Let P be the degree-(m-1) truncation of Q H_N and put R=P(1)/Q(1).
The prescribed pole corresponds to the largest support node x=1/2 in
H_N(z)=sum x_k/(1-z*x_k), x_k=1/k!. This is different from the earlier
unconstrained [m-1/m] finite Stieltjes Padé test.

The script checks every defining equation, Q(1)!=0, and R>S_N exactly,
where S_N=sum_(k=2)^N 1/(k!-1). No numerical solver output is trusted.
The general Gauss–Radau sign theorem is not asserted as Lean-verified here.

## Completed finite test

Parameters:

    m=1,...,12;
    N in {m+2,2m+2,4m+2}, duplicates removed.

All 36 systems were solved. Write the fully reduced R=B/A with A>0.
The error A*alpha-B is enclosed by exact rational arithmetic using

    W=2000!,
    L=sum_(k=2)^2000 floor(W/(k!-1)),
    L/W < alpha < (L+2002)/W.

Results:

* 27 certified errors were greater than one;
* 8 certified errors were less than minus one;
* the single case (m,N)=(1,3) had error strictly between minus one and zero;
* no case was ambiguous.

For m>=2 all tested scaled errors had absolute value greater than one.
Both signs occur: the positive omitted row tail can exceed the negative
finite-quadrature error, so the finite-row upper-bound sign must not be
transferred automatically to alpha.

Selected diagnostic logs (the certificates themselves use exact intervals):

    m   N   denominator bits   log10 |A*alpha-B|
    2   4          10                    0.922953
    2   6          28                    4.977358
    6  26        2723                  793.431918
   12  14        1893                  557.588166
   12  50       26470                 7902.048390

Artifacts:

    /tmp/stieltjes_radau_factorial.py
    /tmp/stieltjes_radau_factorial.log
    /tmp/stieltjes_radau_factorial.json

The computation has completed; nothing is running. These finite failures
are not an asymptotic impossibility theorem and do not exclude other
quadrature constructions. No family with controlled integral coefficients,
nonzero error, and error tending to zero was obtained.

## Other review in this pass

The common-leading-coefficient / one-sided approximation gap for the
factorial-power columns remains. Ordinary two-sided Dirichlet bounds do not
supply the needed sign or nonvanishing. The reduced rowwise tails have
sublinear bounds but still lack a proved late residue violation. No new
Lean declaration or complete informal proof was obtained in this pass.
