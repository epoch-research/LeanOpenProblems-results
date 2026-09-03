# Quadratic-tail comparison (verified; NOT a disproof of Erdős 68)

`QuadraticTailComparison.lean` compiles and its olean has been built.
The axiom audits for `sum_coeff` and `comparison_properties` list only
`propext`, `Classical.choice`, and `Quot.sound`.

## Explicit construction

For natural n define the integer t_n by

    t_n = n-3             if n is even,
    t_n = n*(n-4)-1       if n is odd.

Set c_n=0 for n<5, and

    c_n = n*t_(n-1)-t_n   for n>=5.

Then:

* c_n=1 for every odd n>=5;
* for every even n>=6,

      c_n = (n-1)*(n*(n-5)-2)+1;

* all c_n are nonnegative integers;
* n divides c_(n+1)-1 for every n>=4;
* c_p=1 for every prime p>=5;
* 0<t_n<=n^2 for every n>=4.

Telescoping, with t_4=1, gives

    sum_(k=0)^n c_k/k! = 1/24 - t_n/n!   for n>=4.

The polynomial bound on t_n implies t_n/n! tends to zero. Consequently

    sum_(n>=0) c_n/n! = 1/24,

and the factorial-scaled tail is exactly t_n for n>=4.

## Consequence and limitation

The predecessor congruences, prime unit coefficients, nonnegative
coefficients, and positive tails bounded by n^2 do NOT force irrationality.
Thus the newer criterion with bound C*n*(floor(sqrt(n))+1) cannot simply be
extended to an unrestricted quadratic tail bound.

These are not the original Lambert or rowwise coefficients. This result
neither proves nor disproves irrationality of sum 1/(n!-1).
`Submission/Spec.lean` remains unchanged with its original `sorry`.
