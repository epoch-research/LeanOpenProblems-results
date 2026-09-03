# Rising-factorial factors added to the monic product kernel

This is an exact external construction test, not a Lean theorem or a
settlement of Erdős 68. Spec.lean is unchanged with its original sorry.
No proof or disproof has been obtained or submitted.

## Family

Use the monic row polynomials

    R_k(x)=product_(i=1)^k(x+i)-1.

For K,N>=0 and shift s in {0,1}, test

    P_(K,N,s)(x) = product_(k=1)^K R_k(x)
                    * product_(i=0)^(N-1)(x+s+i).

The first K rows still vanish. As in the already verified general theorem
RisingMonicForms.integer_form_identity, the integral pair is

    A=P(1),
    B=sum_(k=1)^(degree P) (P div R_k)(1).

The test divides (A,B) by its gcd before estimating the error. Multiplying
P by 1/N! (the corresponding integer-valued-binomial normalization) would
not change this reduced pair. No termwise denominator lower bound is assumed.

The motivation was that roots of the added factor lie at consecutive
nonpositive integers, near many roots of the row polynomials. The test does
not establish a general root-location bound or a sign theorem.

## Exact finite test

Parameters:

    K=1,...,10,
    N in {0,K,2K,K(K+1)/2,K^2,2K^2}, duplicates removed,
    s=0,1 for N>0; only s=0 for N=0.

There are 100 cases. Every monic quotient/remainder identity is checked
exactly in ZZ[x], including the remainder degree. All coefficient pairs
are reduced exactly.

For error certification, put W=2000! and

    L=sum_(k=2)^2000 floor(W/(k!-1)).

The elementary positive-tail estimate gives

    L/W < alpha < (L+2002)/W.

For each reduced pair a,b with a>0, the program checks the exact rational
interval for a*alpha-b. No floating-point result determines a sign or a
less-than-one classification. Decimal logarithms are diagnostics only.

Results:

* 5 cases have errors in (0,1);
* 8 cases have errors in (-1,0);
* 49 cases have errors greater than 1;
* 38 cases have errors less than -1;
* no interval classification is ambiguous;
* all 77 cases with K>=4 have absolute error greater than one.

The small cases (K,N,s,a,b) are

    (1,0,0,1,1), (1,1,0,1,2), (1,1,1,2,3),
    (1,2,0,1,1), (1,2,1,3,4),
    (2,0,0,5,7), (2,2,0,5,6), (2,2,1,5,6),
    (2,3,1,120,151), (2,4,0,15,19), (2,4,1,50,63),
    (2,8,1,5400,6769), (3,0,0,115,144).

Artifacts:

    /tmp/rising_product_shifted_test.py
    /tmp/rising_product_shifted_test.log
    /tmp/rising_product_shifted_test.json

The computation completed; no process is running. Its finite failures do
not prove an asymptotic obstruction and do not exclude other polynomials.
They supply no controlled sequence of nonzero small integer forms.

## Other review in this pass

The carry and row-GCD recurrences were reviewed, but no arithmetic exclusion
of eventual stabilization was obtained. Prime-base computations do not imply
an all-prime nonconstancy theorem. A renewed local-library search found no
applicable irrationality theorem for the exact factorial-minus-one sum.
No new complete informal argument is awaiting Lean formalization.
