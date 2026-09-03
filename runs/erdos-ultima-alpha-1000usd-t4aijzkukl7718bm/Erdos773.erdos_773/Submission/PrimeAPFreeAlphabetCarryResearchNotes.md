# Prime bases and weighted-average-free alphabets: a carry obstruction

This does NOT settle Erdős 773. Spec.lean has not been edited. Its sole
admission remains 0 < epsilon < 1/3; the completed unconditional endpoint
remains eventual M(N) >= N^(2/3).

## Verified module

Submission/PrimeAPFreeAlphabetCarry.lean imports only the independently
verified FormalGaussianSidon module, not Spec.lean. The complete source
compiles without errors, warnings, or admissions, and has a rebuilt olean.
All twelve printed audits use only propext, Classical.choice, Quot.sound.
Log: /tmp/prime-ap-free-alphabet.log.

For t >= 0, let B=1452t+509. Define

    P_j(X)=1+b_j X+a_j X^2, E_j(X)=X^3+6P_j(X),
    b=[66t+33,132t+34,66t+11,132t+56],
    a=[40t+9,181t+66,40t+18,181t+60].

Their digits are [6,6b_j,6a_j,1], all positive and canonical at radix B.
The constant is exactly 6 and the leading coefficient exactly 1. The
parameters are admissible for the Gaussian-Eisenstein construction, so the
four formal polynomial square values are Sidon. The exact certificate is

    E_0^2+E_1^2-E_2^2-E_3^2
      =36 X^2 (B-X)(X^2-4X-2).

It vanishes at X=B. The positive values satisfy

    E_0(B) < E_2(B) < E_3(B) < E_1(B).

The module proves both the integer and natural square-sum equalities and
both negated Sidon statements. Natural casts use checked nonnegativity.

## Progression-free alphabets

The parameter alphabet consists of slope_i*t+offset_i for

    offset=[1,9,11,18,33,34,56,60,66],
    slope =[0,40,66,40,66,132,132,181,181].

For t>=133 it is three-term-progression-free. The offset alphabet is
injective and AP-free by kernel decision. Reduction modulo t recovers an
actual AP of offsets, because every relevant sum lies below t.

No parameter letter is twice another. Hence adjoining zero preserves
AP-freeness; multiplying by six and adjoining the leading digit 1 also
preserves AP-freeness. The resulting digitAlphabet contains every root
digit. It includes an UNUSED zero. canonical_ap_free_digits proves this
membership, the fixed constant and leading coefficients, and the bounds.

## Every bounded positive weighted three-term average can be excluded

The positive actual digit table is

    digitOffset=[1,6,54,66,108,198,204,336,360,396],
    digitSlope =[0,0,240,396,240,396,792,792,1086,1086],
    positiveDigit(t,i)=digitSlope_i*t+digitOffset_i.

A kernel-checked determinant certificate says that no three distinct
(slope,offset) points in this table are collinear. If 1<=K and 792K<t,
no nontrivial relation

    u*a+v*c=(u+v)*b, 0<u,v<=K,

holds among these positive digits. Both weighted offset sums lie in
[0,792K], so reduction modulo t separates the offset equation from the
slope equation. The determinant certificate and positive-weight
cancellation force a=b (and the equation then also forces c=b).

coefficient_positiveDigit gives an explicit table index for every one of
the four coefficients of every root polynomial. positiveAlphabet is the
image of the ten positive digits; coefficient_mem_positiveAlphabet proves
that ALL the actual coefficients at positions 0 through 3 belong to it.
positiveAlphabet_weighted_free states the weighted property directly for
members of this alphabet, not just for table indices.

The unused zero is deliberately NOT adjoined in this weighted assertion:
0,1,6 already admit the weighted relation 5*0+1*6=6*1.

## Unbounded prime bases, with each fixed weight bound

Dirichlet's theorem and gcd(509,1452)=1 give arbitrarily large primes of
the form 1452t+509 with t>=133. arbitrarily_large_prime_obstruction
packages prime growth, AP-freeness, and failure of integer Sidonness.

arbitrarily_large_prime_weighted_obstruction proves, for EVERY fixed
natural K>=1 and EVERY requested prime lower bound M, existence of t with:

* B=1452t+509 prime and B>M;
* all positive weighted three-term averages with weights at most K trivial
  in the one shared positiveAlphabet;
* all four roots' coefficients canonical and belonging to this alphabet;
* the NATURAL square-value family not Sidon.

The prime bound max(M,1452*(792*K)+509) forces 792K<t. The formal Sidon
property, strict positivity, and value injectivity are separate uniform
verified APIs; the combined theorem does not repeat every one of them.

## Scope

This refutes only proposed SUFFICIENT digital specialization criteria.
The alphabet has ten positive entries; no growing or near-full alphabet
size is asserted. No common histogram or full-permutation property is
asserted, and this is not AllowedAlphabetCandidate. Root primality,
pairwise coprimality, and negative real polynomial roots are not asserted.
A four-root collision says nothing about the largest Sidon SUBSET of the
carrier, let alone an upper bound for all squares.

The continuation's review of finite checksums, restricted permutation
carriers, factor selection, amplification, and capacity-one extraction
supplied no original-conjecture exponent improvement. External reference
access failed at DNS resolution; no external result was used. No near-linear
selector or unrestricted fixed-power upper bound was obtained.
