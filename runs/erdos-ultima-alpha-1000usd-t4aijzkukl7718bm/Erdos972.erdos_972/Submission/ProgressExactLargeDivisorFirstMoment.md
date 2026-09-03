# Exact large-divisor first moment — not a settlement

The original conjecture in Spec.lean is still unresolved and unchanged.
No prime-pair lower bound or irrational counterexample has been proved.

New verified file: ExactLargeDivisorFirstMoment.lean.
Namespace: Erdos972ExactLargeDivisorFirstMoment.
Its principal declarations compile and print only propext,
Classical.choice, and Quot.sound as axiom dependencies.

## Exact complementary-divisor identity

Define

    outputPrefix(alpha,m) = ceil((m+1)/alpha)-1

with NATURAL ceil and subtraction. For alpha>0, the file proves exactly

    floor(alpha*p) <= m  iff  p <= outputPrefix(alpha,m).

For alpha>=1, D>0, and floor(alpha*N)<=D*K, and ANY real input weight a,

    sum_{D<d<=2D} row(d,N)
      = sum_{0<k<=K} [row(k,min(N,outputPrefix(alpha,2Dk)))
                      - row(k,min(N,outputPrefix(alpha,Dk)))].

Both endpoints and their rounding are retained. This strengthens the
previous one-sided complementary-divisor switching inequality.

## Two-sided estimate and actual scales

For the actual prime weights, define B(alpha,N,D,K) by replacing each row
on the right by psi(endpoint)/k. This is `blockChebyshevMain` in the file.
Uniform small-row prefix error at most E gives

    |sum_{D<d<=2D} R_d - B(alpha,N,D,K)| <= 2*K*E.

The file proves the needed prefix estimates on actual irrational good
scales, including the full proper-prime-power error. In particular,

    root64(u)*primeRowError(u)/u^6 -> 0.

`exists_block_firstMoment_scale`: for every alpha>1 irrational, epsilon>0,
and initial bound, there is a larger positive u such that, with N=u^6,
SIMULTANEOUSLY for every D,K satisfying

    D>0, K<=root64(u), floor(alpha*N)<=D*K,

one has

    |sum_{D<d<=2D} R_d - B(alpha,N,D,K)| <= epsilon*N.

No new row-distribution assumption is present in this theorem.
No asymptotic B~N*log(2) is asserted or proved in this file.

## Retained centering

For any nonnegative row values R_d and center X>=0,

    sum_{D<d<=2D} (R_d-X/d)^2
      <= sum_{D<d<=2D} R_d^2
         -(X/D)*sum_{D<d<=2D} R_d + X^2/(2D).

The reciprocal-square bound is the exact standard bound <=1/(2D).
This keeps a negative cross term rather than discarding it.

`exists_explicit_centered_block_bound` combines both moments at ONE actual
scale. Under the preceding block conditions and additionally

    M>0, alpha*M<D, N<=D*M,

it proves the first-moment estimate above AND

    sum_{D<d<=2D} (R_d-psi(N)/d)^2
      <= M*log(N)*(14*D*K+epsilon*N/2)
         -(psi(N)/D)*(B(alpha,N,D,K)-epsilon*N)
         +psi(N)^2/(2D).

The first and second moments in this last theorem genuinely use the same
selected rational approximation and the same u. No intersection of
unrelated existential good-scale sets is assumed.

## Remaining gap

The raw second-moment contribution still contains the large multiplicity
bound with log N. The retained cross term does not establish the signed
four-factor lower gap, nor a positive prime-pair count. Intermediate and
balanced divisor ranges also remain unresolved. These are unconditional
auxiliary improvements, not a proof or disproof of Erdos 972.

No incomplete proof was submitted.
