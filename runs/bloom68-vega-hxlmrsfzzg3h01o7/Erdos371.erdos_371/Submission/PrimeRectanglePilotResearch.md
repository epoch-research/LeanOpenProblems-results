# The .6/.9 prime rectangle: bounded feasibility attempt

## Outcome

No positive eta for the requested pilot is proved here. In particular, this is not a proof of the natural-density target in Erdős 371. The concrete estimates obtained in this attempt are:

* Replacing BOTH prime indicators by Lambda(n)/log(n), keeping coprimality, costs **O(X^(19/10)) in the mean square of the error**. This is not a claim that the two energies differ by O(X^(19/10)).
* The entire same-prime-modulus contribution, including unequal q's, is **O(X^(8/5))**.
* With a suitable small Vaughan cutoff on the Q variable, all its Type I terms are **O_A(X^(-A))**, pointwise for the relevant h. This uses the zero complete mean of the sine, not a conjectural bound for primes.
* What remains is a signed distinct-prime-modulus correlation, displayed explicitly in (13) and (15). Ordinary large sieves give X^(11/5), leaving a saving greater than X^(1/5) still to obtain. The checked trilinear and unbalanced-convolution theorems do not supply it.

No specification or Lean file was accessed. No countermodel or formalization is used.

## 1. Normalization and reciprocity

Throughout,

    P = X^(3/5), Q = X^(9/10), H = floor(X^(1/2)),
    E(F) = (1/H) sum_{1 <= h <= 2H} |F(h)|^2.

All implicit constants may depend on the fixed smooth real functions U,V, supported inside (1,2). We take X sufficiently large that 2H<P and 2Q<P^2. Put

    S(h) = sum_{p,q prime} U(p/P)V(q/Q) sin(2 pi h (inverse q mod p)/p).

Reciprocity, with least positive inverses, gives

    (inverse p mod q)/q + (inverse q mod p)/p = 1 + 1/(pq).

Consequently

    K_X(h) = -S(h) + O(h),
    E(K_X+S) = O(H^2) = O(X).                              (1)

One can put two logarithms in the pointwise error, but they are unnecessary.

Define rho(n)=Lambda(n)/log(n) for n>=2. Thus rho(p^j)=1/j and rho is zero elsewhere. Define the coprime sum

    T(h) = sum_{m,n >= 2, (m,n)=1}
             rho(m)rho(n)U(m/P)V(n/Q)
             sin(2 pi h (inverse n mod m)/m).               (2)

The exclusion (m,n)>1 is retained in every convolution below. In particular, configurations m=l^2,n=l^3 are NOT silently assigned inverses.

## 2. Prime powers are harmless in mean square, not by trivial deletion

The following uses only the usual additive and primitive-character multiplicative large sieves. No GRH, small-modulus BDH asymptotic, or individual prime-progression asymptotic is assumed.

### 2.1 Proper prime powers in the Q variable

First keep p prime and replace q-primality by rho(q). The error R_Q is supported on a set B of O(sqrt(Q)) proper prime powers. Its coefficients b_n=rho(n)V(n/Q) are bounded. Since p>sqrt(2Q), all these n are coprime to p. For a in (Z/pZ)^*, put

    c_{p,a} = sum_{n in B, inverse n mod p = a} b_n.

A pair n!=n' in (Q,2Q) can be congruent modulo at most one prime p in (P,2P): the product of two such primes exceeds |n-n'|. Therefore

    sum_{p~P} sum_a |c_{p,a}|^2
       << P sqrt(Q) + Q.

For the sine use the odd coefficients (c_{p,a}-c_{p,-a})/2; their squared norm does not increase. The reduced fractions a/p are distinct and separated by at least 1/(4P^2). The additive large sieve proves

    E(R_Q) << (1+P^2/H)(P sqrt(Q)+Q)
             << X^(7/4).                                  (3)

Trivial pointwise deletion would only give O(P sqrt(Q))=O(X^(21/20)), and would not suffice.

### 2.2 Proper prime powers in the P variable

Now let m range over proper prime powers in (P,2P), and let n carry rho(n)V(n/Q). This error R_P includes configurations where both variables are proper prime powers, always with (m,n)=1.

For any such m, write

    A_m(a)=sum_{n~Q, n=a mod m} b_n,  b_n=rho(n)V(n/Q),
    Delta_m(a)=A_m(a)-A_m(-a),  (a,m)=1.

Character orthogonality gives

    sum_{a mod m}^* |Delta_m(a)|^2
       = 4/phi(m) sum_{chi mod m, chi(-1)=-1}
                         |sum_n b_n chi(n)|^2.             (4)

The principal character is absent. If m=l^k, every character in (4) is induced by a primitive character of conductor l^j, j>=1. The induced and primitive characters agree on every integer, including their zeros on multiples of l. Moreover, a given primitive character can occur for at most one m=l^k in the open dyadic interval (P,2P). Since phi(m)>=m/2, the primitive-character large sieve gives

    sum_{m~P, proper prime power} sum_a^* |Delta_m(a)|^2
       << ((P^2+Q)/P) sum_n |b_n|^2
       << ((P^2+Q)/P) Q.                                  (5)

This conductor argument is why no invalid uniform BDH estimate for all composite moduli is needed.

There are O(sqrt(P)) such m. Cauchy only over this sparse error set, followed by extending the nonnegative h-square sum to a full period modulo each m, gives

    E(R_P) << sqrt(P) (P/H)
                    sum_{m~P, proper prime power} sum_a^* |Delta_m(a)|^2
             << sqrt(P) Q(P^2+Q)/H
             << X^(19/10).                                (6)

Here complete Fourier Parseval is applicable to the inverse-residue permutation; explicitly the full-period sine square sum is (m/4) sum_a^* |Delta_m(a)|^2.

Combining (1), (3), and (6), Minkowski gives the useful, correctly normalized conclusion

    | sqrt(E(K_X)) - sqrt(E(T)) | << X^(19/20).             (7)

Thus a bound E(T)<<X^(2-eta), for any fixed 0<eta<1/10, would prove the requested pilot with that eta. Equation (7) is NOT a proof of that bound.

## 3. Actual Vaughan sums in both variables

Write L(n)=log n, 1(n)=1, and let a subscript <=z or >z denote restriction of an arithmetic function. The exact convolution identity is

    Lambda = mu_{<=z} * L
             - mu_{<=z} * 1 * Lambda_{<=z}
             + mu_{>z} * 1 * Lambda_{>z}
             + Lambda_{<=z}.                              (8)

On a band Y<n<2Y with z<Y the last term vanishes. More explicitly, define

    c_z(d)=sum_{ab=d, a<=z, b<=z} mu(a)Lambda(b),
    B_z(v)=sum_{b|v, b>z} Lambda(b),  0<=B_z(v)<=log v.

Then the three actual coefficient families are

    I_1: sum_{d<=z} mu(d) sum_v (log v) F(dv),
    I_2: -sum_{d<=z^2} c_z(d) sum_v F(dv),
    II:  sum_{d>z} mu(d) sum_{v>z} B_z(v) F(dv).            (9)

The smooth factors 1/log(dv), U(dv/P), V(dv/Q) belong to F; no logarithmic prime weight is simply dropped.

Apply (8) to BOTH rho factors in (2). After dyadic subdivisions the actual sums have the form

    sum_{d~D,v~M,a~A,b~B, (dv,ab)=1}
       alpha(d) beta(v) gamma(a) delta(b)
       [U(dv/P)/log(dv)] [V(ab/Q)/log(ab)]
       sin(2 pi h (inverse ab mod dv)/(dv)),                (10)

with DM comparable to P and AB comparable to Q, and with each coefficient pair exactly one of (9). These are not arbitrary modulus phases. The signs and coefficients in (8) must remain part of the argument.

### The Q-Type I part can actually be removed

Take, for example,

    z_Q = X^(7/50) = X^.14.

Its Type I divisor d is at most z_Q^2=X^.28, so the unrestricted variable has length

    N=Q/d >= X^.62,
    N/m >> X^.02  for every m in (P,2P).

If (d,m)>1 the coprime summand vanishes. Otherwise

    v -> 1_{(v,m)=1} sin(2 pi h (inverse dv mod m)/m)

is periodic modulo m and has complete mean zero by v->-v. For any fixed smooth band weight W (including the logarithmic ratios in (9)), Fourier expansion and Poisson summation give

    sum_v W(v/N) 1_{(v,m)=1}
                  sin(2 pi h (inverse dv mod m)/m)
       <<_A N (m/N)^A.

The derivatives of these weights are uniform in the permitted d,m. Choosing A as large as necessary absorbs the polynomial number of m,d and their divisor-bounded coefficients. The total Q-Type I contribution to (2) is therefore O_C(X^(-C)), for every C, uniformly for 1<=h<=2H. This estimates the Type I terms, rather than merely naming them. The same argument by Poisson in residue progressions bounds their odd residue differences uniformly.

Only Q-Type II remains. Taking z_P=P^(1/3)=X^.2 displays, among the remaining blocks, the genuinely balanced II-by-II sum

    d,v ~ X^.3,  a,b ~ X^.45,
    coefficients mu(d) B_{z_P}(v) mu(a) B_{z_Q}(b),          (11)

with precisely the weights, inverses, and coprimality in (10). The entire signed identity in the P variable, not just this one block, is retained. No bound for the blocks sufficient to close (7) is obtained here.

## 4. Signed energy: the entire same-modulus term is small

For the original prime sum define

    u_p=U(p/P),  v_q=V(q/Q),
    A_p(a)=sum_{q prime, q=a mod p} v_q,
    Delta_p(a)=A_p(a)-A_p(-a),
    F_p(h)=sum_{q prime} v_q sin(2 pi h (inverse q mod p)/p),
    C_H(t)=(1/H)sum_{h=1}^{2H} cos(2 pi h t).

Expanding AFTER both prime sums gives exactly

    E(S) = (1/2) sum_{p,r,q,s prime} u_p u_r v_q v_s
      [ C_H((inverse q mod p)/p - (inverse s mod r)/r)
       -C_H((inverse q mod p)/p + (inverse s mod r)/r) ].    (12)

Neither cosine term has been bounded separately.

Separate D=sum_p u_p^2 E(F_p) and the p!=r contribution O. As in (4), all characters occurring in the odd residue variance are odd and hence, for prime p, primitive. The multiplicative large sieve implies

    sum_{p~P} sum_a^* |Delta_p(a)|^2 << ((P^2+Q)/P) Q << PQ.

Parseval and 2H<p now give

    0 <= D << (P/H) PQ = P^2 Q/H = X^(8/5).

Thus even the additional coincidences q=s mod p and q=-s mod p are not the bottleneck; this goes beyond removing the literal repeated pair.

### Exact distinct-prime-modulus CRT correlation

For p!=r the map from the two inverse residues to k modulo pr is bijective on units. Reindexing both cosine sums in (12), and then pairing k with -k, gives

    O = -(1/4) sum_{p!=r, p,r prime} u_p u_r
          sum_{k mod pr, (k,pr)=1} C_H(k/(pr))
             Delta_p(r inverse k mod p)
             Delta_r(p inverse k mod r).                  (13)

For clarity, the intermediate unsymmetrized formula is

    (1/2) sum_k C_H(k/(pr)) A_p(r inverse k mod p)
      [ A_r(-p inverse k mod r)-A_r(p inverse k mod r) ].

This fixes both the minus sign and the factor 1/4 in (13). It also shows explicitly where the cosine-difference subtraction survives.

The kernel obeys

    |C_H(t)| << min(1, 1/(H ||t||)).

Its central spacing window is |k| << pr/H, of size P^2/H=X^.7; this is a window, not an exact sharp cutoff. No absolute value is taken separately on the two orientations.

Opening a Q-Type II odd residue factor gives the explicit convolution

    Delta_p^II(x) = sum_{d>z_Q,v>z_Q} mu(d) B_{z_Q}(v)
                  V(dv/Q)/log(dv)
                  [1_{dv=x mod p}-1_{dv=-x mod p}].         (14)

Thus (13), with the Q von Mangoldt weights, is the signed average of

    sum_{sigma,tau in {+1,-1}} sigma tau
      1_{k d v = sigma r mod p}
      1_{k e w = tau p mod r},                             (15)

weighted by C_H(k/(pr)), by both prime-modulus weights, and by

    mu(d)B_{z_Q}(v) mu(e)B_{z_Q}(w)
    V(dv/Q)V(ew/Q)/(log(dv)log(ew)).

The Q-Type I errors in this formula are negligible by the progression version of the argument in section 3. The Q proper-prime-power error has the mean-square bound (3), so it can be transferred using Minkowski. If an additive energy comparison is desired, the available baseline E(S)<<X^(11/5) and (3) even give

    | E(S with rho on Q) - E(S) | << X^(79/40),

which is below X^2. This last assertion concerns only the Q replacement, not both replacements.

Equations (13)-(15), or the full signed double-Vaughan family (10), are the remaining bottleneck. They require a correlation estimate between distinct prime moduli with varying residues, not an estimate for one prime progression at a time.

## 5. Quantitative tests of the cited tools

### Ordinary large sieves: exactly the outstanding X^.2 loss

Applying the additive large sieve to the inverse-residue odd coefficients, followed by the primitive-character large sieve just used, gives

    E(S) << (1+P^2/H) PQ << X^(11/5).                       (16)

This is the baseline in the question, not an improvement claimed here. Since D is only X^(8/5), the missing estimate is a saving greater than X^(1/5) in the distinct-modulus part (13). Complete cancellation of the principal character has already been used in (16); invoking oddness a second time does not improve it.

Even an assumed individual square-root estimate |F_p(h)|<<sqrt(Q) would, after taking absolute values over p, give E(S)<<P^2 Q=X^(21/10). That route is therefore stopped rather than promoted to an argument.

### Bettin--Chandee: actual theorem, not its Lindelof-strength conjecture

The checked theorem is Theorem 1 in arXiv:1502.00769, source lines 47-53. For

    sum_{a,m,n} nu_a alpha_m beta_n e(a inverse m mod n)

it gives, when a~A,m~M,n~N,

    ||nu||_2 ||alpha||_2 ||beta||_2 (1+A/(MN))^(1/2)
      [ (AMN)^(7/20+epsilon)(M+N)^(1/4)
       +(AMN)^(3/8+epsilon)(A(M+N))^(1/8) ].

For the frequency-dual pilot, A=H, M=Q, N=P, ||nu||_2=1, and the other two norms are at most X^(.75+epsilon). Both terms give a dual bound X^(67/40+epsilon). After dividing its square by H this is only X^(57/20+epsilon), worse than (16). The desired dual bound is X^(5/4-eta/2).

Grouping the factors in (10) and then quoting this theorem discards precisely the arithmetic information one was trying to use. I do not continue that route. The conjectural stronger trilinear estimate is not assumed; the same source explicitly notes its Lindelof consequence at line 72.

### Fouvry--Radziwill and well-factorable moduli

The checked input is Corollary 1(i) of arXiv:1811.08672, source lines 66-77. For a convolution of total length t and modulus R it requires its short Siegel--Walfisz factor to satisfy

    N <= R^(-11/12) t^(17/36-rho),  rho>0.

Here t=Q and R=P, so the right side is

    X^(-1/8-(9/10)rho) < 1.

The admissible factor range is empty, even before asking for a correlation of two varying residues. Treating (15) as a length-Q^2 problem with modulus P^2 gives the same relative obstruction. The theorem's fixed-residue L1 statement is also not the required signed four-prime correlation.

A well-factorable modulus weight at level R vanishes at primes greater than sqrt(R): use its balanced factorization. Hence a prime-modulus coefficient supported on p~P cannot be inserted directly into such a theorem at any level R<P^2. Opening it by (8) is an exact identity, not a license to replace it by arbitrary or well-factorable phases while discarding the remaining terms.

Irving's arXiv:1301.6372 supplies useful averages of absolute Kloosterman-prime sums; its introductory Theorems 1 and 2 are explicitly L1 over moduli. Such an input loses the cross-prime-modulus sign in (13). It is not used as a substitute for that missing correlation.

## 6. Verification and stopping point

`PrimeRectanglePilotVerification.py` independently checks:

* reciprocity with exact rational arithmetic;
* the Vaughan identity including the small-Lambda term, with formal prime-log coefficients;
* inverse-residue Parseval for prime and prime-power moduli;
* the full signed cosine expansion and the CRT formula (13), including weights of both signs;
* sparse proper-prime-power collision counting;
* uniqueness of the prime-power lift of a primitive conductor in a dyadic interval;
* the rational exponents in (3), (6), (16), and the cited-theorem substitutions.

Running `python3 Submission/PrimeRectanglePilotVerification.py` passed all **37,745** recorded checks. These are checks of identities and bookkeeping, not numerical evidence for the asymptotic pilot. The analytic bounds above follow from the stated large-sieve and Poisson arguments.

**Stopping point:** no estimate improving (13) to O(X^(2-eta)) has been obtained. The frequency average, the odd projection, the same-modulus contribution, the prime powers, and the free Type I variables have all been accounted for. The remaining step would have to exploit the actual two-prime/convolution coefficients across distinct moduli, beyond the tested ordinary large sieves and cited trilinear theorem. It is not supplied by a reflection identity or by separately estimating the two cosine terms.

## 7. Subsequent audit and the weaker cofactor-count target

An independent audit confirmed the auxiliary estimates above, and the main
process reran all 37,745 finite checks. No bound for the outstanding signed
covariance was obtained. When localizing the Type I proof into separate
free-variable blocks, those cutoffs must be smooth.

The full energy pilot is stronger than necessary. For A=X^.4, B=X^.1,
P=X^.6, Q=X^.9, one can instead ask for the signed smooth count D of
ap-bq=+1 minus ap-bq=-1, with a~A,b~B and p~P,q~Q prime. The meaningful
raw-prime target on this *fixed dyadic* rectangle is D=o(X/log^2 X).
Merely D=o(X) is trivial here: for each p,b, Brun--Titchmarsh applied to
q congruent to +/-inverse(b) modulo p gives the unsigned bound

```
C_+ + C_- << BQ/(log(Q/P) log P) << X/log^2 X.
```

This uses Q/P=X^.3. It does not sum to o(X) over the O(log^2 X)
rectangles needed for fixed exponent-width sectors. The interval
Brun--Titchmarsh statement was source-checked in
`/corpus/src/1410.7561/WBTI-AA-revised.tex:220-224`.

The equivalent prime-restricted Lambda-weighted target is o(X): within
each prime band the logarithms vary by O(1), so

```
D_Lambda = (log P)(log Q) D + O(X/log X).
```

For this direct count, adding proper prime powers is inexpensive:
O((A sqrt(P)+B sqrt(Q))log^2 X)=O(X^.7 log^2 X). After one prime power
and its cofactor are fixed, the neighboring integer has at most one
prime-power divisor in the other open dyadic band, which lies above
its square root. Distinct underlying primes would have product too
large, while two powers of the same prime cannot lie in that band.
This is a statement about the direct count, not an improvement of the
energy errors in section 2.

A further classical dispersion theorem was source-checked, beyond the
tiny-factor 17/33 corollary already tested above. Fouvry's earlier
Theoreme 1 is quoted in
`/corpus/src/1811.08672/FouvryRadzi7.tex:928-930` as giving arbitrary
logarithmic saving for the fixed-small-residue L1 discrepancy of a
length-T convolution with short Siegel--Walfisz factor N, provided

```
R <= min(T^(1/2) N^(1/2), T^(5/8) N^(-3/4)) T^(-epsilon),
N > T^epsilon,   1 <= |residue| <= T^(epsilon/1000).
```

Applied to bq with T=X,N=B=X^.1 and residues +/-1, both bounds for R
are X^.55. The requested prime modulus P=X^.6 is still outside the
range. Thus this stronger classical range check does not close even
the weaker direct-count target.

The free-cofactor version remains an odd-residue pairing, not an
unrestricted Titchmarsh divisor sum. Complementary divisor switching
preserves the requirement that (bq+/-1)/a is prime. No cancellation
estimate for that weight has been established in this work.
