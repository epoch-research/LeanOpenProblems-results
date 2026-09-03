# Missing-band inverse attempt: common anchor mask, factor phases, and characters

## Outcome

No contradiction or proof of Erdős #5 was obtained. This pass tests whether the **exact** missing-gap condition can be converted into character rigidity, rather than assuming a generic prime-pair asymptotic. The useful reduction is that, under the missing-band hypothesis, the interior-prime mask is the **same prime-anchor function for every shift in the band**. The subsequent inverse step fails for an explicit arithmetic reason: perfect factor-phase alignment is automatic on actual rough semiprimes, even though that entire semiprime population is equidistributed in all fixed-power-of-log arithmetic progressions.

Only this scratch report was added. No Lean file, axiom, or admitted helper was added or changed. `Spec.lean` retains its two `sorry`s and SHA-256

    47104279c0cb871e0a255d81fffde6a4a6ea7e71c3eec5c5b57e0bc7c0654123

## 1. Exact linearization of the consecutive-gap mask

Assume the eventual absence of consecutive prime gaps in `(a log(index), b log(index))`, where `0<a<b`. Choose fixed

    a < A < B < b,   L = log X,   H_X = {h in Z : A L < h < B L}.

PNT gives `log(index(p))/L -> 1` uniformly for `X<p<=2X`. Consequently, for sufficiently large X, no consecutive prime gap starting in this range belongs to `(A L,B L)`. The interior margins, rather than an equality between the two logarithms, justify this normalization.

Write `g(p)` for the gap from p to its next prime. Restrict anchors to `X<p<=2X-BL` and put

    E_X = {such primes p : g(p)>A L}.

Under the hypothesis this is also `{p : g(p)>=B L}`. For EVERY `h in H_X` and EVERY permitted prime anchor p, exactly

    product_(1<=t<h) (1-1_P(p+t)) = 1_(p in E_X).             (1)

Indeed the product is one iff `g(p)>=h`. Since `g(p)` avoids `(AL,BL)`, this is equivalent to `g(p)>=BL`. This argument includes the possible endpoint equality `g(p)=h`: that equality would be a forbidden gap, not an uncounted interior prime.

Thus the original h-dependent interior mask becomes a common one-coordinate prime mask. Define

    U_X = union_(p in E_X) {p+h : h in H_X}.

These sets are disjoint: if `p<q` are both in `E_X`, then `q>=p+g(p)>=p+BL`. They lie wholly in `(X,2X]`, and every member is composite. In particular,

    |U_X| = |E_X| |H_X|.

This is a genuine consequence for the actual primes, with global consecutivity retained. No CRT mask is introduced. It does NOT say that all prime-pair distances in the band are absent: a pair with an intervening prime has zero weight in (1).

## 2. All factor phases collapse, but the collapse is just degree two

Fix `1/3<theta<1/2`, and let `y=X^theta` and `R_y(n)=1_(P^-(n)>y)`. For sufficiently large X, `y^3>2X`. Hence every rough member of `(X,2X]` is either a prime or a product of exactly two primes, counting multiplicity.

For `|z|<=1`, the function

    f_(X,z)(n) = R_y(n) z^Omega(n)

is completely multiplicative (with value 1 at n=1). Define the masked generating function

    F_X(z) = sum_(p in E_X) sum_(h in H_X) f_(X,z)(p+h),
    M_X = F_X(1).

Every contributing integer is composite and has exactly two prime factors. Disjointness from Section 1 therefore gives, exactly,

    F_X(z) = z^2 M_X,       M_X <= |S_theta(X)|,              (2)

where

    S_theta(X) = {X<m<=2X : P^-(m)>X^theta, Omega(m)=2}.

In particular `F_X(-1)=M_X`. The whole family of phases is aligned, not just Liouville. However, it supplies **no independent constraints beyond excluding the degree-one coefficient**. Before assuming the hole, the analogous nearest-prime-predecessor sum is exactly `z K_X+z^2 T_X`, with K_X the consecutive-prime band count. Setting K_X to zero explains all of (2).

The containing population has an explicit size. Unique factorization, including squares, gives

    |S_theta(X)|
      = sum_(y<r<=sqrt(X), r prime) [pi(2X/r)-pi(X/r)]
        + sum_(sqrt(X)<r<=sqrt(2X), r prime)
            [pi(2X/r)-pi(r)+1].                             (3)

The second sum is `O(X/L^2)`. PNT uniformly for the first sum's cofactor intervals, followed by partial summation over r, yields

    |S_theta(X)| = (c_theta+o(1)) X/L,
    c_theta = integral_theta^(1/2) dt/[t(1-t)]
            = log((1-theta)/theta).                         (4)

Thus the hole has the rigorously justified consequence

    0 <= M_X <= (c_theta+o(1)) X/log X                       (5)

for every sufficiently large X and every FIXED `1/3<theta<1/2`. No lower bound for `|E_X|` or M_X was obtained; M_X may be zero, in which case the phase identity is vacuous. No division by M_X is used. No uniformity as theta approaches 1/2 with X is claimed. The previously recorded near-square second-order calculation is not being rederived here.

The unmasked generating function, using PNT again, is

    sum_(X<n<=2X) f_(X,z)(n)
       = (z+c_theta z^2+o(1)) X/L,                          (6)

uniformly for `|z|<=1`. Since `0<c_theta<log 2<1`, this actually gives, uniformly on the unit circle,

    |sum f_(X,z)| / sum R_y
       >= (1-c_theta)/(1+c_theta) + o(1) > 0.               (7)

In particular the global rough Liouville mean is NEGATIVE, of size `(1-c_theta)X/L`, not relatively cancelling. Merely inserting a power-rough indicator into an unconditioned cancellation theorem would be wrong even at the one-point level.

## 3. An actual arithmetic obstruction to the character inference

The following fact requires no missing-gap hypothesis. For every fixed `D,C>0`, uniformly over all nonprincipal Dirichlet characters chi modulo `q<=L^D`,

    sum_(m in S_theta(X)) chi(m) <<_(theta,D,C) X/L^C.       (8)

Here is the complete reduction to the ordinary Siegel-Walfisz theorem; no two-point prime theorem is involved. Write

    T_chi(t) = sum_(r<=t, r prime) chi(r).

Siegel-Walfisz, after summing reduced residue classes against chi and choosing an arbitrarily larger logarithmic saving, gives

    T_chi(t) <<_(theta,D,J) t/L^J

for any fixed J, uniformly for `X^theta<=t<=2X^(1-theta)` and `q<=L^D`. Replacing the prime-counting functions in (3) by T_chi and multiplying each outer summand by chi(r) gives the exact character sum, with `+chi(r)` in place of `+1` in the second bracket. Since `P^-(m)>y>q`, no character-zero issue occurs. The interval terms have total absolute bound

    << X/L^J sum_(y<r<=sqrt(2X), r prime) 1/r
    <<_theta X/L^J.

The square correction is `O(sqrt(X))`, which is absorbable in `X/L^C` for any fixed C. This proves (8). Character orthogonality then also gives equidistribution of S_theta among reduced residue classes modulo every `q<=L^D`, with errors smaller than the relative main term after increasing C.

But simultaneously, on this SAME actual set,

    lambda(m)=1 and z^Omega(m)=z^2 for every m in S_theta(X).

Thus a sparse arithmetic set of size `asymp_theta X/log X` has perfect alignment of all these multiplicative phases while displaying no nonprincipal character bias throughout the Siegel-Walfisz range. This is not a renewal model or an assignment of fake prime indicators. It uses the real prime factors of real integers.

**Scope:** (8) is for the full semiprime set, NOT for `S_theta(X) intersect U_X`. It neither constructs a prime-gap counterexample nor rules out a future rigidity theorem exploiting further properties of the specific mask U_X. It rules out the proposed first leap from phase extremality alone to a global small-conductor character obstruction.

## 4. Why the checked analytic inputs do not pass to the mask

### Sparse pretentiousness degenerates on this support

For `f_X=R_y lambda`, the modified distance relevant to sparse multiplicative functions satisfies

    Mhat(f_X;X)
      = min_(|t|<=X) sum_(r<=X, r prime)
           (|f_X(r)|-Re(f_X(r)r^(-it)))/r
      <= 2 sum_(y<r<=X) 1/r
      = 2 log(1/theta)+o(1).                               (9)

The upper bound simply takes t=0. It does not diverge. The usual unmodified distance has a diverging contribution from `r<=y`, but there `f_X(r)=0`: this records sparsity, not sign oscillation. For any unit phase z the same calculation gives the bounded upper bound `(1-Re z) log(1/theta)+o(1)`.

Moreover R_y fails the actual non-vanishing hypothesis of the sparse short-interval theorem. For any fixed range exponent tau>0, choose `0<eta<min(theta,tau)` and take `w=X^(eta/2)`, `v=X^eta`. Then

    sum_(w<r<=v) |f_X(r)|/r = 0,
    sum_(w<r<=v) 1/r = log 2+o(1).

This contradicts a lower bound `alpha sum 1/r - O(1/log w)` for every fixed alpha>0 and a uniform implied constant. Letting constants depend on X would invalidate the theorem's conclusion. This is a checked hypothesis failure, not a blanket objection to sparse functions.

Source: Matomaki-Radziwill, `/corpus/src/2007.04290/Vanishing27.tex`, modified distance at lines 239-248; non-vanishing definition at 285-293; main theorem at 310-325; removal of the main term using large modified distance at 338-346.

### Averaged cancellation on shifted primes discards the entire relevant rough set

Lichtman's theorem allows very general bounded factors alongside the prime weight, so the common-anchor simplification in (1) is useful and should not be dismissed as an arbitrary-mask issue by itself. Nevertheless two concrete obstacles remain:

* Its shift range requires `log H/log log X -> infinity`. Here `H` is of order `log X`, so the ratio tends to 1.
* Its arbitrarily strong logarithmic Fourier saving is on a typical-factorization set requiring a prime factor in

      [exp((log X)^(2/3+delta/2)), exp((log X)^(1-delta/2))].

  For fixed small delta>0, this whole interval lies below `X^theta` eventually. Using the source at height 2X rather than X does not change that comparison. Therefore EVERY power-rough integer used in (2) lies outside that typical set. The relevant mass is in the part treated by an absolute sieve bound, not in the part where cancellation is proved. Multiplying by the rough indicator does not give the saving relative to M_X.

Sources: `/corpus/src/2009.08969/2009.08969.tex`, main theorem at 34-43; typical-factorization set and Fourier theorem at 247-264; absolute treatment of its complement at 266-287; arbitrary bounded extra factors in the almost-all-shifts theorem at 955-984. None of these statements evaluates the rough, prime-anchor-selected correlation at logarithmic shifts.

For (8), the exact unconditional input is the classical Siegel-Walfisz bound with arbitrary fixed logarithmic saving. A corpus statement is `/corpus/src/2004.04766/BV-2021.tex`, lines 682-686, for prime powers. Removing higher prime powers costs `O(sqrt(t) log t)`, harmless here. The character version above also pays the number of residue classes; the arbitrarily increased saving explicitly absorbs it.

## Precise stopping point

The exact zero successfully removes the h-dependence of the interior-prime mask. It does **not** make the surviving rough function relatively nonpretentious or make the anchor mask independent of factorization.

After factoring a selected composite `m=rs`, the remaining weight is `1_U_X(rs)`. Explicitly it still tests a prime `rs-h` and the absence of primes at every intervening integer. Inserting this weight into the cofactor sums used to prove (8) destroys their interval-only form. PNT/Siegel-Walfisz no longer evaluate the inner sum. Conversely, stripping the weight abandons the consequence of the hole. This masked cofactor sum is the first unclosed arithmetic implication; no relative estimate for it was proved or assumed.

The substantive results are (1)-(9), with the stated scope. They expose a real limitation of this inverse attempt, not an unconditional contradiction and not a sufficient-condition reformulation offered as a proof.

## Checks

* Mask linearization, disjointness, and exclusion of endpoint primes were exhaustively checked on all 15,522 binary configurations of length 16 avoiding consecutive-one gaps 3 and 4. This tests finite algebra, not prime-gap existence.
* The rough prime/semiprime classification, exact count (3), and generating polynomial were checked on four finite integer intervals with `y^3>2X` and `y^2<X`, including prime squares.
* The exact character-factorization identity underlying (8) was independently checked for five quadratic characters, including the diagonal square corrections. These are finite identity tests, not numerical verification of Siegel-Walfisz.
* The real antiderivative `log t-log(1-t)` was symbolically differentiated; endpoint evaluation gives the constant in (4).
* The source hypotheses and the Spec hash/two-sorry count were checked. No numerical observation is used to claim an asymptotic or a missing prime-gap band.
