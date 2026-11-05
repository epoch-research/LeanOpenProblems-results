# An unbounded shifted-factor and sieve route (not a proof of Erdős–Straus)

This is an ordinary mathematical argument; it does **not** alter `Spec.lean` or
assert that every hard prime has a witness. As in the existing notes, a witness
has positive, **strictly increasing** denominators. All analytic assertions
below use standard, unconditional prime number/Mertens theorems in *fixed*
arithmetic progressions. In particular, no density assertion is interpreted
as pointwise divisor existence.

## A split quadratic factorization of every prime type-II solution

**Theorem.** Suppose positive integers `v,w,r,s` satisfy `r<s` and
`v | r+s`, and put

    a=(r+s)/v,    p=4wrs-a.

Then `p>2wrs>=4`, and the following is a strictly ordered identity:

    4/p = 1/(wrs) + 1/(p v w r) + 1/(p v w s).                (1)

For a prime `p`, conversely **every** ordered type-II solution, meaning one
whose last two denominators are divisible by `p`, is of this form with
`gcd(r,s)=1`. This is NOT a description of type-I solutions.

**Proof.** Since `r<s`, one has `2rs>r+s`, so
`a <= r+s < 2wrs` and `p=4wrs-a>2wrs`. In particular `p v>s`, whence
`wrs < p v w r < p v w s`. The sum in (1) has numerator
`p v+r+s=v(p+a)=4v w r s` over denominator `p v w r s`.

Conversely let `x<pm<pu` be a solution for prime `p`, with `m<u`. Put
`a=4x-p`; clearing denominators gives `a m u=x(m+u)`. Since
`4/p=1/x+1/(pm)+1/(pu)<3/x`, we have `x<3p/4<p`.
Write `g=gcd(m,u)`, `m=gr`, `u=gs`, `gcd(r,s)=1`, `r<s`. Then
`a g r s=x(r+s)`. Because `gcd(rs,r+s)=1`, we can write `x=wrs`.
Also `g p=w(4g r s-r-s)`, so `w|g p`. As `w<=x<p` and `p` is prime,
`gcd(w,p)=1`, and therefore `g=vw`. Canceling `w` gives
`a v=r+s` and hence `p=4wrs-(r+s)/v`, with the three denominators
exactly as displayed. This proves both directions.

This is equivalently an **exact divisor criterion for type II**. For fixed
`v,w>0`, let `N=4v^2 w p+1` and `M=4v w`. Equation (1) implies

    N=(M r-1)(M s-1).                                        (2)

Conversely, a proper divisor `q` of `N` with `q<N/q` and
`q ≡ -1 (mod M)` provides `r=(q+1)/M` and `s=(N/q+1)/M` and hence (1).
Indeed `N ≡ 1 (mod M)` implies its cofactor is also `-1 (mod M)`;
expanding (2) shows `v p=4v w r s-r-s`, so `v|r+s` automatically.
The strict condition `q<N/q` rules out equal last denominators. This is a
factorization/positive-integral-points problem, not a conclusion from
rational points on the hyperbola or local congruence solvability.

## Two useful axes of the parameterization

**Shift `p+k`.** Let `p>=5` be a prime with `p ≡ 1 (mod 4)`, and let
`1<=k<p`. If **some divisor** `q | p+k` satisfies `q ≡ -1 (mod 4k)`,
set `w=(q+1)/(4k)` and `t=(p+k)/q`. Then

    p=4k w t-k-t,
    4/p=1/(k w t)+1/(p k w)+1/(p w t).                       (3)

The first denominator is smaller than both others: `k<p`, and
`t=(p+k)/q<p` since `q>=3` and `k<p`. The two remaining denominators
are distinct: `t=k` would give `p=k(q-1)`; primality and `p>k` force
`k=1`, in which case the odd prime `p=q-1` would be even. Thus sort
`p k w` and `p w t` according as `k<t` or `t<k`. Formula (3) follows
from `p+k=(4kw-1)t`. **Primality of `q` is not needed** for (3).
In the canonical parameters of (1), this is the `v=1` axis. Unlike a
fixed `(m,d)` modular class, `w`, `q` and `t` are unbounded.

**Shift `v p+1`.** Let `p>=5` be prime with `p ≡ 1 (mod 4)`. If
`q | vp+1` and `q ≡ -1 (mod 4v)`, write
`w=(q+1)/(4v)`, `t=(vp+1)/q`. Then

    4/p=1/(w t)+1/(p v w)+1/(p v w t),                      (4)

strictly ordered. Here `t<vp` because `q>=3`. Also `t=1` would imply
`v(4w-p)=2`: for `v=1`, `p=4w-2` is even, and for `v=2`,
`p=4w-1 ≡ 3 (mod 4)`; both contradict the assumptions. Thus `t>1`.
The identity follows from `vp+1=(4vw-1)t`. This is the `r=1` axis
of (1). It can work when none of the original shifted divisors of
`p+4` work.

One quadratic-splitting illustration is available without pretending it
settles every prime. Write `p=24h+1`,

    A=(p+2)/3=8h+1,   B=(2p+1)/3=16h+1=2A-1.

The `k=2` version of (3) works **if and only if** `A` has a prime
factor `5` or `7 (mod 8)`: if `ell ≡ 7 (mod 8)` use `q=ell`, and if
`ell ≡ 5 (mod 8)` use `q=3ell ≡ 7 (mod 8)`; conversely, products of
primes `1` or `3 (mod 8)`, even after multiplying by `3`, cannot be
`7 (mod 8)`. The same statement for `B` and the `v=2` version of (4)
holds verbatim. Prime factors `1,3 (mod 8)` are precisely the split
odd primes in `Q(sqrt(-2))`. Thus simultaneous failure of these two
small families forces **both** `A,B` to have only split prime factors;
merely being norms would be weaker (an inert prime with even exponent
can occur in a norm). Neither splitting restriction is universal.

## Quantitative analytic result: arbitrary logarithmic-power rarity

Define, for a **fixed** integer `K>=1`,

    kappa_K = sum_{k=1}^K 1/phi(4k).

Let `E_K(X)` count primes `p<=X`, `p ≡ 1 (mod 24)`, for which there is
**no prime** `q | p+k` satisfying `q ≡ -1 (mod 4k)` for **any**
`1<=k<=K`. In particular, every putative insoluble hard prime is
counted by `E_K(X)`: each omitted divisor would yield the ordered
identity (3), including when the divisor is composite.

**Theorem (unconditional).** For every fixed `K`,

    E_K(X) <<_K X / (log X)^(1+kappa_K).                    (5)

Consequently, for every fixed real `C>0`, the number of hypothetical
counterexample **primes** `p<=X` is `O_C(X/(log X)^(1+C))`. Relative to
all primes `p ≡ 1 (mod 24)`, this is `O_C((log X)^(-C))`. This is
much stronger quantitatively than a density-one assertion, but it
**does not establish that any individual exceptional prime is soluble**.

Here is a direct Selberg-weight proof of (5), including the sieve
truncation, rather than an appeal to an unproved distribution assumption.
Fix `K`, take `z=X^eta` (with small fixed `eta>0` chosen below), and
for every prime `q` with `4(K+1)<q<=z` forbid the distinct residues

    R_q = {0} union {-k (mod q) : 1<=k<=K, q ≡ -1 (mod 4k)}.

Let `omega(q)=|R_q|=1+#{k<=K:q ≡ -1 (mod 4k)}` and
`rho(q)=omega(q)/q`; then `0<rho(q)<1/4`. The class `0` removes
integers divisible by a sieving prime, while each `-k` removes a prime
`p` having the witness `q|p+k`. In particular,
primes `p>z` escape the `0` classes. Any such prime counted by
`E_K(X)` avoids every `R_q`.
Write `S(X,z)` for the number of **all** integers `n<=X` avoiding
these residue sets, so `E_K(X)<=z+S(X,z)`.

Restrict all later `d,e,r` sums to squarefree products of the sieving
primes (the empty product is `1`), and extend `omega,rho`
multiplicatively on these products. Here `Omega(d)` counts their prime
factors. By the Chinese remainder theorem, the
number of `n<=X` hitting a forbidden residue at each prime `q|d` is

    X rho(d) + O(omega(d)).

Set `g(q)=rho(q)/(1-rho(q))`, extend it multiplicatively, and put
`G(z)=sum_{d<=z} g(d)` over these squarefree `d`. The elementary
Selberg weights

    lambda_d = mu(d) G_d(z/d) /
               (G(z) product_{q|d}(1-rho(q))),
    G_d(T)=sum_{e<=T, gcd(e,d)=1} g(e),

have `lambda_1=1` and `|lambda_d|<=2^{Omega(d)}`. To check their main
quadratic form, define `y_r=sum_{d<=z, r|d} lambda_d rho(d)`.
Mobius inversion gives `y_r=mu(r)g(r)/G(z)`. With
`h(r)=product_{q|r}(1-rho(q))/rho(q)=1/g(r)` and the identity

    rho(lcm(d,e)) = rho(d)rho(e) sum_{r|gcd(d,e)} h(r),

one obtains

    sum_{d,e<=z} lambda_d lambda_e rho(lcm(d,e))
        = sum_{r<=z} h(r)y_r^2 = 1/G(z).

The square of the weight sum is `1` for every sifted integer. The CRT
error, using `omega(lcm(d,e))<=omega(d)omega(e)` and
`omega(d)<=(K+1)^Omega(d)`, is at most

    (sum_{d<=z} (2(K+1))^Omega(d))^2
      <= z^(2+2 log_2(2(K+1))).

Hence `S(X,z)<=X/G(z)+O_K(z^(2+2 log_2(2(K+1))))`.

For completeness, `G(z)` has the required size. Put
`delta=1/(8(K+1))`, `Z=z^delta` and
`P(Z)=product_{4(K+1)<q<=Z}(1+g(q))` over primes. If squarefree
products of these primes receive probability proportional to `g(d)`,
their mean `log d` is

    sum_{q<=Z} (g(q)/(1+g(q))) log q
      = sum_{q<=Z} rho(q) log q
      <= (K+1) sum_{q<=Z} (log q)/q
      <= 2(K+1) log Z = (log z)/4

for large `Z`. Markov's inequality leaves at least `3/4` of `P(Z)` on
`d<=z`, so `G(z)>=(3/4)P(Z)`. Mertens' theorem for primes in each
fixed progression `q ≡ -1 (mod 4k)` yields

    sum_{q<=Z} rho(q)
       = (1+kappa_K) log log Z + O_K(1).

Since `log P(Z) >= sum_{q<=Z}rho(q)`, we obtain
`G(z) >>_K (log z)^(1+kappa_K)`.
Choose `eta=1/(4+4 log_2(2(K+1)))`, so the CRT error is at most
`X^(1/2)`, and `log z=eta log X`; the `z` exceptional small primes
and the CRT error are absorbed into (5).

Finally `kappa_K >= (1/4)sum_{k<=K}1/k` tends to infinity. For any
specified `C`, choose **one fixed** `K` with `kappa_K>=C`, apply (5),
and use the prime number theorem in the progression `1 (mod 24)`
for the relative version. Neither `K` nor the implied constants are
uniformly controlled as a function of an individual `p`. It would be
incorrect to send `K` to infinity for a fixed prime in (5).

## An explicit prime outside the previous easy cases

For `p=66529` (prime by trial division through `floor(sqrt(p))`),
`p mod 840=169`, `p mod 11=1`, and `p+4=66533` is prime `1 (mod 4)`.
Also `(p+3)/4=16633` is prime `1 (mod 3)`, `(p+1)/2=5*6653`
and `4p+1=266117` have only prime factors `1 (mod 4)`.
The two `Q(sqrt(-2))` tests fail too:

    (p+2)/3 = 67*331        (both 3 mod 8),
    (2p+1)/3 = 17*2609     (both 1 mod 8).

Nevertheless `p+5=66534=39*1706`, `39=4*5*2-1` (not prime),
so (3) with `k=5,w=2,t=1706` gives the exactly checked identity

    4/66529 = 1/17060 + 1/665290 + 1/226996948.

A residual example detected by a **prime** sieving divisor is `p=170641`:
`p mod 840=121`, `p mod 11=9`, `p+4=5*34129` (both factors
`1 (mod 4)`), and `p+5=239*714` with prime `239=4*5*12-1`.
Here `(k,w,t)=(5,12,714)` gives, by (3),

    4/170641 = 1/42840 + 1/10238460 + 1/1462052088.

A complementary example of (4) is `p=5569`: `2p+1=47*237`,
`47=4*2*6-1`, and

    4/5569 = 1/1422 + 1/66828 + 1/15838236.

**Precise conditional route.** If every prime `p ≡ 1 (mod 24)` had
**either** a divisor of `p+k` as in (3) for some `1<=k<p`, **or** a
divisor of `vp+1` as in (4) for some `v>=1`, then (3)/(4) and the
already proved reduction from hard primes would settle all `n>2`.
This two-axis hypothesis is *stronger* than Erdős–Straus: (1) also
allows `v,r>1`, and type-I solutions need not have this form.
Even the first, more restrictive axis alone handles all but the
exceptional primes bounded in (5), yet its **pointwise** universality
has not been proved. Such finite identities prove no universal
pointwise divisor assertion. A complete proof would still require
showing that **each** remaining hard prime has a suitable factor in
(2), or in an axis (3)/(4), or an unrelated type-I witness. The sieve
theorem alone cannot do so; a nonempty, even infinite, set can satisfy
all the displayed upper bounds.
