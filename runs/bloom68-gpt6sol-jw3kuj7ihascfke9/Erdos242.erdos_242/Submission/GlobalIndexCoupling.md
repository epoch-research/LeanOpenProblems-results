# Divisor-retaining couplings between hard-prime indices: a conditional duality and an isolated failed fiber

**Status.** These are elementary, exact conditional constructions and finite counterexamples to one proposed orbit rule, **not** a proof or refutation of the hard-prime cover or Erdős–Straus. No Lean file is modified. `python3 Submission/GlobalIndexCouplingAudit.py` independently checks every finite assertion by trial factorization, enumeration of *all* divisors of the relevant whole squares, and exact rational arithmetic. The existing `CoveringGap.all_good_iff_explicit_hard_cover` gives the universal equivalence; none of the arguments below fills its outstanding existence step.

## An exact move between indices, including the Type-II size condition

Let `p=24k+1` be prime, `k>=1`, `0<=j<6k`, `x_j=6k+1+j`, `a_j=4j+3`. Directly,

    p<4x_j,             2x_j<p,
    3<=a_j<=p-2,        4x_j=p+a_j,        gcd(a_j,x_j)=1.   (1)

For the gcd, any common factor divides `4x_j-a_j=p`, while `a_j<p` and `x_j<p`. For `t>0`, let `rho(t)=product over prime powers ell^e||t of ell^ceil(e/2)`. Unique factorization gives

    t|x_j^2  iff  rho(t)|x_j;
    if t|x_j^2, then t|x_{j'}^2 iff rho(t)|(j'-j).          (2)

The last divisibility is for the absolute difference if `j'<j`. The following are **exact factor tests for reusing a square divisor `t` at a DIFFERENT eligible index** `j'`:

* Type I: `a_{j'}|4t+1`;
* Type II: `a_{j'}|p+4t`, equivalently `a_{j'}|x_{j'}+t`, since `4(x_{j'}+t)=p+a_{j'}+4t` and `a_{j'}` is odd.

In either case require `rho(t)|(j'-j)`. Equivalently, find a divisor `a'` of the displayed number with `3<=a'<=p-2`, `a'≡a_j (mod 4rho(t))`, and `a'≠a_j`; then `j'=(a'-3)/4` is automatically eligible and different from `j`. This is a **conditional** transition, not a claim such a factor always exists.

The apparent missing Type-II restriction `t<x_{j'}` is not a loophole. Set `x=x_{j'}`, `a=a_{j'}`, and `e=x^2/t`. Since `gcd(a,x)=1` and `t|x^2`, also `gcd(a,t)=1`. The identity

    t(x+e)=x(x+t)

shows that `a|x+t` implies `a|x+e`. Moreover `t=x` would give `a|2x`, and thus `a|2`, impossible since `a>=3`. Therefore one of `t,e` is **strictly less than** `x`; choosing that divisor supplies the *full* Type-II certificate `0<d<x`, `d|x^2`, `a|x+d`. Thus the move retains the required ordered first-denominator bounds and, where needed, replaces a too-large divisor by its complement.

For completeness, the resulting ordered *integer* decompositions require no further existence assumption. Type I with `c|x^2`, `r=x^2/c` gives `y=(px+r)/a`, `z=(px+p^2c)/a`: modulo `a`, `p≡4x` and `4c+1≡0`, so both displayed numerators are divisible by `a`. Type II with `d|x^2`, `e=x^2/d` gives `y=p(x+d)/a`, `z=p(x+e)/a`, also integers by the preceding complementary argument. In both cases `x<y<z`: `p>2x` ensures `x<y`; for Type I, `pc>x` ensures `r<p^2c`, and for Type II `d<x<e` ensures `d<e`. Elementary multiplication using `cr=x^2` or `de=x^2` gives `1/y+1/z=a/(px)`, hence `1/x+1/y+1/z=(p+a)/(px)=4/p`. These formulas justify strict order as well as the congruence-to-solution step.


## A universal retained-divisor orbit cannot start at some failed fibers

At `p=193=24*8+1`, `x_0=49=7^2` and `a_0=3`. Both types fail there: all divisors `t|49^2` are `1 (mod 3)`, whereas both targets are `2 (mod 3)`. In fact **no** choice of an old square divisor can make either transition at *any* other index. Here is the exhaustive table (`t=1,7,49,343,2401`):

| `t` | factorization of `4t+1` | factorization of `193+4t` |
|---:|---|---|
| 1 | `5` | `197` |
| 7 | `29` | `13*17` |
| 49 | `197` | `389` |
| 343 | `1373` | `5*313` |
| 2401 | `5*17*113` | `97*101` |

All the displayed factors are primes `1 (mod 4)`, as certified by trial division. Hence **neither number has ANY divisor `3 (mod 4)`**, so there cannot even be a prospective new modulus `a_{j'}`; condition (2) is irrelevant. Nevertheless `j=1`, `x=50`, `a=7`, `c=5|50^2` and `d=20|50^2`, `d<50`, work: `7|4*5+1=21` and `7|50+20=70`. The successful square divisors have a new prime factor `5` absent from `49^2`. This disproves the rule “every failed index has an outgoing success move reusing one of its square divisors,” **not** the actual covering claim.

A general isolation lemma explains the other mandatory test primes. Suppose `q=x_0=6k+1` is prime and *every* prime factor of `p+4` is `1 (mod 4)`. Since `q≡1 (mod 3)`, `j=0` fails both types. Its whole-square divisors are only `1,q,q^2`. For either nonunit divisor `rho(t)=q`, but `0<j'<6k=q-1` implies `0<j'<=q-2`, so `q` cannot divide `j'-0`: neither nonunit divisor can be retained anywhere else in the eligible interval. For `t=1`, Type I would need `a_{j'}|5`, impossible for `a_{j'}≡3 (mod 4)` and `a_{j'}>=3`; Type II would need `a_{j'}|p+4`, also impossible because all its divisors are `1 (mod 4)`. Thus **no outgoing retained-divisor edge at all** leaves this failed `j=0`. It applies (primalities checked by trial division) to

| `p` | prime `q=x_0` | factorization of `p+4` |
|---:|---:|---|
| 2521 | 631 | `5^2*101` |
| 66529 | 16633 | `66533` |
| 1915201 | 478801 | `5*383041` |

All four specified stress primes therefore have an isolated **failed initial vertex** for this precise orbit rule. This does not prevent a method that introduces genuinely new divisors at a later index.

There **are** valid failed-to-success moves elsewhere: for `p=2521`, `j=1` has `x=632=8*79`, `a=7`; all divisors of `632^2` lie in `{1,2,4} (mod 7)`, whereas both targets equal `5`, so the whole fiber fails. Retain `t=8`, for which `rho(t)=4`, and move to `j'=5`: `4|5-1`, `x_5=636`, `a_5=23`, and `2521+4*8=2553=23*111`. Now `8|636^2`, `8<636`, and `23|636+8=644`. Note `8` divides the **square** of 636 but not 636 itself.

## A genuine, but witness-dependent, two-index Type-I involution

There is also a symmetric coupling among **already successful** indices. Assume `a,r,h≡3 (mod 4)`, all positive, and

    p=ahr-a-r > max(a,r)

is a hard prime. Put `u=(ah-1)/4`, `v=(rh-1)/4`. Then `u,v>=2`, `hp+1=(ah-1)(rh-1)=16uv`, and two *different* indices with moduli `a` and `r` yield the explicitly ordered identities

    4/p = 1/(ru) + 1/(4ruv) + 1/(4puv)
        = 1/(av) + 1/(4auv) + 1/(4puv).                       (3)

Indeed `4ru=p+a`, `4av=p+r`, so both first denominators satisfy (1). The cofactors `u|ru` and `v|av` meet `a|4u+1=ah` and `r|4v+1=rh`. For each row, the middle denominator exceeds the first because `u,v>=2`, and the common last denominator exceeds the middle because `p>r,a`. Adding the first two fractions gives `h/(4uv)` (`4v+1=rh` or `4u+1=ah`), and adding the last gives `(hp+1)/(4puv)=4/p`. If `a=r` then `a|p`, impossible for a prime `p>a`, so the indices are distinct. Swapping `a` and `r` twice returns to the starting witness.

For instance `p=8353` is prime and `p=7*63*19-7-19`; `u=110`, `v=299`. Formula (3) gives `j=1,4` and

    4/8353 = 1/2090 + 1/2499640 + 1/1098920680
           = 1/2093 + 1/920920  + 1/1098920680.

This works in an infinite *selected* hard-prime progression: take `h=24n+15`, `p=3192n+1969`; `gcd(3192,1969)=1`, so Dirichlet supplies infinitely many prime values. **It does not derive either witness from a failed candidate**: the factorization `p=ahr-a-r` already supplies Type I, and no analogous factorization is known to exist for every hard prime.

## Exhaustive four-prime stress audit and remaining gap

Enumerating every square divisor with prime exponents `0,...,2v_q(x_j)` produces the following **first** successful indices (strict order also checked using exact rational arithmetic):

| `p`, `k` | failed `j` before first hit | first `j`, `x`, `a` | full witnesses at first hit |
|---|---|---|---|
| `193`, `8` | `0` | `1, 50, 7` | I `c=5`, II `d=20` |
| `2521`, `105` | `0,...,4` | `5, 636, 23` | I `c=477`, II `d=8` |
| `66529`, `2772` | `0,...,3` | `4, 16637, 19` | I `c=2179447=127*131^2>x`; **no II** |
| `1915201`, `79800` | `0,...,10` | `11, 478812, 47` | I `c=239406`, II `d=24` |

For `66529`, `x_4=127*131`; its *only* Type-I divisor at this fiber is `127*131^2`, with `rho(c)=16637>4`, and no Type-II divisor exists. Thus none of the first four failed fibers can reuse this successful `c`. For `1915201`, `x_11=2^2*3*39901`; its only Type-I/II witnesses at this fiber are the two displayed, with `rho(c)=239406` and `rho(d)=12`, both greater than every distance `11-j` for `j<11`. The independent audit also verifies that at **each** `j=0,...,10`, *both targets are absent from all residues of every divisor of `x_j^2`*, before imposing `d<x_j`; `Submission/LeastJacobiTransfer.md` lists their complete factorizations and residue sets. The `j=11` witnesses give `47|4*239406+1=957625` and `47|478812+24=478836`, with `24|478812^2`, `24<478812`; this prime is not a counterexample.

**Unresolved:** Neither (2), the isolated-prefix obstructions, (3), nor any finite scan constructs a Type-I or Type-II divisor at *some* `0<=j<6k` for **every** hard prime, or proves that a prime fails both at **all** such indices. A successful orbit must create new suitable factors when its old divisors are isolated; no theorem here forces the required exact factor residue. The original `Spec.lean` remains unchanged with its `sorry` declarations.