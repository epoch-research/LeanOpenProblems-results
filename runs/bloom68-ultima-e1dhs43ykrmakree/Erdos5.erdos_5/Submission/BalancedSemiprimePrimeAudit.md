# Balanced semiprimes next to primes: source audit and an upper-bound consequence

## Status

No proof or disproof of Erdős #5 was obtained. This pass checked genuine prime + exact balanced-semiprime correlations, rather than divisor moments or a prime/P2 disjunction. The new usable input is an upper bound only. `Spec.lean` was not changed.

## 1. Uniform exact-balanced upper bound

Put `L=log X`. Let `N_h(X)` count prime pairs of factors `sqrt X<q<=r`, `qr<=2X`, such that `p=qr-h` is prime and both `p,qr` belong to `(X,2X]`. The product is composite, and squares are included once.

For fixed `B>0`, uniformly for nonzero even `|h|<=B L`,

```
N_h(X) << (|h|/phi(|h|)) X/L^3.
```

To prove this, fix the smaller factor `q`, necessarily `sqrt X<q<=sqrt(2X)`. The elementary two-linear-form upper sieve gives

```
#{r<=2X/q : r and q*r-h prime}
  << (|hq|/phi(|hq|)) X/[q log^2(4X/q)].
```

Since `q>|h|` eventually, the arithmetic factor is at most a fixed constant times `|h|/phi(|h|)`. Also `log(4X/q)~L/2`, and PNT gives

```
sum_(sqrt X<q<=sqrt(2X), q prime) 1/q << 1/L.
```

Summation proves the bound. No lower or asymptotic joint-primality assertion enters. Odd `h` contribute zero for sufficiently large `X`.

Source: `/corpus/src/2101.03440/HR_shift.tex`, lines 265–280, displays precisely the two-linear-form sieve bound with general integer coefficients; the constant convention at 87–90 is uniform unless a dependence is indicated. The restricted-factor corollary alone has an `E(x)+O(1)` term and would lose the extra balanced-range logarithm. The proof above uses its internal sieve bound, not that corollary.

The elementary identity

```
n/phi(n)=sum_(d|n) mu(d)^2/phi(d)
```

and convergence of `sum_d mu(d)^2/[d phi(d)]` give a finite Cesaro mean. Therefore, for any fixed `0<A<B`,

```
sum_(A L<h<B L) [N_h(X)+N_(-h)(X)]
  <= C (B-A) X/L^2 + o_(A,B)(X/L^2),
```

with an absolute, nonoptimized `C`. The small-width assertion takes `X->infinity` first with `A,B` fixed; no shrinking-band uniformity is asserted.

## 2. What it gives in the near-square sieve

Let `R_X={X<n<=2X : P^-(n)>sqrt X}` and let `S(X)` count its composite vertices. Unique factorization and PNT give

```
S(X)=(4 log 2-2+o(1)) X/L^2.
```

Let `E(X)` count adjacent `R_X` gaps in `(A L,B L)`. If the original consecutive-prime gaps eventually avoid a larger band with fixed interior margins, there are no prime–prime edges in `E(X)`: adjacent rough prime endpoints would be globally consecutive primes.

Split the remaining edges into prime–semiprime and semiprime–semiprime edges. The first type is bounded by the sum in Section 1. Edges of the second type form a subgraph of the ordered path on composite runs, so their number is at most `S(X)`. Thus the missing-band hypothesis has the somewhat sharper necessary consequence

```
E(X) <= [4 log 2-2+C(B-A)+o_(A,B)(1)] X/L^2.
```

The previous degree bound was `E(X)<=2 S(X)`. Neither inequality supplies a contradictory lower bound for `E(X)`. In particular, the prime–semiprime upper bound does not prove even one such pair exists, and dropping an interior mask in a positive upper bound is not a way to restore consecutivity in an existence argument.

## 3. Closest sources do not give a lower bound

* **Exact factor-count lower bounds:** Ford, `2101.03440/HR_shift.tex:138–149`, explicitly distinguishes a fixed number of prime factors from the known `{k,k+1}` alternative and identifies the parity issue.
* **Conditional localized asymptotic:** Debouzy, `1907.06393/Article-Debouzy-arXiv.tex:2221–2227`, still has the sum of a twin-prime term and a localized two-prime-factor term, even after removing prime powers. It assumes an Elliott–Halberstam-type conjecture. The proof uses fixed exponent intervals; constant-factor balance would require width `O(1/log X)` around exponent `1/2`, for which no uniformity is supplied. It concerns shift 2, not a stated logarithmic-shift family.
* **Quadratic forms with a prime coordinate:** Lam–Schindler–Xiao, `1809.10755/1809.10755.tex:59–71`, treats a positive-definite homogeneous binary quadratic form with a weight on one coordinate. It covers neither `qr-h` nor two prime input coordinates. Friedlander–Iwaniec, `1811.05507/1811.05507.tex:26–90`, explicitly labels both-prime coordinates in the Gaussian-prime problem conjectural; their theorem has one prime coordinate and one coordinate with at most seven prime factors.
* **Asymptotic sieve:** Ford's restatement, `math_0401215/math0401215.tex:151–169`, requires a remainder estimate beyond exponent `2/3` and a strong Möbius-weighted bilinear cancellation hypothesis. Those hypotheses have not been verified here for shifted balanced products of primes.
* **Chen in progressions:** Lewulis, `1601.02873/1601.02873.tex:29–35,74–83`, has the prime/P2 alternative and roughness `x^(1/8)`, explicitly including twin primes. It is not an exact balanced E2 theorem.

The main agent checked these primary passages and the upper-bound derivation independently. The record is an arithmetic upper-bound consequence and a source audit, not a proof of the original theorem or its negation.
