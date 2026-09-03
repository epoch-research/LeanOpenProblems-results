# Exact generating functions for prime-period interval covers

## Outcome and scope

**No proof or disproof of the general period-sum bound is obtained:**

\[
 j\!\left(\prod_{p\in\mathcal P}p\right)
 \stackrel{?}{\le}1+\sum_{p\in\mathcal P}(p-1).
\]

In particular, this investigation does **not** resolve `H(k) = O(k²)` or
establish `j(N) = O(Σp)` for arbitrary distinct prime sets.

There are, however, rigorous conclusions about the proposed exact method:

1. The positive denominator gives an exact, phase-independent averaging
   identity. It proves the period-sum bound in the case `Σ1/p < 1`, but does
   not give a sign contradiction when `Σ1/p > 1`.
2. There is an exact truncation/end-strip formulation. **Nonnegativity of
   the cleared polynomial, even together with divisibility, is not equivalent
   to covering.** An explicit one-residue-per-distinct-prime example makes
   this relaxation pass at arbitrarily large lengths.
3. This obstruction can also pass all single-frequency triangle inequalities
   at roots of unity of order dividing `N`, after an algebraic prime extension.
4. Neither the denominator nor an exact full-phase averaging kernel can have
   its degree reduced by cancellation. Turning the covering inequality into
   the exact zero condition for the uncovered-point indicator instead brings
   in all `N` Fourier modes.

These are obstructions to specified reductions, **not** a no-go theorem for
all possible use of the exact generating function. The exact coefficient
condition retains the original arithmetic problem.

`Submission/Spec.lean` was not modified. Its SHA-256 remains
`c961aa894dc05a671003b74cd770bf0efc120992bcaaa79466c418b03e1688e7`.
The proofs below are mathematical proofs; no new Lean formalization is claimed.

## 1. Conventions and the exact averaging identity

Let `𝒫` be a nonempty finite set of **distinct primes**, and put

\[
 N=\prod_p p,\qquad k=|\mathcal P|,\qquad
 D=\sum_p(p-1),\qquad \sigma=\sum_p\frac1p.
\]

For `0 ≤ a_p < p`, define, for all integer `t`,

\[
 m_a(t)=\sum_p1_{t\equiv a_p\ (p)},\qquad f_a(t)=m_a(t)-1.
\]

Thus `f_a(t)` is an integer in `[-1,k-1]`. A cover of `[0,L)` means
`f_a(t) ≥ 0` at every one of those `L` positions. By CRT, arbitrary choices of
these residues are equivalent to translates of divisibility by the primes
of `N`. Consequently `j(N)` is one plus the greatest possible covered length.
The proposed bound is exactly the assertion that no such cover has length
`D+1`.

Write

\[
 Q_p(z)=1+z+\cdots+z^{p-1},\quad Q(z)=\prod_pQ_p(z)=\sum_{i=0}^Dq_i z^i,
\]
\[
 P_a(z)=\sum_p z^{a_p}\frac{Q(z)}{Q_p(z)}-Q(z).
\]

Every `q_i` for `0 ≤ i ≤ D` is strictly positive, `Q(1)=N`, and
`deg P_a ≤ D`. The given generating function is exactly

\[
 R_a(z)=\sum_{t\ge0}f_a(t)z^t=\frac{P_a(z)}{(1-z)Q(z)}.
\]

Set

\[
 C=P_a(1)=N(\sigma-1)=\sum_pN/p-N.
\]

The key identity is

\[
 \boxed{\ \sum_{i=0}^Dq_i f_a(t-i)=C\quad(t\in\mathbb Z).\ } \tag{1}
\]

For the one-sided generating function, the coefficient interpretation of
(1) applies without negative indices when `t ≥ D`.

**Proof.** The coefficients of `Q` have exactly `N/p` total weight in each
residue class modulo `p`. Indeed, convolution with the factor `Q_p` makes the
residue sums uniform, and the other factors have total mass `N/p`. Therefore
`Σ_i q_i 1_{t-i ≡ a_p (p)} = N/p`, regardless of `a_p` and `t`. Subtracting
`Σ_i q_i=N` proves (1). Equivalently, `Q R_a=P_a/(1-z)` has constant
coefficient `C` from degree `D` onward.

**Sparse-case consequence.** If `σ<1`, a cover of `D+1` positions contradicts
(1) at `t=D`, because its left side would be nonnegative and its right side
negative. Hence

\[
 \sigma<1\quad\Longrightarrow\quad j(N)\le D+1. \tag{2}
\]

There is no equality case `σ=1`: reducing `C` modulo any `p∈𝒫` gives
`C ≡ N/p (mod p)`, which is nonzero. In the difficult case `σ>1`, (1) instead
prescribes a positive weighted amount of overlap excess. It does not force
that excess to vanish.

## 2. The precise end-strip formulation

For an integer `L≥1`, let

\[
 b_p=(a_p-L)\bmod p\in\{0,\ldots,p-1\},\qquad
 A_L(z)=\sum_{t=0}^{L-1} f_a(t)z^t.
\]

The exact tail identity is

\[
 R_a=A_L+z^LR_b,
\]

and hence

\[
 \boxed{\ (1-z)Q A_L=P_a-z^LP_b.\ } \tag{3}
\]

Define the polynomial

\[
 H_L(z)=\frac{P_a(z)-z^LP_b(z)}{1-z}=Q(z)A_L(z). \tag{4}
\]

It is a polynomial because `P_a(1)=P_b(1)=C`. For `0≤r<D` put
`c_a(r)=Σ_{i=0}^r [z^i]P_a`, and similarly define `c_b(r)`. When `L>D`,
its coefficients are exactly

\[
 [z^t]H_L=
 \begin{cases}
 c_a(t),&0\le t<D,\\
 C,&D\le t<L,\\
 C-c_b(t-L),&L\le t<L+D,\\
 0,&t\ge L+D.
 \end{cases} \tag{5}
\]

Thus coefficientwise nonnegativity of **the product** `Q A_L` reduces to
conditions on two strips of width `D` and a constant plateau. But the exact
covering condition is

\[
 \boxed{\ A_L\in\mathbb Z_{\ge0}[z]
 \quad\Longleftrightarrow\quad
 H_L\in Q\,\mathbb Z_{\ge0}[z].\ } \tag{6}
\]

It is not enough that

\[
 H_L\in\mathbb Z_{\ge0}[z]\cap Q\mathbb Z[z]. \tag{7}
\]

Multiplication by a positive polynomial preserves coefficientwise
nonnegativity; division by it need not. The next example disproves the
replacement of (6) by (7) **within the genuine special-numerator class**.

## 3. A strictly positive, genuine-prime obstruction

Take

\[
 \mathcal P=\{2,3,5,7\},\qquad (a_2,a_3,a_5,a_7)=(0,0,4,6).
\]

Here `N=210`, `D=13`, `σ=247/210`, and `C=37`. In increasing degree order,

```
Q = [1,4,9,15,21,26,29,29,26,21,15,9,4,1],
P = [1,2,2,1,1,1,2,3,4,5,6,5,3,1].
```

In particular, **both polynomials have strictly positive coefficients**.
Nevertheless `f_a(0)=1` and `f_a(1)=-1`: the point `1` belongs to none of the
four chosen residue classes.

For every integer `r≥1`, take `L=210r`. Then `b=a`, so (4) becomes

\[
 H_L=P_a(1+z+\cdots+z^{L-1}). \tag{8}
\]

Every coefficient from degree `0` through `L+D-1` is strictly positive.
Moreover `Q | H_L` in `Z[z]`, either by (3), or because every `Q_p` divides
`1+z+⋯+z^{L-1}` and the `Q_p` are pairwise coprime. But

\[
 [z^1](H_L/Q)=[z^1]A_L=-1.
\]

The two end strips in (5) are, explicitly,

```
left:  [1,3,5,6,7,8,10,13,17,22,28,33,36],
right: [36,34,32,31,30,29,27,24,20,15,9,4,1],
```

and the entire middle strip is `37`, regardless of `r`.

This example retains all of the following:

- distinct prime periods, with exactly one residue per prime;
- the prescribed numerator `P_a`, not an arbitrary recurrence numerator;
- integer coefficients `-1≤f_a(t)≤3` globally;
- all exact tail-phase and cyclotomic divisibility conditions;
- strictly positive numerator, denominator, and cleared end strips.

Yet the relaxed end-strip condition accepts arbitrarily large `L`. In a full
period the excess histogram is

```
f=-1: 48 positions;  f=0: 92;  f=1: 56;  f=2: 13;  f=3: 1.
```

Thus (8) hides `48r` actual uncovered positions.

**This is NOT a counterexample to the period-sum bound.** Exact enumeration of
the 48 reduced residues modulo 210 gives `j(210)=10<14=D+1`; for example,
`200,...,208` are covered between the consecutive reduced residues 199 and
209. The example refutes the end-strip relaxation, not actual covering.

### Stability under adding distinct primes

Adding a new prime `q` and any residue `a_q` gives

\[
 Q_{\rm new}=Q Q_q,\qquad
 P_{\rm new}=P_a Q_q+z^{a_q}Q. \tag{9}
\]

Starting with the example above, strict coefficient positivity is therefore
preserved under every such extension. Choosing every new residue to be zero
also preserves the uncovered point `t=1`. For every extended prime set, all
full-period lengths again pass (7). This is an algebraic family of
obstructions, not an extrapolation from a finite search.

## 4. What roots of unity do and do not add

Let `ζ≠1` have order `p∈𝒫`. Because the primes are distinct,

\[
 P_a(\zeta)=\zeta^{a_p}(Q/Q_p)(\zeta)\ne0. \tag{10}
\]

The same formula for `b`, together with `L+b_p≡a_p (mod p)`, gives

\[
 P_a(\zeta)=\zeta^L P_b(\zeta). \tag{11}
\]

Thus the root equations enforcing divisibility in (3) are automatically
satisfied at **every** `L`, covered or not. Evaluating the cleared numerator
at these roots does not supply a new covering constraint.

One can also use positivity of the *quotient* to obtain inequalities. For
example, nonnegative coefficients of `A_L` imply
`|A_L(ζ)|≤A_L(1)` on the unit circle. These are genuine additional constraints,
not tautologies. But even all the single-frequency tests at `N`th roots do
not suffice:

Extend (9) to the first ten primes, with residues zero at
`11,13,17,19,23,29`. Then

\[
 N=6469693230,\quad D=119,\quad
 \sigma=\frac{9920878441}{6469693230}>\frac32.
\]

The numerator is still strictly positive and `f_a(1)=-1`. At a full-period
length `L=rN`, direct summation of the geometric series gives

\[
 A_L(1)=L(\sigma-1),\qquad
 A_L(\zeta)=\frac Lp\zeta^{a_p}\quad(\operatorname{ord}\zeta=p\in\mathcal P),
 \tag{12}
\]

and `A_L(ζ)=0` at every other nontrivial `N`th root. Since
`σ-1>1/2≥1/p`, **all** of these triangle inequalities pass, as do the cleared
end-strip conditions, despite the genuine negative coefficients.

This does not rule out coupled Fourier/positive-definiteness inequalities.
Those retain more information than individual root values or magnitudes.

## 5. Exact degree obstructions and Fine–Wilf

### No denominator cancellation

Equation (10) shows that no `Q_p` cancels against `P_a`. Also `P_a(1)=C≠0`
by the congruence in section 1. Therefore

\[
 \gcd(P_a,(1-z)Q)=1.
\]

The minimal denominator of `R_a`, and hence the minimal constant-coefficient
linear-recurrence order of `f_a`, has degree **exactly `D+1`**. Large periods
cannot be replaced by small occurrence-count weights simply by cancelling
factors in this exact generating function.

### Minimal degree of any exact phase-independent averaging polynomial

Suppose a nonzero polynomial `W(z)=Σw_i z^i` has equal coefficient sums in
each residue class modulo every `p∈𝒫`. Then `W(ζ)=0` at every nontrivial
`p`th root, so `Q_p | W` for every `p`, and therefore

\[
 Q\mid W,\qquad \deg W\ge D. \tag{13}
\]

Conversely, these divisibilities imply the uniform residue sums. At degree
`D`, such a polynomial is necessarily a scalar multiple of `Q`. Positivity
of `W` is not needed for the degree lower bound.

Thus the proposed denominator already gives the unique minimum-degree
full-phase averaging kernel, up to scale. A sharper count-weighted degree
cannot come from a different **exact, phase-independent** kernel. Approximate,
residue-dependent, or partial averaging is not excluded by (13).

### Equality propagation is not inequality propagation

The `D+1` distinct exponential modes of `f_a` give a Vandermonde argument:
if `f_a` is zero on `D+1` consecutive positions, it is identically zero.
Hence an *exactly-once* cover cannot have that length. An ordinary cover only
says `f_a≥0`, so this equality argument does not apply. Assigning one label
to each covered position does not repair it: resolving overlaps destroys the
periodicity of the individual columns.

For comparison only, the sequence

\[
 g(t)=k-1-\sum_p1_{t\equiv p-1\ (p)}
\]

has the same distinct prime frequency orders, integer range `[-1,k-1]`, and
`g(t)≥0` for `0≤t<N-1`, but `g(N-1)=-1`, by CRT. Its local summands cover
`p-1` residues, not one, so it is **not** in the original special-numerator
class. This illustrates the limitation of generic recurrence arguments; the
main counterexample in section 3 does not rely on this relaxation.

### The exact hole indicator has all N modes

There is an equality formulation that retains the actual one-class system:

\[
 u_a(t)=1_{m_a(t)=0}=\prod_p(1-1_{t\equiv a_p\ (p)}).
\]

But this is a **pointwise product**, not the ordinary product of the generating
functions. On the CRT group `∏_p Z/pZ`, each local factor has Fourier coefficients

\[
 1-1/p\quad\text{at the trivial character},\qquad
 -\frac1p e^{-2\pi i h a_p/p}\quad(h\not\equiv0\pmod p).
\]

Every coefficient is nonzero. Their products give a nonzero coefficient at
**every one of the `N` characters**. Consequently

\[
 \sum_{t\ge0}u_a(t)z^t
   =\frac{\sum_{t=0}^{N-1}u_a(t)z^t}{1-z^N}
\]

has no denominator cancellation and minimal recurrence order `N`, not
`D+1`. Applying equality propagation to this exact indicator therefore
recovers only the full-period scale by that route. This is not a claim that
its special structure cannot yield a better estimate by other methods.

## 6. The integer lower bound and count-weighted consequences

The lower bound `f_a(t)≥-1` gives a useful necessary Abel inequality. A cover
of `[0,L)` would imply, for `0<x<1`,

\[
 R_a(x)\ge -\frac{x^L}{1-x},\qquad
 P_a(x)+x^LQ(x)\ge0. \tag{14}
\]

The numerator-positive examples above satisfy (14) for **every** `L`, despite
their holes. This particular use of the integer lower bound cannot rescue
the end-strip argument.

There is also an exact first-moment/count formula. The number of occurrences
of residue `a_p` in `[0,L)` is

\[
 n_p(L)=\frac{L+b_p-a_p}{p}.
\]

Differentiating (3) at `1`, or simply summing the multiplicities, gives

\[
 A_L(1)=\sum_p n_p(L)-L
       =L(\sigma-1)+\sum_p\frac{b_p-a_p}{p}. \tag{15}
\]

Under covering this is nonnegative. Since the absolute value of the last
sum is at most `Σ(p-1)/p=k-σ`, it yields the elementary necessary bound

\[
 L\le\frac{k-\sigma}{1-\sigma}\quad\text{if }\sigma<1. \tag{16}
\]

No bound for the dense case follows from this first moment: its leading term
has the wrong sign. Formula (2) is a separate, sometimes stronger, consequence
of the full positive kernel.

More generally, at a full-period length, averaging `f_a` only over positions
avoiding a subset `S` of the chosen residues gives exactly

\[
 \sum_{0\le t<L}f_a(t)\prod_{p\in S}(1-1_{t\equiv a_p\ (p)})
 =L\prod_{p\in S}(1-1/p)\left(\sum_{p\notin S}1/p-1\right). \tag{17}
\]

For every fixed integer `r`, extend the positive-numerator example by enough
initial primes that the sum of reciprocals remaining after removal of any
`r` primes is greater than one. This is possible because the sum of prime
reciprocals diverges. Then every test (17) with `|S|≤r` is nonnegative, while
the hole at `1` remains. Thus these fixed-order averaged sign tests also
cannot replace coefficientwise positivity. This leaves open higher-order,
length-sensitive, or non-averaged inequalities.

## 7. Status of the actual period-sum proposal

For the first `k` primes, the proposed bound would give

\[
 j(p_k\#)\le(1/2+o(1))k^2\log k
          =(1/2+o(1))\frac{p_k^2}{\log p_k}.
\]

This is a genuine logarithmic improvement over the cited Iwaniec-scale bound,
not something supplied by the rational-function degree calculation.
Furthermore, a pointwise sum-of-actual-primes bound would not by itself imply
a uniform quadratic bound in `k`: the actual primes are not bounded above by
the first `k` primes. The primorial and maximal Jacobsthal functions must not
be identified.

The unresolved algebraic statement is precisely exclusion of

\[
 \frac{P_a-z^L P_b}{(1-z)Q}\in\mathbb Z_{\ge0}[z]
 \quad\text{for }L>D,\qquad b_p\equiv a_p-L\pmod p. \tag{18}
\]

For (18), retaining the quotient's individual coefficient inequalities
retains the original problem. Dropping them in favor of the positive
cleared end strips is provably invalid. Neither the exact period-sum
assertion nor any universal `O(Σp)` bound is proved or refuted here.

## 8. Verification and corpus evidence

### Reproducible fixed certificates

Run, from `/workspace/leanproject`:

```
python3 Submission/verify_period_sum_gf.py
```

Output is saved in `Submission/PeriodSumGFFiniteCheck.log`. This uses only
exact integers and rational numbers in Python's standard library. It checks:

- the displayed `P` and `Q` coefficient vectors;
- the truncation and end-strip identities at eleven specified lengths;
- the full-phase averaging weights and one-period convolution identity;
- positive cleared coefficients but negative quotient coefficients at
  `L=210,420,630` (the proof of all `L=210r` is (8));
- the same relaxed failure at `L=D+1=14`;
- exact occurrence-count formula (15);
- all cyclotomic pole orders of the excess and hole indicator for `N=210`;
- the algebraic prime extension and exact threshold `σ>3/2` for (12), without
  enumerating the enlarged full period;
- `j(210)=10`, to prevent confusing the obstruction with a conjecture
  counterexample;
- the unchanged SHA-256 of `Spec.lean`.

An independent SymPy calculation also verified the rational generating
identity, the displayed positive numerator, and
`gcd(P,(1-z)Q)=1` for the fixed example. There was no prime/residue parameter
search and no extrapolation of a numerical Jacobsthal bound to an asymptotic
claim.

### Sources consulted

- F. Costello and P. Watts, *A short note on Jacobsthal's function*,
  arXiv:1306.1064, `/corpus/src/1306.1064/1306.1064.tex`, introduction,
  lines 29–47: the uniform bound `g(n)≪(k log k)²` and the distinction from
  explicit elementary bounds.
- W. D. Banks, K. Ford, and T. Tao, *Large prime gaps and probabilistic models*,
  arXiv:1908.08613,
  `/corpus/src/1908.08613/GAPS-MODEL-20190822b.tex`, lines 604–622:
  the primorial/interval-sieve form `J(z)≪z²` and the effect of stronger
  interval-sieve lower bounds.
- M. Ziller, *New computational results on a conjecture of Jacobsthal*,
  arXiv:1903.11973, `/corpus/src/1903.11973/Ziller_2019.tex`, definitions
  and discussion around lines 50–75, results table around lines 443–475:
  `H(k)` is not in general the primorial value `h(k)`; for example,
  `H(24)=236>234=h(24)`. These are source-reported computations, not a new
  exhaustive computation here and not counterexamples to the period-sum
  proposal.
- S. A. Rankin, *Fine-Wilf graphs and the generalized Fine-Wilf theorem*,
  arXiv:0906.1780, `/corpus/src/0906.1780/0906.1780.tex`, opening discussion:
  Fine–Wilf concerns equality/period compatibility, not an inequality for
  a sum of periodic indicator functions.

The new algebraic identities and obstruction in this report have their own
proofs above; none is being attributed to these references or taken as an
assumption in `Spec.lean`.
