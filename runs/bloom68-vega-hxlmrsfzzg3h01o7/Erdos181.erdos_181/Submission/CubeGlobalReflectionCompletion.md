# Global full-pattern transfer: exponential loss and a sparse product-weight repair

**The full conjecture is not proved.** `Submission/Spec.lean` is unchanged.
This note records a precise failure of an **unweighted maximum-relative initial
transfer**, not another absolute-baseline error example. It also proves an exact
product-weighted, all-pattern comparison for the same family of actual hosts.
There is no extension of that comparison to arbitrary colourings here.

Use the full labelled injection counts `T_sigma` and reduced square-pattern
family `mathcal R_d` from `CubeFullPatternReflection.md`. Put

\[
 M=\max_\sigma T_\sigma,\qquad
 M_{\mathcal R}=\max_{\tau\in\mathcal R_d}T_\tau.
\]

The attempted initial-transfer inequality was

\[
 \boxed{M_{\mathcal R}\ge a(C)M\quad(N=C2^d),\qquad a(C)>0.} \tag{MT}
\]

**(MT) is false for every fixed integer `C>=3`.** Even replacing `a(C)` by
any positive inverse polynomial in `d` cannot make it true.

## 1. An actual colouring with exponentially small reduced maximum

Let `d>=3`, `t=2^(d-3)`, `h=8t`, and let `C>=3` be an integer. Partition the
host into sets `A,B` of sizes

\[
 a=(4C+1)t,\qquad b=(4C-1)t,\qquad a+b=Ch=N.
\]

Colour within each part red and between the parts blue. Both parts have at
least `h` vertices. In particular **both monochromatic cube counts are positive**;
this is not a counterexample to Ramsey existence or to a zero-monochromatic-count
qualified inequality.

### Exact full counts

For a source vertex subset `S`, let `sigma_S` be blue precisely on the edges
crossing `S`. Write

\[
 f(s)=(a)_s(b)_{h-s},\qquad F(s)=f(s)+f(h-s).                 \tag{1}
\]

Then `T_(sigma_S)=F(|S|)`. Indeed, the two possible host-part assignments are
`S -> A, S^c -> B` and their interchange. Their counts are the two products
of falling factorials in (1). Each product counts distinct host labels on
both source classes, and the host classes are disjoint.

Conversely, every injection into this colouring produces a cut pattern.
Since the cube is connected, a cut pattern determines its source vertex
subset up to complement. Thus every full-pattern count is either zero or
one of the values `F(s)`, and

\[
 M=\max_{0\le s\le h} F(s).                               \tag{2}
\]

This is an exact count of full injections, not a homomorphism calculation.

### Exact reduced maximum

A reduced pattern is pulled back from a square by

\[
 x\longmapsto (x_i,p_{[d]\setminus\{i\}}(x)).
\]

Each square vertex has `h/4=2t` preimages. A square pattern with an odd number
of blue edges cannot occur in this host: restrict to the square using coordinate
`i` and any other coordinate. An even-blue square pattern is a cut, and its
lift has source part size `2jt`, `0<=j<=4`. All these sizes occur, up to
complement. Consequently

\[
 M_{\mathcal R}=\max_{0\le j\le4} F(2jt).                  \tag{3}
\]

The ratio

\[
 \frac{f(s+1)}{f(s)}=\frac{a-s}{b-h+s+1}
\]

shows that `f` increases up to `s=5t` and decreases thereafter. The factorial
formula also gives `f(6t)=f(4t)` and `f(8t)=f(2t)`. Therefore

\[
 \begin{aligned}
 F(0)&=f(0)+f(2t)\le2f(4t),\\
 F(2t)&=f(2t)+f(4t)\le2f(4t),\\
 F(4t)&=2f(4t).
 \end{aligned}
\]

By symmetry these cover all five values in (3). In particular

\[
 \boxed{M_{\mathcal R}=T_{m_B}=2f(4t),\qquad
               T_{m_R}\le T_{m_B}.}                       \tag{4}
\]

On the other hand, a cut of size `5t` is an allowed full pattern, so
`M>=F(5t)>=f(5t)`. Direct cancellation of falling factorials gives

\[
 \frac{f(4t)}{f(5t)}
 =\prod_{j=0}^{t-1}\frac{(4C-4)t-j}{(4C-3)t-j}
 \le\left(\frac{4C-4}{4C-3}\right)^t.
\]

With exactly the reflection parameter `q=h/(4N-3h)=1/(4C-3)`, this proves

\[
 \boxed{\frac{M_{\mathcal R}}M
       \le2(1-q)^{h/8}\le2e^{-qh/8},\qquad
 \frac{T_{m_R}+T_{m_B}}M\le4e^{-qh/8}.}                    \tag{5}
\]

These are actual complementary-colour full-pattern counts. Thus even a
summed two-colour lower bound by a dimension-independent positive multiple
of `M` is false. The loss occurs **before** any comparison confined to the
16 square patterns can help.

### Consequence for a global reflection defect

For the three-stage operator `H=P Q_a P` from the previous report, every
output belongs to `mathcal R_d`. If `sigma_*` is any maximizer in (2), then

\[
 M-(HT)(\sigma_*)\ge(1-2e^{-qh/8})M.                       \tag{6}
\]

In fact (6) holds for any probability kernel whose outputs are reduced.
It rules out an **unqualified** estimate of this defect by `epsilon(C)M`
with `epsilon(C)<1`, regardless of how many elementary folds implement
that kernel. Explicitly, such an upper bound fails whenever
`2^d > 8(4C-3) log(2/(1-epsilon(C)))`. All exact Kneser identities and
joint-colour sector inequalities hold in this example, since it is an actual
host colouring.

Equation (6) does **not** refute the zero-level estimate (7.6) in
`CubeFullPatternReflection.md`: its hypothesis that both monochromatic
counts vanish fails here. Nor does (5) rule out a multiplicative comparison
with loss exponential in `h`.

## 2. A sparse positive product-weight repair, proved globally for this family

The following positive statement concerns **all full patterns simultaneously**,
not conditional half-extension laws. It is useful for distinguishing a failure
of unweighted normalization from a failure of every product-weight approach.

**Proposition.** Let `J` be any connected balanced bipartite source graph on
`h=2m>=2` vertices. Use the same two-part host colouring, now with arbitrary
integers `a=b+p`, `b>=h`, `p>=1`. Choose `p` vertices of `A` as an exceptional
set `E`, leaving exactly `b` unweighted vertices in `A`. Set

\[
 w_v=\begin{cases}
 \epsilon=(b-h+1)/(p(b+1)),&v\in E,\\
 1,&v\notin E.
 \end{cases}                                              \tag{7}
\]

Then `0<epsilon<1`. For patterns on `E(J)`, define

\[
 T_\sigma(w)=\sum_{\phi\text{ a full injection realizing }\sigma}
                         \prod_{x\in V(J)}w_{\phi(x)}.
\]

For these explicit positive product weights,

\[
 \boxed{\max_\sigma T_\sigma(w)=T_{m_B}(w)>0.}             \tag{8}
\]

Only `p` original host vertices have weights different from one.

**Proof.** Let `Z_A(s)` be the total product weight of ordered injections of
`s` distinct source labels into `A`. It is positive for `0<=s<=h`. Under
this weighted injection law, let `K` be the number of used exceptional
vertices. Appending one unused host vertex gives the exact ratio

\[
 \frac{Z_A(s+1)}{Z_A(s)}
     =b-s+p\epsilon+(1-\epsilon)\mathbb E K.               \tag{9}
\]

For a specified `v in E`, its occupancy probability is

\[
 \Pr(v\text{ is used})
   =\frac{s\epsilon Z_{A\setminus\{v\}}(s-1)}{Z_A(s)}
   \le\frac{s\epsilon}{b-s+1}.                            \tag{10}
\]

For the inequality, append an unused unweighted vertex to an ordered
`(s-1)`-injection avoiding `v`. There are at least `b-s+1` choices. The
prefix and last image are recoverable from the resulting `s`-injection,
so this is a literal injective counting map. For `s=0`, the occupancy is zero.

Sum (10) over the `p` exceptional vertices. Equations (7)--(9) give, for
`0<=s<h`,

\[
 b-s\le\frac{Z_A(s+1)}{Z_A(s)}
 \le b-s+p\epsilon\frac{b+1}{b-s+1}
 =b-s+\frac{b-h+1}{b-s+1}<b-s+1.                          \tag{11}
\]

Put `g(s)=Z_A(s)(b)_(h-s)`. Then

\[
 \frac{g(s+1)}{g(s)}
   =\frac{Z_A(s+1)/Z_A(s)}{b-h+s+1}.
\]

By (11), this ratio is greater than one for `s<m` and less than one for
`s>=m`. Hence `g` has its unique maximum at `m`. The cut-counting bijection
from Section 1 remains valid with these weights: every nonzero full-pattern
count is `g(s)+g(h-s)`. This is at most `2g(m)`, which is exactly the all-blue
count because the source has equal bipartition sizes. Moreover
`2g(m)>=2(b)_m^2>0`, by using only the unweighted cores. This proves (8). `□`

In the cube family of Section 1, `p=a-b=2t=h/4=N/(4C)`. Thus for `C>=32`
the repair changes at most `N/128` vertex weights, and it yields

\[
 M_{\mathcal R}(w)=M(w)=T_{m_B}(w).
\]

This matches the *size* of the sparse-penalty budget in the higher-block
work, but it is a separate explicit construction. No claim is made that
those general block weights satisfy (8), or that vertex-occupancy bounds
alone imply it. The proof here uses the complete two-part structure in
(9)--(11).

## 3. Exact stopping point and audit

The universal unweighted initial transfer (MT) fails exponentially by (5).
The sparse product-weight repair is proved only for the displayed two-part
hosts. I did **not** obtain a corresponding global comparison for arbitrary
colourings, or a signed-defect bound under the zero-monochromatic-count
hypothesis. In particular there is no completing argument for fixed `N/h`.

Run

```text
python3 Submission/check_cube_global_reflection_completion.py
```

The audit checks the cut-count formulas against direct enumeration of **full
injections**, independently classifies all represented reduced patterns in
small dimensions, verifies the exact maximum and rational ratio bounds,
and tests (9)--(11) and (8) using an independent weighted counting formula.
It does not replace any all-dimensional proof above with finite testing.
Its output is saved in `CubeGlobalReflectionCompletionVerification.txt`.

No Lean source was edited or used as an assumption. The unchanged SHA-256
of `Submission/Spec.lean` is

```text
9cb89c42b7983ce8600b21cf6ffe9861fee7d6baca58206d9fa2d51c0636203b
```

**Full conjecture proved: no.** The precise new obstruction is (5), including
the initial transfer; the precise positive result is the restricted but
all-pattern product-weight theorem (8).
