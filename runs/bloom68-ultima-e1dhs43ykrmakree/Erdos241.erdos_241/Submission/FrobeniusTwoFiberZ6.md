# The Frobenius two-fiber Z/6 family is uniformly impossible

## Result

Let `q = 2^m`, let `theta` have degree three over `F_q`, and put
`z_t = theta + t`. In CRT coordinates write the proposed points as

\[
 U_t=(0,\epsilon_0(t),z_t),\qquad
 V_t=(1,\epsilon_1(t),z_t^2)
 \quad\text{in }\mathbb Z/3\times\mathbb Z/2\times K^*.
\]

Here **strong B3** means uniqueness of every unordered three-term sum,
including all repetitions.

**Theorem.** For every positive odd `m`, no choices of the two binary
functions make the full `2q`-point set strong B3. In fact:

* For every `q > 2`, a three-equation parity obstruction works for every
  `theta`, without using any finite-field arithmetic beyond the identity
  `(z_a z_b)^2 = z_a^2 z_b^2`.
* The remaining case `q = 2` also has a three-equation contradiction; its
  certificate uses the pure-branch collisions as well as a mixed collision.
* Independently, for every odd `m` and every degree-three `theta`, the
  **exact number of three-element 2+1 field fibers** is
  \[
    N_3=\frac{q(q^2-4)}{48}=\binom{q/2+1}{3}.
  \]
  It is positive for every admissible `q >= 8`. Thus a trace restriction
  forcing at most two rational mixed triples does not occur.

More precisely, if `N_j` counts field outputs with exactly `j` unordered
triples `(a,b;c)`, where `a,b` are the branch-0 parameters and `c` is the
branch-1 parameter, then

\[
\boxed{
 N_1=\frac{q(5q^2+4q+4)}{16},\quad
 N_2=\frac{q^2(q+2)}{16},\quad
 N_3=\frac{q(q^2-4)}{48},\quad N_j=0\ (j>3).
}
\]

These are proved below, not extrapolated from the finite audits.

## 1. The shortest uniform obstruction: repeated summands

For distinct parameters `a,b`, consider

\[
  2U_a+V_b\quad\text{and}\quad 2U_b+V_a.
\]

They are distinct multisets. Their mod-3 coordinates are both 1, and their
field coordinates are both `(z_a z_b)^2`. Their mod-2 coordinates are,
respectively, `epsilon_1(b)` and `epsilon_1(a)`; the repeated branch-0
summands cancel from the parity calculation.

Consequently, strong B3 would require

\[
 \epsilon_1(a)+\epsilon_1(b)=1\qquad(a\ne b).
\]

Choose any three distinct parameters `a,b,c`. Adding the equations for
`{a,b}`, `{b,c}`, and `{a,c}` gives **`0 = 1` in F2**. Equivalently, a binary
function cannot be injective on three parameters. This proves impossibility
for every `q > 2`, for every `theta`, and even without the cyclicity assumption.

This is a structural obstruction to a doubled second branch, rather than
an obstruction peculiar to Bose sets or to a particular minimal polynomial.
In `Z/6`, a branch-0 tag is either 0 or 3, so twice that tag is always 0.

### Deleting a small number of points does not repair this full construction

If the retained branch parameter sets are `R,S subset F_q`, the same argument
applies to `R intersect S`, forcing `|R intersect S| <= 2`. Therefore any strong
B3 subset of this form satisfies

\[
 |R|+|S|\le q+2.
\]

Thus deleting only `o(q)` points from the proposed `2q` points cannot suffice.
This statement concerns subsets with at most one chosen tag per parameter
per branch, exactly as in the proposed family.

## 2. The q = 2 edge case, including pure-branch collisions

After possibly replacing `theta` by `theta+1` (just a parameter relabeling),
we may assume `theta^3 = theta+1`. Every degree-three element over `F_2` is
covered by this normalization. Put `x=theta`, so `x` has order 7. The field
coordinates of `U_0,U_1,V_0,V_1` are

\[
 x,\ x^3,\ x^2,\ x^6.
\]

The following are three necessary separations. The equalities in the middle
column are equalities of the field coordinate, **not assertions that the
arbitrary parity tags already agree**.

| Distinct triple multisets | Common field output | Necessary parity equation |
|---|---:|---|
| `3U_0` and `2V_0+V_1` | `x^3` | `epsilon_0(0)+epsilon_1(1)=1` |
| `2U_0+V_1` and `2U_1+V_0` | `x` | `epsilon_1(0)+epsilon_1(1)=1` |
| `U_0+2U_1` and `V_0+2V_1` | `1` | `epsilon_0(0)+epsilon_1(0)=1` |

The mod-3 coordinates agree in each row: 0 in the first and third rows,
and 1 in the second. The three parity equations again sum to `0=1`.
The exact audit additionally tested all 16 binary tag vectors and found
zero strong B3 assignments.

## 3. Which theta changes are legitimate?

Write the minimal polynomial as

\[
 f(X)=X^3+uX^2+vX+w.
\]

Replacing `theta` by `theta+u` gives the depressed polynomial

\[
 X^3+(u^2+v)X+(uv+w).
\]

When `m` is odd, `q = 2 mod 3`, so the cube map on `F_q^*` is bijective.
Thus `u^2+v` cannot vanish: otherwise this depressed cubic would have a root
in `F_q`. Let `lambda^2=u^2+v`. Dividing the translated generator by
`lambda` gives a generator with irreducible polynomial

\[
 X^3+X+\omega.
\]

If `theta = lambda*theta' + u`, then

\[
 z_t=\lambda\left(\theta'+\frac{t+u}{\lambda}\right).
\]

A product with `k` branch-1 summands scales by `lambda^(3+k)`. Therefore
this affine normalization preserves **every within-composition field-fiber
cardinality**, in particular all 2+1 and 1+2 fiber counts.

**Important limitation:** scaling need not preserve collisions between
all-branch-0 and all-branch-1 triples, since their scale factors are
`lambda^3` and `lambda^6`. We do not use scaling as an equivalence of the
full parity problem. The uniform obstruction in Section 1 needs no such
normalization. At `q=2`, the only nonzero scale is 1, so Section 2 covers
all generators without this issue.

## 4. The mixed-fiber cubic, with its exceptional denominator resolved

For a 2+1 triple put

\[
 s=a+b,\quad p=ab,\quad z=c^2.
\]

In characteristic two,

\[
 (X+a)(X+b)(X+c)^2
 =X^4+sX^3+(p+z)X^2+szX+pz.
\]

Its remainder modulo `f` is `h_2 X^2+h_1 X+h_0`, where

\[
\begin{aligned}
 h_2&=u^2+v+us+p+z,\\
 h_1&=uv+w+s(v+z),\\
 h_0&=uw+ws+pz.
\end{aligned}
\]

Set `A=h_2+u^2+v`, `B=h_1+uv+w`, `C=h_0+uw`. Elimination gives

\[
 \boxed{(z+v)(z^2+Az+C)+B(uz+w)=0,}
\]

or

\[
 z^3+(A+v)z^2+(C+Av+uB)z+Cv+wB=0.
\]

For `z != v`, recover `s=B/(z+v)` and `p=A+z+us`.
For `z=v`, necessarily `B=0`, and instead

\[
 s=\frac{C+v^2+Av}{uv+w},\qquad p=A+v+us.
\]

The denominator is nonzero: if `uv+w=0`, then
`f=(X+u)(X^2+v)`, contrary to irreducibility. Thus **each root z determines
at most one unordered pair `{a,b}`**, even at the exceptional denominator.
The pair exists exactly when `X^2+sX+p` splits over `F_q`. If `s=0`, it is
the unique repeated pair; if `s!=0`, the criterion is
`Tr_{F_q/F_2}(p/s^2)=0`. Also `c` is uniquely determined by `c^2=z`.

This proves the bound of three for **every** 2+1 fiber, not merely generically.

## 5. Exact uniform count via a nondegenerate trace form

Normalize to `f=X^3+X+w` as in Section 3. Then

\[
 A=h_2+1,\ B=h_1+w,\ C=h_0,
 \qquad F_h(z)=(z+1)(z^2+Az+C)+Bw.
\]

The map from `(h_0,h_1,h_2)` to the three coefficients of this monic cubic
is bijective, since `w!=0`.

### 5.1 Three distinct cubic roots and the splitting conditions

Suppose `F_h` has three distinct roots `z_i=c_i^2`. Vieta's formulas and
the reconstruction above give, for `{i,j,k}={1,2,3}`,

\[
 s_i=\frac{(z_j+1)(z_k+1)}w,
 \qquad p_i=1+z_j+z_k.
\]

These formulas also hold at `z_i=1`, by the exceptional reconstruction.
If neither `c_j` nor `c_k` is 1, set

\[
 \alpha_j=(c_j+1)^{-1},\qquad\alpha_k=(c_k+1)^{-1}.
\]

Using invariance of the absolute trace under squaring,

\[
 \operatorname{Tr}(p_i/s_i^2)
 =\operatorname{Tr}\bigl(w(\alpha_j^2\alpha_k+
       \alpha_j\alpha_k^2+\alpha_j^2\alpha_k^2)\bigr).
\]

Define the symmetric F2-bilinear form

\[
 \mathcal B(x,y)=\operatorname{Tr}\bigl(w(x^2y+xy^2+x^2y^2)\bigr)
 \quad\text{on }F_q.
\]

### 5.2 Why this form is nondegenerate

Let `rho=sqrt(w)`. The coefficient of `y` under the trace pairing is

\[
 L(x)=wx^2+\sqrt{wx}+\rho x,
 \qquad \mathcal B(x,y)=\operatorname{Tr}(L(x)y).
\]

If a nonzero `x` were in the radical, then `L(x)=0`. Squaring gives

\[
 0=L(x)^2=wx(wx^3+x+1).
\]

But `wx^3+x+1=0` says precisely that `1+x^{-1}` is a root of
`X^3+X+w`, contradicting irreducibility. Hence the radical is zero.
Also

\[
 \mathcal B(x,x)=\operatorname{Tr}(wx^4)
\]

is a nonzero linear functional. Put `n=q/2`, `r=n-1`. There are `r`
nonzero isotropic vectors and `n` anisotropic vectors.

### 5.3 Orthogonality edges and triangles

Consider the simple graph on `F_q^*` joining distinct `x,y` when
`mathcal B(x,y)=0`. An anisotropic vertex has degree `r`; an isotropic
vertex has degree `r-1`. Its number of edges is therefore

\[
 E=\tfrac12\bigl(nr+r(r-1)\bigr)=r^2.
\]

For adjacent distinct nonzero `x,y`, their two orthogonality functionals
are independent, so their common orthogonal subspace has `q/4` elements.
After removing 0 and any of `x,y` that are isotropic, summing common-neighbor
counts over edges gives

\[
 3T=E(q/4-1)-r(r-1),
 \qquad T=\binom r3.
\]

This argument is for `q>=4`; for `q=2` the graph has no edges or triangles,
and the same final formulas hold directly.

A three-root set containing `c_i=1` gives two automatic repeated-pair
triples. Its third triple exists exactly when the other two associated
nonzero `alpha` values form an edge. A three-root set not containing 1
gives three triples exactly when its three `alpha` values form a triangle.

The root set uniquely determines the output, and each reconstructed split
product is nonzero, so no zero field output is inadvertently counted.
It follows that

\[
 N_3=E+T=r^2+\binom r3=\binom{r+2}{3}
     =\frac{q(q^2-4)}{48}.
\]

In particular, **exactly `(q-2)^2/4` three-element fibers have the two
repeated-pair triples**

\[
 (a,a;b),\quad(b,b;a),
\]

with a third triple whose branch-1 parameter is 1 in normalized coordinates.
This alone is already a uniform positive three-fiber count for `q>=8`.

### 5.4 The two-element fibers and complete histogram

For three distinct roots with no `c_i=1`, the number of rational mixed
triples is the number of edges induced on the three corresponding graph
vertices. The number inducing exactly two edges is

\[
 W=\sum_x\binom{\deg x}{2}-3T
  =\frac{nr(r-1)}2.
\]

For three distinct roots including 1, a two-element fiber corresponds to
a nonedge among the other two vertices, giving

\[
 \binom{q-1}{2}-E=nr
\]

such fibers.

The remaining two-element fibers come from a cubic with two distinct roots:
write its square-root multiset as `{a,a,b}`, with `a!=b`. At the root `a^2`,
reconstruction gives `s=(a^2+1)(b^2+1)/w`, `p=1+a^2+b^2`; at `b^2`, it gives
`s=(a^2+1)^2/w`, `p=1`. The exceptional reconstruction gives these same
formulas if either root is 1. Thus:

| Case | Condition for two rational mixed triples | Number |
|---|---|---:|
| `a=1` | automatic | `q-1` |
| `b=1` | `(a+1)^(-1)` isotropic | `r` |
| `a,b!=1` | `(a+1)^(-1)` isotropic and orthogonal to `(b+1)^(-1)` | `r(r-1)` |

The sum in this table is `n^2`. A cubic with only one distinct rational root
cannot give two triples. Consequently

\[
 N_2=W+nr+n^2=\frac{n^2(n+1)}2=\frac{q^2(q+2)}{16}.
\]

There are `q*binom(q+1,2)=q^2(q+1)/2` mixed multisets in total, with all
repetitions included. Thus `N_1+2N_2+3N_3=q^2(q+1)/2`, proving the stated
formula for `N_1`. Affine normalization transfers these exact formulas
back to every degree-three `theta` for odd `m`.

## 6. Targeted exact audits: q = 2, 8, 32

The dependency-free Python audit uses the base-field polynomial encodings

* `q=2`: `F_2`;
* `q=8`: `F_2[b]/(b^3+b+1)`;
* `q=32`: `F_2[b]/(b^5+b^2+1)`.

Integers encode coefficients in the binary basis (`2=b`, `4=b^2`, etc.).
It tests **every** `w` for which `X^3+X+w` is irreducible:

| q | w values |
|---:|---|
| 2 | `1` |
| 8 | `2,4,6` |
| 32 | `1,6,7,20,21,22,23,24,25,28,29` |

These normalized representatives cover every generator for purposes of
within-composition fiber cardinalities, as proved in Section 3. No claim
of affine invariance of the pure-branch cross fibers is made.

### 2+1 histograms and full parity ranks

`N_j` below counts occupied field outputs of fiber size `j`.

| q | Mixed triples | N1 | N2 | N3 | Repeated-pair N3 | Coefficient rank | Augmented rank |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 2 | 6 | 4 | 1 | 0 | 0 | 2 | 3 |
| 8 | 288 | 178 | 40 | 10 | 9 | 15 | 16 |
| 32 | 16,896 | 10,504 | 2,176 | 680 | 225 | 63 | 64 |

Each row holds for every normalized `w` at that `q`. The ranks use the full
system in `2q` epsilon variables, including **all** unordered pairs of
colliding triples. In particular, a fiber of size three contributes all
three inequalities, not merely two equations against a chosen representative.
Every system is inconsistent.

### The other composition and the pure cross type were also included

Each pure branch is B3 by the Bose polynomial argument; its squared image is
also B3. Each pure branch has `binom(q+2,3)` distinct outputs. The only pure
collision type is between the two branches. Here are the additional counts:

| q | normalized w | 1+2 histogram `(N1,N2,N3)` | all-0 versus all-1 common outputs |
|---:|---|---|---:|
| 2 | `1` | `(6,0,0)` | 2 |
| 8 | `2,4,6` | `(198,42,2)` | 24 |
| 32 | `1` | `(10716,2340,500)` | 1367 |
| 32 | `6,20,22,25,29` | `(10728,2328,504)` | 1076 |
| 32 | `7,21,23,24,28` | `(10716,2340,500)` | 1076 |

The total number of unordered triples examined per representative is
`binom(2q+2,3)`: 20, 816, and 45,760, respectively. Across all 15
representatives, this is **505,828 multisets**. The mixed cubic reconstruction
was separately verified at **every nonzero field output**, including empty
fibers: **361,977 output checks** in total.

### A concrete q=8 three-fiber witness

Take `b^3=b+1` and `theta^3=theta+b`. The three mixed triples

\[
 (0,0;b^2),\qquad (b^2,b^2;0),\qquad
 (1,b^2+b+1;1)
\]

all have product

\[
 b\theta+(b^2+b+1)\theta^2.
\]

Here `(a,b;c)` denotes two branch-0 parameters and one branch-1 parameter,
not tags. The first two products are `(theta*(theta+b^2))^2`; the third is
`(theta+1)^3*(theta+b^2+b+1)`. All three triples have mod-3 tag 1, leaving
only two binary tag values for three multisets. The JSON also records an
explicit maximum fiber and a parity-triangle certificate for every audited
representative.

## 7. Reproduction and independent verification

Files, all under `Submission/`:

* `frobenius_twofiber_z6_audit.py`: independent-of-Sage field arithmetic,
  exhaustive multisets, all parity equations, Gaussian elimination,
  mixed-cubic reconstruction, trace-graph checks, and explicit certificates.
* `frobenius_twofiber_z6_audit.json`: complete finite audit results.
* `frobenius_twofiber_z6_verify_sage.py`: independent Sage verification using
  polynomial quotient fields and Sage matrix ranks, not the arithmetic or
  elimination code of the first script.
* `FrobeniusTwoFiberZ6.md`: this proof and audit note.

Run:

```sh
python3 Submission/frobenius_twofiber_z6_audit.py --all-outputs
sage -python Submission/frobenius_twofiber_z6_verify_sage.py
```

Both passed. Sage independently reproduced every composition histogram,
every mod-3-combined histogram, both matrix ranks, every stored maximum-fiber
example, and each three-equation inconsistency certificate for all 15
representatives. It also verified the trace-form ranks, orthogonality edge
and triangle counts, and all five cases in the two-fiber classification.
The general polynomial-reduction, affine-normalization, Vieta, and
exceptional-root identities were also checked symbolically over
characteristic two.

## Conclusion

The proposed Frobenius two-fiber family is ruled out **uniformly**, not by
finite failure or by an unproved monodromy assumption. Repeated summands
already force an impossible binary coloring when `q>2`; `q=2` is eliminated
by its pure/mixed parity triangle. Moreover, the mixed 2+1 fibers have a
positive, exactly determined cubic-order count of three-element fibers.

For odd `m`, `Z/6 x K^*` is cyclic of order `6(q^3-1)`, as proposed. A cyclic
CRT/discrete-log isomorphism preserves the collisions just proved, so it
cannot turn these sets into strong B3 sets. The formal ratio `8/6` is
therefore not attained by this construction.
