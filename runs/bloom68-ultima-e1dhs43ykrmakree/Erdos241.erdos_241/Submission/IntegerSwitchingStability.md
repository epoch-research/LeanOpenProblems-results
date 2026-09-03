# Integer character switching: a local obstruction for arbitrary lifts

## Status and precise scope

This note proves an **integer**, dense-partial-selection obstruction for the reflection model in `CharacterSwitching.md` and, more generally, for arbitrary one-per-parameter integer lifts of the switched points. A modular collision is **not** being treated as an integer collision.

The result is uniform in the odd prime power, the Bose parameter, the logarithm generator, the reflection translation, and the selected parameter subsets. In fact the multiplier may be **any nonsquare** of F_(q^3), not just the value of a monic irreducible quadratic.

For each fixed eta>0, every integer strong B3 set in the one-lift-per-selected-parameter model below with n>=eta q satisfies

    n^3 / N <= 1 + o_eta(1),                              (1)

where N is its actual integer span and the error is uniform over those choices. There is a sharper bound `27/32 + o_eta(1)` when all the selected lifts occupy a single interval of length at most `m=(q^3-1)/2`.

These are asymptotic obstruction/stability results, not a construction and not a resolution of Erdős 241. In particular:

* the dense hypothesis matters when converting an additive o(q) error to a cubic ratio;
* sparse selections n=o(q) are not excluded;
* each selected switched parameter is used with one integer representative; variants that reuse a parameter with several different representatives are not asserted to satisfy this bound;
* no existence assertion is made at the stability boundary n~q, N~q^3.

Arbitrary pointwise lifts of span between m and 2m **are included**. The proof uses the Weil bound for curves, including its standard rank-one tame-character-sum form. It is not a Lean formalization. `Spec.lean`, `Reductions.lean`, and `SignedSums.lean` are unchanged.

## 1. Model and the quantitative shape of the obstruction

Let f be a monic irreducible cubic over F=F_q, q odd, let theta be a root in K=F_(q^3), and put

    M=q^3-1,       m=M/2,       H=(K*)^2,
    z_t=theta-t,   epsilon(t)=chi_K(z_t)=chi_F(-f(t)).

Choose any nonsquare w in K*. There is a unique polynomial W of degree at most two such that w=W(theta). Write

    W(X)=lambda X^2+mu X+nu,       c=Res(f,W),       chi_F(c)=-1.

Define

    u_t=z_t        if epsilon(t)=+1,
    u_t=w/z_t      if epsilon(t)=-1.                       (2)

All u_t belong to H. Choose **any** generator h of H, an arbitrary parameter subset S, and **arbitrary integers** a_t satisfying `h^(a_t)=u_t`, one for each t in S. Form A={a_t:t in S} and assume A is strong B3, including repeated summands. There is no bound on the individual winding numbers in this definition. Let

    n=|A|,       N=max A-min A+1,       alpha=N/m.

The empty set is irrelevant here. Point coincidences cause only an O(1) issue: if u_a=u_b with opposite signs, then W=(X-a)(X-b). Removing the at most two F_q-roots of W makes (2) injective. We make this deletion in the proof; it changes n by at most two and never increases N.

### Integer-lift theorem

Uniformly in all the above data,

    n/q <= F(alpha)+o(1),                                 (3)

where

    F(alpha) = 3 alpha/4            for 0<=alpha<=1,
               1/2+alpha/4         for 1<=alpha<=2,
               1                  for alpha>=2.

The assertion is an asymptotic uniform additive bound, not an exact finite-q inequality. Together with n>=eta q it implies (1).

### The original integer reflection model is included

A useful special case is to choose an interval J_sigma of m consecutive integers for each branch and use its unique representatives there. These are the **two-window lifts**, but the theorem does not require this restriction.

Let g be any generator of K*, write `z_t=g^(b_t)` with 0<=b_t<M, and set

    U={b_t/2 : b_t even},
    V={(M-1-b_t)/2 : b_t odd}.

For **every** integer translation T,

    U union (V+T)

is (2) with

    h=g^2,        w=g^(2T-1),
    J_+=[0,m-1],  J_-=[T,T+m-1].                          (4)

Indeed `g^(2((M-1-b_t)/2+T))=g^(2T-1)/z_t`. Thus (3) applies to arbitrary partial selections from U and V, not merely to the full q-point set or to the finitely audited bases.

A common cyclic translation of the original Bose logarithms is harmless too. In field notation replace z_t by d z_t. If d is square, a common square factor reduces the switched points to (2) with multiplier w/d^2. If d is nonsquare, common inversion followed by multiplication by the square w/d reduces them to (2) with multiplier w/d^2 and interchanges the branch labels. Common integer translation/reflection and length-m windows preserve the hypotheses and the span. Thus scalar translates of a Bose affine line are included as well.

### Shorter integer arcs and the numerical example in the question

Any lift of a selected subset into an interval of length N<=m is included. In particular, a short arc is not required to be cyclic B3.

For N/m -> alpha<=1 the bound is

    n <= (3 alpha/4+o(1))q.                               (5)

At span `0.4q^3`, alpha->0.8, so the bound is `n<=(0.6+o(1))q`. Retaining `0.74q` at that span is therefore excluded in this model, despite the fact that the old, unlocalized cyclic density bound did not exclude it.

## 2. A quartic pencil for every nonsquare multiplier

The monic-quadratic hypothesis in the earlier density note is not appropriate for arbitrary reflection translations. The replacement pencil is

    P_(a,k)(X)
       = W(X)(X-a)^2 + ((1-lambda)X+k) f(X).               (6)

It is monic of degree four, and

    P_(a,k)(theta)=w(theta-a)^2.

A good fiber at a has four distinct F_q-roots, none equal to a, with three roots of sign epsilon(a) and one of the opposite sign. Its root signs have product -1, since

    product_(P(t)=0) (-f(t)) = Res(P,f)=c f(a)^2.           (7)

If a is positive, write the roots as positive p1,p2,p3 and negative b. Then

    u_p1 u_p2 u_p3 = u_a^2 u_b.                           (8)

If a is negative, the identical formula holds with the majority and minority signs reversed. Outside the at most two discarded parameters, these are nontrivial collisions on five distinct parameters, with the center a used twice.

Let M(a,t) be 1 when t belongs to a good fiber at a, and 0 otherwise. For a fixed pair (a,t), its fiber is unique:

    k(a,t)=-W(t)(t-a)^2/f(t)-(1-lambda)t.                  (9)

As before, every fiber contributes four incidences. In particular, this is a zero-one matrix; no multiplicity is hidden in the definition.

## 3. The generalized residual curve is uniformly genus two

Fix t with W(t)!=0 and put

    A_t(X)=[f(t)W(X)-W(t)f(X)]/(X-t),

    C_t(a,X)=[f(t)W(X)(X-a)^2-W(t)f(X)(t-a)^2]/(X-t)
                 +(1-lambda) f(t)f(X),                   (10)

    D_t(X)=W(t)W(X)+(lambda-1) A_t(X).                    (11)

The polynomial C_t is cubic in X, with leading coefficient f(t), and its roots are the other three roots of the fiber (9). Regarding it as a quadratic in a gives the exact identity

    disc_a C_t(a,X) = 4 f(t) f(X) D_t(X).                 (12)

The leading coefficient of D_t in X is W(t). Also

    coefficient_a C_t = -2(t A_t+f(t)W),
    gcd(A_t,W)=1.

Thus C_t is primitive as a polynomial in a over kbar[X]. Whenever D_t has two distinct roots, disjoint from those of f, its normalization is the connected genus-two curve

    y^2=f(X)D_t(X).                                      (13)

There are only O(1) excluded values of t, uniformly for **every** allowed W. Here is the nondegeneracy check that prevents an exceptional multiplier from escaping the argument.

For a root beta of f, write `g_beta=f/(X-beta)`. Then

    D_t(beta)=W(beta)[W(t)-(lambda-1)g_beta(t)].            (14)

The bracket is monic quadratic, so common roots of f and D_t occur for at most six t.

Suppose `disc_X D_t` were identically zero as a polynomial in t. Evaluating at the three roots beta of f forces the quadratic polynomial

    (lambda-1)(lambda+3) beta^2
      +2(lambda-1)((lambda+1)c2-mu) beta
      +(mu-(lambda-1)c2)^2-4nu+4(lambda-1)c1             (15)

to vanish identically, where `f=X^3+c2 X^2+c1 X+c0`. There are two possibilities.

* lambda=1: W has discriminant zero and is a monic square, so W(theta) is square, contrary to the hypothesis.
* lambda=-3: necessarily `mu=-2c2`, `nu=c2^2-4c1`. Direct substitution gives

      disc_X D_t
       =-16 f(t)[-9c0+4c1c2-c2^3+(3c1-c2^2)t].          (16)

  Outside characteristic three, identically zero would make
  `f=(X+c2/3)^3`. In characteristic three it forces c2=0 and W=-c1. If -c1 were nonsquare, the F_3-linear map `x -> x^3+c1 x` on F_q would be bijective, so f would have an F_q-root. Irreducibility therefore makes -c1 square, again making W(theta) square.

Both possibilities are impossible. Since `deg_t disc_X D_t<=4`, only O(1) t must be excluded.

### A short argument that the cubic group is S3, not C3

The degree-three map from (13) to the a-line is separable. In characteristic three an inseparable extension of prime degree three of kbar(a) would be rational, unlike (13).

Let iota be the hyperelliptic involution. The quadratic formula in a gives

    a+iota(a)=2t+2f(t)W(X)/A_t(X).                        (17)

This is a **nonconstant rational function of X of degree at most two**. If the cubic cover were cyclic, its order-three automorphism would commute with the central hyperelliptic involution. It would fix both a and iota(a), hence (17). But an order-three automorphism of kbar(X) cannot fix a nonconstant function of degree at most two. If it acted trivially on X, it would instead belong to the degree-two hyperelliptic group, also impossible.

Therefore the cubic splitting group is S3. This argument works uniformly in characteristic three as well.

## 4. Signed covers, distinct columns, and the unweighted mixing input

Write `Delta(t,a)=disc_X C_t(a,X)`, using the universal cubic discriminant. Its bidegrees are at most (12,8). For each root beta of f,

    Delta(beta,a)=W(beta)^4 disc(g_beta)(a-beta)^8.         (18)

Consequently the degree in a is eight outside O(1) t.

The genus-two double cover obtained by adjoining `sqrt(-f(X))` to (13) is connected and unramified: f and D_t are squarefree and coprime, and neither is a square in kbar(X). If x1,x2,x3 are the residual roots, (7) gives

    product_i (-f(x_i)) = [c/(-f(t))] f(a)^2.              (19)

Exactly as in the signed-cover argument of `QuadraticSwitchingDensity.md`, the geometric sign-change kernel is

    V={(e1,e2,e3) in F_2^3 : e1+e2+e3=0}.

It is all of V, not zero: otherwise the connected unramified double cover just described would equal the S3 splitting field over a root field, whereas that double cover is ramified. For the latter assertion, inertia with nontrivial image in S3/A3 contains a transposition; at a conjugate point it intersects the chosen root stabilizer nontrivially. Thus the signed geometric group is

    V semidirect S3 = S4,                                (20)

with unique quadratic subfield generated by sqrt(Delta_t).

There is a moving odd factor of Delta over kbar[t,a]. Indeed, if every odd horizontal factor were independent of t, unique factorization would give `Delta=V(t)B(a)E(t,a)^2`, with B squarefree. Formula (18) forces B constant. This contradicts the nonsquare cubic discriminant established in §3 for generic t.

Bounded-degree specialization now gives O(1) exceptional columns. For each remaining t there are at most **96** remaining s with `Delta_s/Delta_t` square in kbar(a): a moving factor has a-degree at most eight and t-degree at most twelve, and one of its specialized roots must be one of the at most eight odd roots of Delta_t. Inseparable horizontal factors cause no difficulty: their inseparable multiplicities are odd, since the characteristic is odd.

For all other pairs, the two S4 covers are geometrically linearly disjoint. Every nontrivial quotient of S4 has a quadratic quotient, so any nontrivial intersection would identify their unique quadratic subfields. The center-character cover `b^2=-f(a)` is independent too: it is ramified at infinity, whereas the discriminant classes, of degree eight, and their products are not.

The covering degrees, genera, branch counts, and numbers of omitted values are absolutely bounded. Over the degree-one Frobenius coset the three residual signs have product `-epsilon(t)`. Conditional on full splitting, the four possible sign vectors of that parity are equiprobable. Thus the good-fiber probabilities are

    p_(sigma,tau)=1/8   if sigma=tau,
                    1/24  if sigma!=tau.                 (21)

The center sign is independently conditioned, not silently ignored. The Weil bound on the one- and two-column signed covers gives the same spectral estimate as in the earlier density note:

    ||M_(sigma,tau)-p_(sigma,tau)||_(2->2)=O(q^(3/4)).      (22)

The at most 96 exceptional partners per column contribute O(q) to each Gram-matrix row; the other entries are O(sqrt(q)). The matrix definition can omit the O(1) bad incidences per column (repeated roots, center a among the roots, etc.) without changing this estimate.

For reference, a center root occurs only when a=t or, for W(t)!=0, `a=t+(1-lambda)f(t)/W(t)`. This is indeed O(1) per column, not an unbounded exceptional set.

## 5. The needed localization lemma — keeping the product relation

Unweighted mixing alone would not prove an integer obstruction. We now retain the logarithmic coordinates of **all four roots**.

Put `x_t=log_h(u_t)/m` in the circle R/Z. For a real continuous function phi on the circle, set

    M_phi(a,t)=M(a,t) product_(r a root of its good fiber) phi(x_r).

Convolution below is Haar probability convolution on the circle, and `tilde(phi)(x)=phi(-x)`. Define

    K_same(x,y)=phi(y)(phi*phi*tilde(phi))(2x-y),
    K_opp (x,y)=phi(y)(phi*phi*phi)(2x+y).                 (23)

### Localized mixing lemma

For arbitrary parameter subsets `A subset E_sigma`, `T subset E_tau`,

    sum_(a in A,t in T) M_phi(a,t)
      =p_(sigma,tau) sum_(a in A,t in T) K_(sigma,tau)(x_a,x_t)
          +o_phi(q^2),                                  (24)

where K is K_same or K_opp as appropriate. The error is uniform in all the field data, generators, and subsets. For fixed trigonometric-polynomial phi it is `O_phi(q^(7/4))`.

The convolution kernels are important. The hidden logarithms are **not** independent uniform variables: their exact product relation is retained. When t has the center's sign, the other roots satisfy

    x_1+x_2-x_3 = 2x_a-x_t  in R/Z;

when t has the opposite sign, they satisfy

    x_1+x_2+x_3 = 2x_a+x_t  in R/Z.

These are precisely the two kernels in (23).

### Proof of (24): Fourier modes and a divisor test

Choose a generator g of K* with g^2=h, and extend the primitive character of H to the primitive character of K* associated with g. First take phi to have a fixed finite Fourier expansion.

Label the residual roots by their prescribed signs, averaging over the two or six compatible orderings. A Fourier term of the three hidden factors has character exponents

    e_i=epsilon(x_i) k_i

on `theta-x_i`, up to a constant power of w. If all e_i are equal, the exact identity

    product_i (theta-x_i)=w(theta-a)^2/(theta-t)           (25)

reduces the term to a row phase times a column phase. Summing precisely these terms gives (23). Subtracting their probability (21) is controlled by (22).

For all the other terms we need a uniform character-sum bound, not an unjustified assertion of log independence. The following local divisor test supplies it.

After O(1) additional columns are omitted, the ordinary and signed covers are unramified at every a=beta with f(beta)=0. There, one residual root equals beta, its function `beta-x_i` has zero of order **two**, and the other two residual roots differ from all roots of f. Each choice of the index i occurs on the Galois cover.

To see that this omission is uniform, at a=beta the quartic factors as

    (X-beta)[H_beta(X)+k g_beta(X)],
    H_beta=W(X)(X-beta)+(1-lambda)X g_beta.

The rational function H_beta/g_beta has two simple poles at the other roots of f; it is therefore separable. Its generic cubic fiber is separable and avoids beta. Thus `Delta(t,beta)` is a nonzero polynomial of bounded degree. The order two then follows directly from `C_t(a,beta)=f(t)W(beta)(beta-a)^2/(beta-t)`.

For two columns t,s with different discriminant classes, their signed covers are independent. Over a=beta **every pair** of root indices i,j occurs. In the correlation of two Fourier terms the character has local exponent

    2(e_i-e'_j),

or twice this after adjoining the ramified center-character cover. A non-main term has nonconstant e_i, so for some i,j this is nonzero. The Fourier indices are fixed, while q^3-1 tends to infinity; hence this exponent is nonzero modulo q^3-1 for all sufficiently large q. Frobenius conjugation of beta multiplies it by a unit q^j and does not change this conclusion.

More explicitly, use the rank-one character sheaf on the torus `Res_(K/F) G_m` whose trace on K* is the chosen multiplicative character. This is the sheaf associated with that character of the kernel of the Lang isogeny. Over kbar, after cyclically indexing the torus coordinates z0,z1,z2, the Lang equations can be written

    z0=y1^q/y0,   z1=y2^q/y1,   z2=y0^q/y2,
    y0^(q^3-1)=z0 z1^q z2^(q^2).

Thus its three geometric Kummer exponents are a common unit times `(1,q,q^2)` modulo q^3-1. On the root cover the coordinates are `beta_j-x_i`. This explicitly justifies the local exponent test, including arbitrary generators.

Prescribed signs can be imposed by the bounded-degree equations `d_i y_i^2=-f(x_i)`, with d_i a chosen square or nonsquare, and the analogous center equation. Ordered, distinct residual roots and these square roots give bounded-degree curve components; dividing their point counts by the fixed ordering and square-root multiplicities gives the matrix correlations. The preceding S4-independence argument identifies the geometric composita of these components. Thus the character sums in the Gram calculation are actual sums on these curves, not an assumed mixing principle for unrelated characters.

The displayed local monodromy proves that the pulled-back rank-one sheaf in each non-main correlation is geometrically nontrivial. Its ramification is tame, and the number of its singularities and the genus of the underlying **bounded-degree signed cover** are absolutely bounded. The standard character-isotypic Weil bound is consequently O_phi(sqrt(q)), independently of the order of the character and of the generator: for a geometrically nontrivial finite-order tame rank-one sheaf on a genus-g curve with at most r punctures, the relevant first-cohomology dimension is bounded in terms of g,r, and its eigenvalues have absolute value at most sqrt(q).

This step does **not** assert bounded genus for a Kummer cover of degree q^3-1; that genus need not be bounded. The integers q and q^2 in the Lang formula can raise divisor multiplicities but not the number of singular points or the tame conductor of a rank-one character. It is this conductor bound that is used.

Thus the Gram matrix of each non-main Fourier matrix has O(sqrt(q)) entries except for O(1) partners per column, where O(q) suffices. Its operator norm is O_phi(q^(3/4)), proving (24) for finite Fourier expansions. Uniform approximation proves it for continuous phi.

Interval indicators are allowed as well, by approximation from a boundary strip. The total change in all incidence sums is at most a constant times `q` times the number of parameters whose log lies in that strip. Uniform single-point equidistribution (next section) makes this `O(|strip|q^2)+o(q^2)`. This also works uniformly for translated intervals: translation changes only the unit phases of their Fourier coefficients. Formula (23) is covariant under a common translation of every logarithmic coordinate. Consequently one may translate the actual integer containing interval when taking the compactness limits below without changing the estimates or the collision identities.

## 6. From a short arc to actual integer equality

The same rank-one Weil bound on the a-line gives, uniformly in generators, multipliers, signs, and circle intervals I,

    #{t in E_sigma : x_t in I}
       = (q/2)|I|+O(sqrt(q) log q).                       (26)

For example, insert `(1+sigma chi_F(-f(t)))/2` and expand the interval in characters. Every nonconstant mode is a nontrivial tame character sum with at most the three roots of f and infinity as singularities. This explains both the uniformity and the absence of a generator exception.

Consider a sequence of models with q tending to infinity and bounded N/m; larger normalized spans are harmless for (3), since n<=q. Translate the actual containing interval to start at zero, normalize integer coordinates by m, and take weak limits of the selected-point measures, normalized by q. On every bounded real interval these limits have densities

    0<=s_sigma(x)<=1/2.                                  (27)

Indeed, in any interval of length less than one, actual selected lifts are bounded by the number of **potential** representatives supplied by (26). There is also a global capacity constraint. Since a parameter is selected at most once, projection of its selected measure to R/Z is dominated by the full branch measure. Thus, for almost every r in [0,1),

    sum_(j in Z) s_sigma(r+j) <= 1/2.                    (27a)

Now take **any** real interval I of length delta<1/3. For each parameter whose residue lies in I modulo one, consider its unique *hypothetical local representative* in I. Define S_I to consist of the parameters whose **actually chosen** lift lies in I, and define

    D_I = {parameters with a hypothetical representative in I} \ S_I.

Crucially, D_I includes a parameter selected globally but lifted into a different period. It is a local absence set, not the complement of the global selection. No fixed branch windows or bound on the chosen winding numbers are being assumed.

If a good fiber's center and all four roots belong to S_I, their actual lifts are all in I and (8) is an **integer** equality: both triple sums lie in an interval of length 3 delta m<m, so their congruence modulo m cannot have nonzero winding. Omitting the O(1) coincidence parameters, integer B3 therefore gives the exact covering inequality

    (1/4) sum_(a in S_I,t in F) M_I(a,t)
         <= sum_(a in S_I,t in D_I) M_I(a,t),              (28)

where M_I uses phi=1_I in §5. Each fiber is tested with its unique hypothetical representatives in I, whose winding is zero. If a globally chosen representative is elsewhere, its parameter is counted in D_I. Thus (28) never treats a nonzero-winding collision among the chosen representatives as an actual integer equality: it only uses an actual equality when all five parameters are locally retained.

Apply (24), divide by q^2, and pass to the weak limits. The two root kernels have equal integrals in y for every center x:

    integral_I (1_I*1_I*tilde(1_I))(2x-y) dy
       = integral_I (1_I*1_I*1_I)(2x+y) dy.               (29)

Here the convolutions can be read on the real line: with all five coordinates in I and delta<1/3 there is no other winding. Their common integral over x in I is positive; in fact it is `11 delta^4/24`.

At a common Lebesgue point x of the two densities, shrink I to x. Write `c_sigma=s_sigma(x)`. The kernels are O(delta^2), so replacing either density by its Lebesgue-point value causes o(delta^4) error. Equations (21), (28), and (29), after cancelling the positive common integral, give

    (c_++c_-)/48
       <= [2(c_++c_-)-3(c_+^2+c_-^2)-2c_+c_-]/24.

Equivalently, for almost every real x,

    4(s_++s_-)^2+2(s_+-s_-)^2 <= 3(s_++s_-),             (30)
    s_++s_- <= 3/4.                                      (31)

This is the local, deletion-robust obstruction. The subsets in (24) were arbitrary, so no regularity or randomness of the selection is assumed. Passing to limiting density profiles does not discard microscopic adversarial selection.

Equation (30) is stronger than just (31); for example retaining the full local density 1/2 of one branch leaves at most 1/6 of the other. For two-window lifts, a branch density vanishes outside its own window, so the total density outside overlap is at most 1/2. But the local proof and (30) do not require the two-window restriction.

## 7. Periodic capacity optimizes the span for arbitrary lifts

Normalize the limiting containing interval to [0,alpha] and put

    d(x)=s_+(x)+s_-(x),       rho=lim n/q=integral d(x) dx.

The two constraints proved above are

    d(x)<=3/4,
    sum_(j in Z) d(r+j)<=1  for almost every r in [0,1).  (32)

The second is the one-copy-per-parameter capacity, not an assumption that all cyclic collisions are forbidden.

For alpha<=1, the first constraint gives rho<=3 alpha/4. For 1<=alpha<=2, the residues r in [0,alpha-1] have two possible positions in the containing interval, while the others have only one. Hence

    rho = integral_0^(alpha-1) [d(r)+d(r+1)] dr
              + integral_(alpha-1)^1 d(r) dr
         <= (alpha-1)+(3/4)(2-alpha)
          = 1/2+alpha/4.

For alpha>=2, the projected capacity gives rho<=1. These are exactly (3), now for **arbitrary** integer lifts, not just lifts into two prescribed windows.

A subsequence/compactness argument makes the o(1) uniform. A failure by a fixed positive amount can only occur with alpha<=2, since n<=q. After translating the actual containing interval to start at zero, all selected measures have bounded support. Equations (26), (24), and the one-copy projection bound give (27), (30), and (32) for a weakly convergent subsequence, contradicting the displayed optimization. If alpha tends to zero, (26) directly makes n/q tend to zero, so that case cannot violate (3).

For dense selections alpha is bounded away from zero by (26). Since `q^3/m -> 2`, (3) gives, along a sequence with N/m -> alpha,

    limsup n^3/N <=
      27 alpha^2/32                if 0<alpha<=1,
      (alpha+2)^3/(32 alpha)       if 1<=alpha<=2,
      2/alpha                     if alpha>=2.           (33)

The middle expression increases from 27/32 to 1; its logarithmic derivative is `(2alpha-2)/(alpha(alpha+2))`. This proves (1), including actual interval compression and unrestricted choices of winding numbers. When N>=2m the direct bound `n^3/N<=q^3/(2m)=1+O(q^(-3))` also suffices.

### Stability

If a dense sequence of arbitrary lifts has `n^3/N -> 1`, necessarily

    n/q -> 1,        N/m -> 2.

For any limiting profile normalized to [0,2], projected capacity is saturated:

    d(r)+d(r+1)=1,       1/4<=d(r),d(r+1)<=3/4

for almost every r in [0,1]. This is a necessary condition only, not a construction at the boundary.

In the original **two-window reflection** notation there is a stronger geometric consequence:

    |T|/m -> 1.                                          (34)

Full asymptotic retention uses almost all of each branch. By (26), each branch therefore has density 1/2 throughout its length-one window. A positive-length overlap would give total density one, contradicting (31). A positive gap would force containing span greater than two. Thus, after a common translation, the two windows asymptotically abut. Again, this does not certify B3 at the boundary.

## 8. Verification and limitations

`integer_switching_stability_audit.py` is an algebraic and winding audit, not a SAT search. Its checks include:

* the generalized pencil, residual cubic, and discriminant identity (12);
* the exceptional-multiplier calculation (15)-(16), including characteristic three;
* moving odd discriminant factors and unramified root-of-f specializations in selected small fields;
* good-fiber character patterns and their repeated-triple identities for arbitrary nonsquare W, including constant, linear, nonmonic quadratic, and split quadratic W;
* the exact integer winding of these identities and the short-arc no-wrap implication, for several generators and branch translations;
* the real convolution integral in (29), the local density algebra, and the periodic-capacity span envelope (33);
* globally selected parameters moved to another period, which must count as locally absent rather than globally deleted;
* protected-file hashes.

The completed audit checked 3,784 field/multiplier pairs: all irreducible f and all nonsquare w at q=3,5, and all nonsquare w for the specified f at q=7,9,11. These include 100 constant, 536 linear, 536 monic quadratic, and 2,612 nonmonic quadratic multipliers. It verified 808 good fibers / 3,232 incidences and 45 deeper discriminant-family cases. The characteristic-three corner was separately checked on all 2,420 irreducible depressed cubics at q=3,9,27,81. The winding audit checked 294 identities in 90 generator/translation models, including nonzero windings and 15 short-arc/window checks. It also checked the periodic-capacity optimization on 385 exact rational mesh cases and the local-absence distinction after moving a globally retained root by one period. All protected hashes matched.

The audit also retained eight explicit integer B3 examples that are **not** cyclic B3; all 35 repeated triple sums were checked in each. For instance, in a q=11 model,

    A={96,397,403,607,664},       m=665,
    403+664+397 = 1464,          96+96+607 = 799.

The two sums differ by exactly m and are not equal as integers. This finite example is not an excess construction; it checks that the winding distinction is real and is respected by the argument.

For the local-absence check, at q=9 and m=364 the five hypothetical representatives `{327,351,381,424,443}` lie in a short interval and contain a good-fiber equality. Moving only 443 to 807 leaves all five parameters globally selected but gives an integer B3 set (all 35 repeated triples checked). The moved parameter must belong to D_I for I=[327,443]. This directly audits the distinction used to pass from two-window lifts to arbitrary lifts.

The analytic part is proved in §§4-6, using the stated Weil input; finite statistics are not a substitute for (24). The crucial additional ingredient beyond `QuadraticSwitchingDensity.md` is the non-main Fourier-mode divisor test at a root of f. Without that test, localization, and the short-arc condition in (28), a cyclic density bound would still leave the integer question open.

The general integer strong B3 conjecture remains unresolved here. The obstruction is specific to dense selections of these switched Bose points, with one representative per selected parameter. It does not exclude sparse selections n=o(q), unrelated integer constructions, or variants that reuse a switched parameter with several different integer representatives.
