# A uniform density obstruction for quadratic character switching

## Status and scope

The cyclic retention proposal in `CharacterSwitching.md` has the following **uniform obstruction**:

> There is an absolute constant C such that, for every odd prime power q and every admissible irreducible cubic f and irreducible quadratic W, a strong cyclic B3 subset of the switched points has at most
>
>     3q/4 + C q^(3/4)
>
> parameters.

In particular, changing W, including choosing W exceptionally as q varies, cannot produce cyclic B3 retention greater than `2^(-1/3) q` along an unbounded sequence. At the proposed ambient length `m=(q^3-1)/2`, the resulting upper bound on the cubic ratio is

    limsup |S|^3/m <= 27/32 < 1.

The proof is specific to the switched construction. It does **not** apply the earlier fixed-quotient bound. It uses repeated-summand collisions of type `d=1, Q=(X-a)^2`; the other collision types are not needed.

This is a mathematical proof using the standard Weil bound / effective Chebotarev theorem for covers of curves over finite fields, not a Lean formalization. No optimality claim is made for the constant 3/4. This is not a resolution of the general strong B3 problem. In particular, it does not exclude integer lifts that avoid actual equalities despite cyclic collisions, or an additional compression into a substantially shorter interval. `Spec.lean` and `Reductions.lean` are unchanged.

## 1. Notation and the theorem

Let F=F_q, q odd, and let f,W be monic irreducible polynomials over F of degrees 3 and 2. Write

    c = Res(f,W),             chi_F(c) = -1,
    epsilon(t) = chi_F(-f(t)),
    E_+ = {t: epsilon(t)=1},  E_- = {t: epsilon(t)=-1}.

Choose a root theta of f in K=F_(q^3). The condition on c is exactly the condition that W(theta) is nonsquare in K. The usual norm identity identifies epsilon(t) with the character used in the switching construction. Put

    u_t = theta-t                    if epsilon(t)=1,
    u_t = W(theta)/(theta-t)         if epsilon(t)=-1.

These points are squares in K and are distinct. Within either branch injectivity is immediate. An equality across branches would give `W(theta)=(theta-a)(theta-b)`, hence `W=(X-a)(X-b)` by the degree-three minimal polynomial, contradicting irreducibility of W.

For a parameter subset S, put `n_+=|S intersect E_+|`, `n_-=|S intersect E_-|`, and `n=n_++n_-`.

### Theorem

If `{u_t:t in S}` is B3 in the square subgroup of F_(q^3)^*, with repeated summands allowed, then

    4n^2 + 2(n_+-n_-)^2 <= 3qn + O(q^(7/4)),                 (1)
    n <= 3q/4 + O(q^(3/4)).                                 (2)

All implied constants are absolute, independent of q, its characteristic, f, W, and S.

The proof below actually needs only avoidance of the square-Q quartic collisions defined in the next section.

## 2. Repeated-root fibers and an exact covering inequality

For a in F and k in F^*, consider the monic quartic

    P_(a,k)(X) = W(X)(X-a)^2 + k f(X).                       (3)

A **good fiber at a** is a value k for which P has four distinct roots in F and the sum of their epsilon values is `2 epsilon(a)`. Equivalently, three of the four roots have the character of a, and the fourth has the opposite character.

There are no roots equal to a, since `P(a)=k f(a) != 0`. Moreover,

    product_(P(t)=0) (-f(t)) = Res(P,f) = c f(a)^2.           (4)

Thus every completely split quartic with four distinct roots has an odd number of negative-character roots. The only possible sign patterns are 3+1 and 1+3. Requiring its majority character to be epsilon(a) is a genuine additional condition.

Each good fiber is a forbidden configuration on **five distinct parameters**, with a used twice in one triple. If a is positive and the roots are positive p1,p2,p3 and negative b, evaluating (3) at theta gives

    u_p1 u_p2 u_p3 = u_a^2 u_b.

If a is negative, with negative roots b1,b2,b3 and positive p, it gives

    u_b1 u_b2 u_b3 = u_a^2 u_p.

These are precisely instances of the supplied collision criterion with `d=1` and `Q=(X-a)^2`.

Define a zero-one incidence matrix M, with row a and column t, by

    M(a,t)=1  iff  t is one of the four roots of a good fiber at a.

For a != t the fiber is uniquely determined:

    k(a,t) = -W(t)(t-a)^2/f(t).                             (5)

Hence a pair (a,t) cannot be counted twice. Each good fiber contributes exactly four entries to its row.

Let D=F\S. If S avoids the displayed collisions, every good fiber whose center a belongs to S must have a root in D. Consequently the following is an **exact** necessary inequality:

    (1/4) sum_(a in S, t in F) M(a,t)
        <= sum_(a in S, t in D) M(a,t).                     (6)

The main task is to estimate both sides for arbitrary S. Pointwise regularity or full-set failure alone would not suffice.

## 3. The uniform incidence-mixing statement

For sigma,tau in {+1,-1}, put

    p_(sigma,tau) = 1/8       if sigma=tau,
                   1/24      if sigma!=tau.

### Mixing lemma

For arbitrary subsets `A subset E_sigma` and `T subset E_tau`,

    sum_(a in A,t in T) M(a,t)
       = p_(sigma,tau) |A| |T| + O(q^(7/4)).                (7)

The error is uniform over all the data and all the subsets. This lemma, not an assumption of randomness of S, is what makes the density conclusion possible.

Sections 4-7 prove it, including the exceptional-parameter analysis.

## 4. A residual cubic on a genus-two curve

Fix t in F. The polynomial

    C_t(a,X) = [ f(t)W(X)(X-a)^2
                 - W(t)f(X)(t-a)^2 ]/(X-t)                 (8)

is cubic in X, with leading coefficient f(t), and quadratic in a. Its roots, together with t, are the roots of (3) with k from (5).

Over an algebraic closure kbar of F, the residual curve `C_t(a,x)=0` is birational to

    y^2 = f(t) W(x)/(W(t) f(x)),
    y = (t-a)/(x-a),       a=(yx-t)/(y-1).                   (9)

The five roots of fW and infinity are the six branch points of the hyperelliptic map to x. This is a connected smooth curve of genus two after normalization. The discarded factor x=t in the unreduced equation is the component collapsed to `(x,y)=(t,1)`; the residual cubic in (8) is irreducible over kbar(a).

Its degree-three map to the a-line is separable. The only possible issue is characteristic three; a purely inseparable degree-three extension of kbar(a) is rational, whereas (9) has genus two.

Write

    Delta_t(a) = disc_X C_t(a,X).

Whenever Delta_t is not a square in kbar(a), the geometric splitting group of the cubic is S3.

Now adjoin to (9) a square root of `-f(x)`. This is a connected, unramified double cover:

* zeros of f(x) and its pole at infinity have even valuations on (9);
* it is nontrivial because the quadratic extensions `kbar(x,sqrt(fW))` and `kbar(x,sqrt(-f))` differ: W is not a square in kbar(x).

Let x1,x2,x3 be the residual cubic roots. From (4),

    product_(i=1)^3 (-f(x_i)) = [c/(-f(t))] f(a)^2.          (10)

Consider the splitting field after adjoining all three square roots `sqrt(-f(x_i))`. Over kbar(a), its sign-change kernel is an S3-stable subgroup of

    V = {(e1,e2,e3) in (F_2)^3 : e1+e2+e3=0}.

The two-dimensional S3-module V has no nonzero proper invariant subgroup. The kernel is therefore either trivial or all of V.

It cannot be trivial. Otherwise the connected unramified double cover of (9) would be the S3 splitting field of the cubic: the latter has degree two over the field of a single root. But that double cover is ramified. Indeed, the S3 cover has some inertia with nontrivial image in S3/A3, since P1 over an algebraically closed field has no nontrivial connected unramified double cover. Such inertia contains a transposition; at a suitable conjugate point it intersects the chosen root stabilizer in an involution, ramifying the degree-two map. This contradiction also applies in characteristic three, without assuming tame cubic ramification.

The geometric signed group is thus

    V semidirect S3 = S4.                                  (11)

Its unique quadratic subfield is the cubic discriminant field `kbar(a,sqrt(Delta_t(a)))`.

### The sign probabilities

Equation (10) specifies the arithmetic constant-field coset exactly. For degree-one Frobenius elements the product of the three signs is

    chi_F(c/(-f(t))) = -epsilon(t).

The geometric group has 24 elements. In the degree-one Frobenius coset, four have trivial permutation on the three cubic roots, one for each sign vector of the prescribed parity. If the desired majority sigma equals epsilon(t), three of those four sign vectors work. If the two signs differ, exactly one works. The probabilities are therefore respectively `3/24` and `1/24`, as in (7).

One must still separate these signed covers as t varies, and separate them from the character of a. This is addressed next; without it, these probabilities would not justify arbitrary-subset mixing.

## 5. No exceptional W can make the discriminant family constant

Treat t,a as indeterminates and let

    Delta(t,a) = disc_X([f(t)W(X)(X-a)^2
                         - W(t)f(X)(t-a)^2]/(X-t)).         (12)

The bracketed quotient is a Bezoutian: it has degree at most three in both X and t, and degree at most two in a. Thus

    deg_t Delta <= 12,        deg_a Delta <= 8.             (13)

Here and below the discriminant is the **universal cubic discriminant polynomial**, including after specialization where the X-degree drops.

There are two useful exact specializations over kbar.

* If f(alpha)=0 and `g_alpha(X)=f(X)/(X-alpha)`, then

      Delta(alpha,a)
        = W(alpha)^4 disc(g_alpha) (a-alpha)^8.             (14)

  The scalar is nonzero. In particular, the a^8 coefficient of Delta is not identically zero as a function of t.

* Write the distinct roots of W as beta,beta'. Then W(t) divides Delta(t,a), and

      [Delta(t,a)/W(t)]_(t=beta)
        = 4 f(beta)^3 (a-beta)(a-beta')^3 f(a).              (15)

  This is a nonzero, nonsquare polynomial in a. Formula (15) follows either by differentiating the cubic discriminant or by the first-order splitting of the double root a in

      C_beta(a,X)=f(beta)(X-beta')(X-a)^2.

  In particular, the order of the vertical factor t-beta in Delta is exactly one.

These formulas are valid in every odd characteristic, including three.

### Moving odd factor lemma

Delta has an irreducible factor H(t,a) over kbar with all three properties:

    deg_t H > 0,       deg_a H > 0,       multiplicity of H odd.    (16)

To prove this, suppose all horizontal odd factors were independent of t. Unique factorization would give

    Delta(t,a) = V(t) B(a) E(t,a)^2,

where B is squarefree. Specializing at any root alpha of f in (14) forces B to be constant: a nonconstant squarefree B cannot occur in a polynomial all of whose root multiplicities are even. Formula (15) then contradicts the resulting assertion that, after removing the single vertical zero at beta, the specialization is a scalar times a square. This proves (16).

### Uniform control of specializations and repeated square classes

There is a set of O(1) exceptional t, with an absolute bound, outside which:

1. Delta_t has degree eight and is nonsquare in kbar(a);
2. odd horizontal factors retain odd root multiplicities, and distinct factors do not acquire common roots;
3. H(t,a) has positive a-degree, with its roots among the odd-multiplicity roots of Delta_t.

For clarity, this is just bounded-degree specialization, not an additional genericity hypothesis on f,W. Factor Delta in kbar[t,a], discard zeros of vertical factors and leading coefficients, and discard zeros of the nonzero discriminants and pairwise resultants of its horizontal factors. For an inseparable horizontal factor in characteristic p, write it as `G(t,a^(p^e))` with G separable in its second variable, and use the discriminant of G. Since p is odd, this inseparable multiplicity is odd and does not change square-class parity. The bounds (13) give an absolute bound for the number discarded.

Moreover, for each nonexceptional t there are at most **96** nonexceptional s with

    Delta_s/Delta_t a square in kbar(a).                    (17)

Indeed, Delta_t has at most eight odd roots. If (17) holds, every root of H(s,a) is among them. For any one such root z, the polynomial H(s,z) in s is nonzero and has degree at most 12. It cannot vanish identically, since that would make a-z divide the irreducible moving factor H. Taking the union over the at most eight choices of z proves the bound 8*12.

Thus the exceptional objects are only O(1) parameter values and O(q) pairs of parameters. There is **no exceptional admissible quadratic W** excluded from this analysis.

## 6. Independence of covers and the necessary character conditioning

Let t,s be nonexceptional with different geometric discriminant square classes.

The two signed S4 extensions from (11) are geometrically linearly disjoint. If their intersection were nontrivial, it would give a common nontrivial quotient of S4. Every such quotient (C2, S3, or S4) has a quadratic quotient. The unique quadratic subfields of the two covers would therefore agree, contradicting the different discriminant square classes.

Their compositum consequently has geometric group S4 x S4. Its quadratic subfields are generated by the two discriminant square classes. Each Delta_t has degree eight, so those classes, and their product, are unramified at a=infinity.

In contrast, the quadratic cover

    b^2 = -f(a)

is ramified at infinity, since f has odd degree three. It is therefore linearly disjoint from the signed-cover compositum. The same argument works for a single signed cover.

This proves the independence of the center sign epsilon(a); it must not be silently assumed from a split-fiber count. Arithmetic constant fields of the signed covers can be F_(q^2), as described after (11). Over the degree-one Frobenius coset the two prescribed sign-parity conditions are fixed, while the two geometric S4 coordinates and the extra center-character coordinate are independent.

### Uniform effective Chebotarev input

We use the standard consequence of the Weil bound for a finite cover of P1: the number of unramified rational base points with Frobenius in a prescribed conjugacy-invariant subset of its degree-one arithmetic coset is its coset proportion times q, with error O(sqrt(q)) when the covering degree and the genus of its geometric Galois closure are bounded.

Both bounds here are absolute. The signed geometric degree is 24; the two-cover compositum with the center-character cover has geometric degree at most `24^2*2`. All these fields can be presented using a bounded number of roots of the bounded-degree equations (8) and `y_i^2=-f(x_i)`, together with the center-character equation. Their projective curve components have bounded degree, hence their normalizations have bounded genus. This argument does not require a characteristic restriction beyond oddness, and also bounds the number of excluded branch points. Equivalently, one can apply the Weil bound to twists of these bounded-genus Galois covers.

It follows, for fixed signs sigma,tau and nonexceptional t,s in E_tau with distinct discriminant square classes, that

    sum_(a in E_sigma) M(a,t)
       = (q/2) p_(sigma,tau) + O(sqrt(q)),                  (18)

    sum_(a in E_sigma) M(a,t) M(a,s)
       = (q/2) p_(sigma,tau)^2 + O(sqrt(q)).                (19)

There are only O(1) additional a to discard for each column: a=t, branch points, and values for which t is also a root of C_t. For the last condition,

    C_t(a,t) = (t-a)[(fW'-Wf')(t)(t-a)+2f(t)W(t)],

which has at most two zeros. Thus (18)-(19) refer to the actual incidence matrix, up to the stated errors.

## 7. From correlations to arbitrary-subset mixing

The Hasse bound for `b^2=-f(a)` gives

    |E_sigma| = q/2 + O(sqrt(q)).                           (20)

Fix sigma,tau, delete the O(1) exceptional columns, and center the incidence block:

    B(a,t) = M(a,t)-p_(sigma,tau),
    a in E_sigma, t in E_tau.

Equations (18)-(20) show that entries of the Gram matrix `B^T B` are O(sqrt(q)) except for pairs of columns having the same discriminant square class. There are at most 96 such columns for each fixed column; on these entries the trivial O(q) bound suffices. Hence every absolute row sum of `B^T B` is O(q^(3/2)), and

    ||B||_(2->2) = O(q^(3/4)).                              (21)

Apply (21) to the indicator vectors of arbitrary A and T. Their Euclidean norms are at most sqrt(q), so the discrepancy is O(q^(7/4)). Reinstating the O(1) deleted columns changes it by only O(q). This proves (7).

In particular, the result is not an inference from average degrees: it controls every pair of parameter subsets, even subsets selected adversarially using f,W and all the collision data.

## 8. Deduction of the density bound

Let `N_sigma=|E_sigma|`. Apply (7) to the left side of (6), summing the four character blocks, and use (20):

    (1/4) sum_(a in S,t in F) M(a,t)
       = qn/48 + O(q^(7/4)).                               (22)

For the right side, `|D intersect E_sigma|=N_sigma-n_sigma`, and (7) gives

    sum_(a in S,t in D) M(a,t)
       = [2qn - 3(n_+^2+n_-^2) - 2n_+n_-]/24
         + O(q^(7/4)).                                     (23)

Terms from `N_sigma-q/2` are O(q^(3/2)) and are included in the error. Combining (6), (22), and (23) yields

    6(n_+^2+n_-^2)+4n_+n_-
       = 4n^2+2(n_+-n_-)^2
       <= 3qn+O(q^(7/4)),

which is (1). If n>=3q/4, divide `n(4n-3q)<=O(q^(7/4))` by n to obtain (2); otherwise (2) is automatic.

Finally, at the cyclic square-subgroup modulus,

    n^3 / ((q^3-1)/2) <= 27/32 + O(q^(-1/4)).               (24)

Thus neither 4/5 retention nor any fixed density above `2^(-1/3)` can be achieved by cyclic B3 subsets of this construction for unbounded q.

## 9. Verification and limitations

`quadratic_switching_density_audit.py` and its JSON output audit the exact algebra behind the argument:

* discriminant specializations (14)-(15), with the universal cubic discriminant convention;
* the quartic-fiber identity and its required character pattern;
* agreement between these five-parameter configurations and direct repeated-triple collisions for small fields;
* the exact covering inequality (6) on all collision-free parameter subsets in the specified small cases;
* geometric discriminant square-class fibers and the incidence-block statistics, including characteristic three and non-prime fields.

The completed audit checked 308 small-field choices: every admissible pair f,W at q=3,5, and every admissible W for the specified f at q=7,9,11,13. It independently checked 37,516 repeated triples and all 16,096 parameter subsets in the designated smallest cases; (6) held for all 15,999 subsets avoiding the quartic configurations. In total it checked 56,182 split-quartic polynomial identities. Both discriminant specializations were checked over q=3,5,7,9,11,27,81,101. Incidence and discriminant diagnostics also covered q=251,503,1009. Hash checks confirmed the protected Lean files were unchanged.

The computed block densities and centered column correlations are only diagnostics. They are not used as proof of (7), which follows from the cover and discriminant arguments above. No random-subset search or extrapolation from full-set failures is used.

The bound addresses the proposed cyclic retention mechanism, not the original integer conjecture. It also specifically uses the strong, repeated-summand B3 property. The repeated center in the forbidden configurations cannot be discarded when applying this obstruction.
