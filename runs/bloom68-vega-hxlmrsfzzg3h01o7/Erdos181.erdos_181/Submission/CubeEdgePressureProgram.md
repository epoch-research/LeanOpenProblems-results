# Edge-fugacity and capacity-pressure program — EL is UNPROVED

**No Ramsey proof is obtained.** This document records a new focused program
suggested by a planning agent and independently checked at the level of its
elementary prerequisites. `Spec.lean` is unchanged. The central inequality EL
below is an unproved target; it must not be cited as a theorem.

## 1. Edge-fugacity optimization (proved elementary prerequisite)

Let G be a majority colour on N vertices. Put p(G)=2|E(G)|/N^2. For j>=1 write
b_j=2^j, e_j=j*2^(j-1), t_j(A)=N^(-b_j) hom(Q_j,A),
a_j(A)=t_j(A)^(1/e_j). Hom counts in this section ALLOW repeated vertices.
Fix an absolute K>=64. For host edges e of G let lambda_e>=0, and define
A_lambda(e)=exp(-lambda_e), with A_lambda=0 on nonedges and the diagonal.
Set alpha=2K/N^2 and

    Phi_j(lambda)=log a_j(A_lambda)+alpha sum_e lambda_e,
    c_j=min_{lambda>=0} Phi_j(lambda).

### Finite minimizers

Each host edge yields two homomorphisms constant on the source parity classes.
Averaging these 2|E(G)| actual homomorphisms and using Jensen gives

    log a_j(A_lambda)
      >= [log(2|E(G)|)-b_j log N]/e_j
         - (1/|E(G)|) sum_e lambda_e.

Since G is a majority colour, alpha>1/|E(G)| for the indicated K and N>=2.
Thus Phi_j is continuous and coercive on the nonnegative orthant. It has a
finite minimizer lambda_j. It is convex, being a scaled log-sum-exp plus a
linear function.

### Exact edge-flux certificate

Under the weighted Q_j homomorphism law at lambda_j, let M_e count the source
edges mapped to unordered host edge e, with multiplicity. Differentiating the
finite partition and using constrained optimality gives

    E[M_e]/e_j <= alpha,
    lambda_{j,e}>0 implies E[M_e]/e_j=alpha.

The multiplicities sum to e_j in every homomorphism. Therefore at most
1/alpha=N^2/(2K) edges are penalized. As 0<A<=1 on G,

    p(A_lambda_j) >= p(G)-1/K.

For every fixed oriented source edge uv and host pair x,y, edge transitivity
(including reversal) of Q_j gives

    Pr(phi(u)=x,phi(v)=y) <= K/N^2.

This is an unconditioned EDGE-flux bound. It is not an assertion about a
boundary-conditioned block law or an injective homomorphism law.

### Monotone optimized profile and one common kernel

Weak norming gives a_(j+1)(A)>=a_j(A), so Phi_(j+1)>=Phi_j pointwise and c_j is
nondecreasing. At its own minimizer, Sidorenko and the density bound give

    log(p(G)-1/K) <= c_j <= 0.

For lambda*=lambda_(k+1), define

    Delta_k(A*)=log a_(k+1)(A*)-log a_k(A*).

Then

    0 <= Delta_k(A*) <= c_(k+1)-c_k.

Thus this SAME kernel has the Q_(k+1) edge-flux certificate and the selected
small norm increment. Reweighting after choosing a scale is not being assumed
to preserve a previous increment bound.

There is also an exact KL comparison. Let nu_k^lambda be the weighted Q_k hom
law. The finite log-partition identity and complementary slackness imply

    D(nu_k^(lambda_k) || nu_k^(lambda*))
       <= e_k [c_(k+1)-c_k].

Indeed D/e_k=log a_k(A*)-log a_k(A_lambda_k)
 +(lambda*-lambda_k) dot (E_lambda_k M/e_k), which is at most
Phi_k(lambda*)-c_k <= c_(k+1)-c_k. No conditional capacity conclusion follows
from this KL inequality without further proof.

## 2. Global soft-edge partition and capped entropy (proved prerequisite)

Put h=2^d, b=2^k, r=d-k, 1<=k<=d/4. The source is Q_r square Q_k. Fix a
symmetric kernel A in [0,1] with zero diagonal. For T>=0 set, off the diagonal,

    K_T(x,y)=A(x,y)+exp(-T)(1-A(x,y)),

and put K_T(x,x)=0. Let Z_T be the weighted sum over GLOBAL INJECTIONS of ALL
h source labels, with internal Q_k edges weighted by A and outer edges by K_T.
Thus Z_0 is a genuine integral packing partition of unlinked Q_k blocks, and

    lim_(T->infinity) Z_T = inj(Q_d,A).

Provided N is a sufficiently large constant multiple of h, p(A)>=15/32, and
d is sufficiently large, Z_0>0. Here is the needed edge-weighted check: after
deleting at most h vertices, normalized weighted density is at least
p(A)-2h/N. Weak norming and dropping edges incident to an identified vertex,
using A<=1, give the usual injective block lower bound with collision error
binom(b,2)/(N' a_k(A_res)^k). For k<=d/4 and a fixed residual density >.4,
this error tends to zero exponentially in d. Greedily choosing the finitely
many blocks therefore constructs a globally injective packing. This does not
assume that a prior vertex-weighted theorem covers arbitrary edge weights.
For finite T, K_T is positive on every distinct host pair, so Z_T>0 as well.

Now pin the FULL cube parity class E by an injection f, put m=h/2 and
X_f=[N] minus im(f). For y in the opposite parity, v in X_f, let

    c_(f,T)(y,v)=product_{x~y} W_xy(f(x),v),

where W_xy=A or K_T according to whether that source coordinate is internal
or outer. This includes EVERY cube edge. Define

    F_(f,T)=max_beta sum_(y,v) beta_yv log(c_(f,T)(y,v)/beta_yv),

where row sums are 1, column sums are <=1, beta>=0, and beta=0 at zero entries
of c. Use 0 log(0/0)=0 on omitted coordinates. If the feasible set is empty,
F=-infinity. Its entropy dual is

    F_(f,T)=inf_(lambda_v>=0)
       [sum_v lambda_v + sum_y log sum_v c_(f,T)(y,v) exp(-lambda_v)].

The infimum need not be attained in boundary cases. Let J_(f,T) be the actual
weighted injective extension count and Zhat_T=sum_f exp(F_(f,T)). Then

    exp(F_(f,T)-m) <= J_(f,T) <= exp(F_(f,T)),
    exp(-m) Zhat_T <= Z_T <= Zhat_T.                       (S)

Proof of lower bound: for any feasible beta, set gamma_v=sum_y beta_yv<=1.
Weighted AM-GM gives Cap_gamma(P)>=exp(objective(beta)) for the product of
actual list linear forms P=product_y sum_v c_(f,T)(y,v) x_v. This product is
real stable. The fixed-exponent truncation inequality from
`CubeJointSignedCompletionAttempt.md` (2.7) yields SF(P)(1)>=exp(F)*exp(-m),
since sum_v I(gamma_v)<=sum_v gamma_v=m. SF(P)(1) is EXACTLY J_(f,T).
The upper bound follows from entropy subadditivity applied to the weighted
law of actual injective matchings. If no feasible beta exists there is also
no matching; in that case both sides are zero. Conversely any feasible beta
has an integral matching on its support by bipartite matching integrality.
Stability is used before summing over f, never for the summed polynomial.

## 3. Target: edge-balanced inverse-Hölder pressure inequality

### EL — UNPROVED, not available as a lemma

Seek a universal epsilon_0>0 and constants C_0(K),L(K) such that the following
hypotheses imply the inequality below:

- A is symmetric, [0,1]-valued, zero-diagonal, p(A)>=15/32;
- N>=C_0(K)h, 1<=k<=d/4;
- A=A_lambda* for an ACTUAL finite minimizer of Phi_(k+1) on a
  majority host G as in Section 1 (this additional hypothesis is allowed in
  the sufficient target; oriented edge flux alone does not imply it);
- consequently the Q_(k+1) weighted hom law has oriented edge flux <=K/N^2,
  and the full edge-multiplicity complementary-slackness certificate holds;
- (k+1)Delta_k(A)<=epsilon_0;
- q_k=t_(k+1)(A)/t_k(A)^2 and

      N^b t_k(A) q_k^r >= h^2 exp(kb/10).

Desired conclusion for EVERY T>=0:

    log Zhat_0-log Zhat_T
      <= [rh/(2e_(k+1))]
           log[t_(k+1)(K_0)/t_(k+1)(K_T)] + L(K)h.         (EL)

These are small-cube hypotheses and a GLOBAL, already capacity-corrected
pressure conclusion. In particular, the hypothesis does not include the
existence of a good pinned sector at T=infinity. EL is stronger than a bare
existence assertion and might itself fail quantitatively; it requires proof
or a genuine diagnostic counterexample.

### Concrete unresolved step: lift price excess to one host-edge direction

At differentiability points, the negative derivative of log Zhat_T is its
sector-weighted average of

    sum_(y,v) beta*_(f,yv) sum_(x~y, outer)
       exp(-T)(1-A(f(x),v))/K_T(f(x),v).

Compare its integrated response with -partial_T log t_(k+1)(K_T), times
rh/(2e_(k+1)). The required total excess budget is O_K(h), not O_K(dh).
A possible inverse-Hölder proof would show that excessive integrated loss
produces either:

1. a genuine penalty direction on actual host edges decreasing Phi_(k+1),
   contradicting the edge-fugacity optimality certificate; or
2. (k+1)Delta_k(A)>epsilon_0.

**NO SUCH IMPLICATION IS PROVED.** The dual prices vary with the whole pinned
sector and with its row lists. Simply averaging them into edge prices does
not preserve the overlapping source constraints and is not a certificate.
Likewise the edge-flux and KL bounds are unconditioned and cannot be carried
through arbitrary boundary pinning without a new argument.

## 4. Conditional completion, if and only if EL is genuinely established

This section is a mathematical implication, not a completed Ramsey proof.
Assume EL with epsilon_0 universal. Choose K extremely large such that

    epsilon_0 log(K/512)>2 log(32/15),

and put theta=64/K. The bounded monotone c_j profile forces, for sufficiently
large d, some k in [ceil(theta d),floor(d/4)] with

    (k+1)(c_(k+1)-c_k)<=epsilon_0.

Otherwise summing epsilon_0/(k+1) over this interval exceeds the total possible
increase of the profile. Choose A=A_(lambda_(k+1)). It has all edge-flux and
norm-increment properties of Section 1, with p(A)>=1/2-2/K for large N.
Weak norming gives q_k>=a_k(A)^b and t_k(A)=a_k(A)^(kb/2). Consequently

    log(N^b t_k q_k^r)
      >= b[log(N/h)+(k/2)log 2-8d/K]
      >= b[log(N/h)+k/5].

Here log a_k>=log p(A)>=-log 2-8/K and k>=64d/K were used. Since k grows
linearly with d, the required surplus h^2 exp(kb/10) follows eventually.
The genuine small-block packing check in Section 2 gives Z_0>0.

Apply EL and (S), and let T tend to infinity. The positive small-cube hom
count t_(k+1)(A) yields

    inj(Q_d,A)
      >= exp(-(L(K)+1/2)h) Z_0
         [t_(k+1)(A)/t_(k+1)(K_0)]^(rh/(2e_(k+1))) >0.

All positive edges of A belong to G, so the same injection is monochromatic
in the original colouring. Finitely many smaller dimensions can be absorbed
in an absolute Ramsey constant using ordinary finite Ramsey existence.

**Critical accuracy issue:** if the proof only supplies epsilon_0(K) with
epsilon_0(K)*log K too small (e.g. epsilon_0=O(1/K)), the optimized-profile
selection does not force EL's hypothesis. A dimension-dependent L or an
O(dh) loss also fails to provide the intended quantitative pressure bound,
though any finite uniform-in-T loss might still give a separate existence
argument if its hypotheses can be forced. Keep these distinctions explicit.

## 5. Known decisive tests, not assumptions

- All-red and two-clique/bipartite hosts: one colour is chosen before
  regularization. No averaged connected cumulants or stability-of-mixtures
  assertion occurs. An exp(-O(h)) loss is allowed, so no refuted
  constant-relative full-pattern transfer is asserted.
- For any host edge set F, the edge-flux law bounds the mass of a fixed source
  edge landing in F by 2K|F|/N^2. For a union of disjoint pockets each of size
  at most h, this is at most Kh/N. This is not a proof for overlapping phases.
- Bad individual pinned sectors may vanish at T=infinity. EL concerns their
  summed, full-column-capacity-corrected pressure.
- The density hypothesis matters: at density <1/4 a random host on N=Ch has
  too few cube copies even at the first-moment level. Do not extend the
  target to arbitrary positive densities.

No changes to `Spec.lean`, no new Lean proof, and no submission claim.
