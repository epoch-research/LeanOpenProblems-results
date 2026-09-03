# Sparse weights for a full-pattern extremum; zero-level estimate still open

**No proof or disproof of the conjecture was obtained.** This report saves the
positive convex-optimization calculation and the exact remaining inequality.
`Spec.lean` is unchanged. These are paper proofs, not Lean proofs.

## 1. A finite extremum on actual full-injection counts

Let H be a graph on h vertices with e edges, and colour the edges of K_N in two
colours, where N >= 256h and h > 0. For each of the 2^e patterns sigma on E(H), put

    T_sigma(w) = sum_{f:V(H) -> [N] injective, realizing sigma}
                     product_{x in V(H)} w_{f(x)}.

All constraints refer to the actual original vertices. For strictly positive
weights, at least one count is positive, since every injection has a pattern.
Write M(w) = max_sigma T_sigma(w), tau = h/N, and kappa = 128h/N. On the
nonnegative orthant in R^N define

    Phi(lambda) = log M(exp(-lambda)) + kappa sum_v lambda_v.

### Proposition

Phi attains its minimum at a finite lambda*. There is a probability mixture pi
supported on the patterns attaining M(exp(-lambda*)) such that, for the exact
product-weighted injection law in each such pattern sector,

    p_{sigma,v} = Pr_{sigma,w}(v is used),
    ell_v = sum_sigma pi_sigma p_{sigma,v},

one has

    ell_v <= kappa,
    lambda*_v > 0 implies ell_v = kappa.

Consequently at most N/128 host vertices have weights different from one.
Furthermore

    sum_v lambda*_v <= e log(2)/(127 tau).

For H=Q_d this last bound is d N log(2)/254.

### Proof

The full sectors partition all injections. Jensen's inequality for a uniform
full injection gives

    sum_sigma T_sigma(exp(-lambda))
      = (N)_h E exp(-sum_{v in im f} lambda_v)
      >= (N)_h exp(-tau sum_v lambda_v).

Each host vertex is used with probability h/N in that uniform law. Hence

    Phi(lambda) >= log (N)_h - e log(2) + 127 tau sum_v lambda_v.

The right side tends to infinity as lambda leaves every bounded set in the
nonnegative orthant. Continuity and compactness therefore give a finite
minimum. Zero-count sectors can be discarded: they stay identically zero for
positive weights. Every remaining log T_sigma(exp(-lambda)) is a smooth convex
log-sum-exp function, with gradient -p_{sigma,v}. The maximum is convex.

At a constrained minimum, the subgradient optimality condition supplies a
convex combination of the gradients of the maximizing sectors such that its
v-th coordinate is zero when lambda*_v>0 and nonnegative when lambda*_v=0.
This is precisely the displayed assertion for kappa-ell_v. Equivalently, this
condition follows by finite-dimensional separation: if the convex hull of
these gradients missed that orthant normal cone, a feasible direction would
have strictly negative directional derivative for every active sector,
contradicting minimality.

Each sector law uses exactly h different vertices, so sum_v ell_v=h. If A is
the set of positive lambda*_v, then |A| kappa <= h, proving |A|<=N/128.
Finally Phi(lambda*)<=Phi(0)=log M(1)<=log (N)_h; comparison with the coercive
lower bound proves the stated sum bound. All weights exp(-lambda*_v) are
strictly positive because lambda* is finite. QED.

**Scope:** this is a capacity bound for a mixture of maximizing FULL-pattern
laws. It is not a per-sector bound, and is not a bound for a single half after
conditioning on its boundary. The result holds for every finite source H; the
cube structure has not yet been used.

## 2. Weighted finite-injection reflection identity

Now take H=Q_d, d>=2. Use the elementary reflections and the unbiased compound
operator H_op = P Q_a P defined and audited in `CubeFullPatternReflection.md`.
That operator includes the initial transfer of an arbitrary full pattern into
the reduced square-pattern family. Its conditional nonmonochromatic survival
coefficient after the first transfer is

    beta_d = 2(d-2)/(d(d-1)).

For one elementary reflection, the fixed source boundary has size 2r and each
exchanged interior has size r, with r=h/4. Fix an actual compatible boundary
injection f, and let n=N-2r. Index the half-extension vectors by r-subsets S of
the unused host set. Multiply each unweighted half-extension count by
product_{v in S} w_v, obtaining vectors a_f and b_f. Put v_f=a_f-b_f and
w(f)=product_{x in the fixed boundary} w_{f(x)}.

Let Dmat(S,T)=1[S and T are disjoint]. The exact original and folded full
counts are respectively

    sum_f w(f) a_f^T Dmat b_f,
    sum_f w(f) a_f^T Dmat a_f,
    sum_f w(f) b_f^T Dmat b_f.

This is a bijective decomposition of full injections: the boundary and each
half are injective and the two half images are required to be disjoint. No
conditioning or occupation estimate is needed for the identity.

Put D=binom(n-r,r) and q_j=(r)_j/(n-r)_j, with q_0=1. The ordinary Kneser
spectral projections Pi_j have eigenvalues D*(-1)^j*q_j. Thus the weighted
arithmetic reflection defect is exactly

    Delta = (D/2) sum_f w(f)
        [sum_{j odd} q_j ||Pi_j v_f||^2
         - sum_{j even} q_j ||Pi_j v_f||^2].

The even sum includes j=0. In particular, this is a SIGNED identity, not an
upper bound obtained by discarding positive contributions.

Start the full H_op trajectory with sigma sampled from the maximizing-sector
mixture pi of Section 1, and add these defects along all its elementary folds.
The implementation has finite expected length, and the finitely many weighted
pattern counts bound each increment. Telescoping is therefore justified. If
E(w,pi) denotes this expected accumulated defect, then exactly

    E(w,pi) = M(w) - sum_sigma pi_sigma (H_op T_w)(sigma).

If both constant pattern counts vanish, they also vanish for all strictly
positive weights. The absorbing pattern operator then gives

    (H_op T_w)(sigma) <= beta_d M(w),
    E(w,pi) >= (1-beta_d) M(w).

### The unproved completing estimate

For some absolute C>=256, at every N>=C h, under the hypothesis that both
constant counts vanish, one would need to establish for a minimizing pair
(w,pi) above that

    E(w,pi) < (1-beta_d) M(w).

**This inequality has not been proved.** The exact identity preceding it is
not evidence for the opposite strict bound. No reweighting descent implying
it has been found. The unweighted maximum-relative initial transfer from the
earlier attempt cannot be substituted: `CubeGlobalReflectionCompletion.md`
gives actual colourings refuting that unqualified estimate exponentially.

## 3. What an intersecting half-family does imply

If a folded full count is zero, each nonnegative boundary summand
w(f) a_f^T Dmat a_f is zero. Thus the positive support of each nonzero a_f is
intersecting. This assertion remains true for the positive weights above.

For a nonzero nonnegative vector a on the r-subsets with a^T Dmat a=0, put

    L=binom(n,r), Z=sum_S a(S),
    theta_v = sum_{S containing v} a(S)/Z,
    chi = L ||a||^2/Z^2.

Set q_3=0 when r<3. Since q_j<=q_3 for all odd j>=3, the zero quadratic form
and the nonnegative even contributions imply

    (1+q_3)||Pi_0 a||^2
      <= (q_1-q_3)||Pi_1 a||^2 + q_3||a||^2.

Indeed the odd spectral mass dominates ||Pi_0 a||^2, and its levels >=3 are
at most q_3 times all mass outside levels 0 and 1. The explicit first-level
projection is

    ||Pi_1 a||^2 / ||Pi_0 a||^2
      = [n(n-1)/(r(n-r))] sum_v (theta_v-r/n)^2,
    ||Pi_0 a||^2=Z^2/L.

Consequently

    1+q_3 <= (q_1-q_3) [n(n-1)/(r(n-r))]
                         sum_v (theta_v-r/n)^2 + q_3 chi.

This retains the actual negative Kneser spectrum. It gives no positivity
claim for connected cumulants or other unverified matrices.

**The missing link:** ell_v in Section 1 is an original-vertex marginal of
complete disjoint two-half configurations, mixed over maximizing sectors and
boundaries. theta_v and chi here belong to a boundary-conditioned SINGLE-half
law. No valid inequality was established transferring the former bound to
the latter quantities strongly enough to control E(w,pi).

## 4. Audit and status

The saved audit `check_cube_weighted_zero_level.py` checks exact weighted
counts, a nontrivial KKT certificate and rational potential comparisons,
weighted reflection spectra, and the last intersecting-family inequality.
The parent reran the agent's audit independently: 364200 full injections,
4096 rational potential comparisons, 10176 reflection spectral checks, and
45 separate intersecting-family checks passed. These finite checks support
the displayed auxiliary identities, not the unproved all-dimensional bound.

No completing mathematical chain is available and neither theorem in
`Spec.lean` has been changed.
