# Spectral benchmark: proof map, exact gaps, and continuation targets

## Outcome that is actually proved

With the definitions in the question, the following implication is proved in full in `CubeSpectralBenchmark.md`:

\[
 p\ge\tfrac12,\quad\|A-p(J-I)\|_{op}\le K\sqrt N,\quad
 N\ge10^6(K+4)^2d^2 2^d
 \quad\Longrightarrow\quad Q_d\subseteq G.
\]

This is an all-dimensional positive result under the original host hypothesis. It is not a proof of the desired `N>=C_K2^d` benchmark. The theorem does not assert a lower bound on the number of injective copies comparable with the random baseline.

The constant `10^6(K+4)^2` is explicit and independent of `d`; the separate factor `d^2` is not hidden in that constant. The full arbitrary-colouring Ramsey problem remains outside what is proved.

## Proven dependency chain

1. Independent edge thinning, with an elementary quadratic-form net estimate, passes to a **subgraph** whose adjacency matrix is spectrally close to the reference matrix `(J-I)/2`. It does not redefine the actual density of this subgraph.
2. Column-degree pruning in a balanced host cut loses only `O(K^2d^2)` vertices and leaves both parts of linear size.
3. For every `d`, the random common-neighbourhood count `Z` has the exact decomposition
   \[
   \operatorname{Var}Z
   =d\,a^T(D^TD/M)a
    +\sum_{v,w}R_{vw}^2\sum_{i=0}^{d-2}(i+1)(q_vq_w)^i c_{vw}^{d-2-i}.
   \]
   The whole Gram term is retained, and the remainder has nonnegative coefficients. This gives `Var Z <= 25(K+4)^2 n/2^d` after pruning. It is an all-orders statement, not a verification for finitely many small cubes.
4. Cube distance-two supports satisfy
   `e_2(T) <= (d-1)|T| log_2|T|/2`. This yields disjoint-neighbourhood subfamilies without paying the full maximum conflict degree on small supports.
5. A simultaneous local-lemma construction avoids small lists, collisions on the first parity class, and disjoint-star overload witnesses.
6. The resulting candidate incidence matrix has minimum row degree greater than its maximum column degree. Hall's theorem supplies an injection on the other parity class, into a disjoint host part.

Every step in this chain is proved with explicit constants. No pseudorandom blow-up lemma with untracked dependence on `d` is invoked.

## The exact signed work that is also proved

`CubeSignedActivityLemmas.md` records:

* the proposed `Xi(0)` and `Xi(1)` identities with zero host diagonal;
* contraction of selected collision components, with the exact partition-lattice Möbius factor;
* preservation of quotient multigraph edge multiplicities and independent quotient labels;
* a proof of the negative-activity positivity criterion;
* the pure-collision load estimate;
* a whole-star formal generating function valid to **every** order,
  \[
  W_\star(t;1)=
  \frac{N^{-1}\sum_x(1+t/(pN))^{\deg(x)}}{(1+t/N)^N};
  \]
* the positive even-cycle trace term and its correct `N^{1-|U|/2}` spectral scale;
* the cube edge-isoperimetric inequality with its exact `1/2` coefficient.

The whole-star numerator includes all degree fluctuations before any coefficient is estimated. A further proved consequence is recorded in `CubeSpectralStarControl.md`: if `N>=4*10^9(K^2+1)2^d`, one can delete at most `10^6K^2d^2` degree-exceptional vertices so that the **entire induced-star activity subfamily**, with no size truncation, has per-vertex absolute load at most `162000(K^2+1)2^d/N < 10^{-3}`. The sharper bound is `8000(9K^2+1)d^2/n` on the remaining `n` vertices. This uses Cauchy coefficient estimates on the fully resummed star generating function and the mean-zero degree errors; it is not an absolute bound on the individual diagrams.

These lemmas are directly compatible with the proposed signed programme, but they do not give a complete polymer regrouping for overlapping cube cores. In particular, a star selected inside a larger non-star support is not covered just because the induced-star supports have been bounded. Section 4 of `CubeSpectralStarControl.md` records a precise remaining budget: induced-star and edgeless supports together use less than `0.002`; a bound of `1-e^{-1}-0.002` for the negative load of the remaining supports would suffice. That remaining inequality is expressly unproved and may require a further exact whole-core regrouping rather than the raw activities.

## Gap A: the small-list construction is not dimension-free

Put `C=N/2^d`. The proved common-neighbourhood lower-tail estimate is

\[
 \Pr(|L_y|<n/2^{d+1})\le500(K+4)^2/C.
\]

Each such event involves `d` independent variables, and each variable belongs to `d` small-list events. The local-lemma budget therefore requires `C` to dominate `K^2d^2`. At fixed `C`, the proof's budget fails for large `d`; one cannot fix this by increasing an absolute numerical constant once and for all.

A substantially better *correlated* treatment is required. Simply replacing the true dependency graph by an independent family, or asserting exponential common-neighbourhood tails from the operator norm alone, is not justified by the variance identity.

## Gap B: the bounded-column certificate is stronger than Hall

The successful proof uses

\[
 C>6k(1+d\log_2C),\qquad k=\lceil8\log C+20\rceil.
\]

That condition also fails at fixed `C` and unbounded `d`. The method deliberately asks for a uniform bound on every column load; Hall's condition only asks for expansion of row sets, and is weaker.

A possible continuation is to count actual Hall-deficient row cores and retain their internal positive structure, instead of ruling out every high column load. No bound sufficient for this continuation is proved in the files. Even repairing this part would leave Gap A.

## Gap C: a compatible whole-core signed regrouping is still absent

After collision contraction an activity is an alternating sum of homomorphism densities of loopless multigraph quotients. Spectral norm control does not authorize a bound `N^{-|U|/2}` for these terms; already an uncontracted `C_4` has the general scale `N^{-1}`.

For a finished activity proof, one would need all of the following, not merely a bound on selected diagrams:

1. An **exact** regrouping into positive whole-core weights and residual signed polymers, compatible when cores overlap.
2. A proof that the positive baseline of that regrouping is strictly positive for the relevant finite population.
3. A uniform estimate for the residual negative load, such as
   \[
   \sup_v\sum_{U\ni v}(-\widetilde w(U))_+e^{|U|-1}
       \le1-e^{-1}
   \]
   when `N>=C_K2^d`, or an explicitly proved replacement criterion that incorporates the positive core gas.
4. Support enumeration adequate for the dense quotient cores, using actual cube geometry rather than just the upper bound `e(U)<=|U|log_2|U|/2` in isolation.

The star formula proves this type of regrouping for a single arbitrarily large star, and the Gram identity does so for the second moment of an arbitrarily large star list. Neither supplies compatibility for a whole cube. Applying the elementary criterion to a different partition function without proving that it equals, or lower-bounds, the original injective count would not close the gap.

## What has not been inferred

* No conclusion that all signed activities are nonnegative.
* No conclusion that all negative pieces of positive cores have small absolute mass.
* No conclusion that ordinary quasirandomness `o(N)` is enough for (T).
* No inference from homomorphism positivity to injectivity.
* No claim that checking finitely many matrices or cubes proves the uniform statements.
* No claim that `d^2` is necessary for the benchmark; it is a limitation of the proved argument.

The next useful checkpoint would be either a genuinely compatible core regrouping with a constant load, or a direct Hall-core embedding argument which overcomes both dimension-dependent conditions above. The present files supply a proved all-dimensional spectral theorem and reusable signed/Gram lemmas, but leave that checkpoint open.
