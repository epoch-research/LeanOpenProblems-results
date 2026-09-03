# Uniform composite-error regularity — conjecture still unresolved

Submission/Spec.lean remains unchanged with its original sorry. No proof of
prime-pair infinitude for every irrational slope, and no irrational
counterexample, has been obtained. No incomplete proof was submitted.

## New verified file

Submission/CompositeErrorRegularity.lean
Namespace: Erdos972CompositeErrorRegularity.

The file compiles without errors or warnings. The three principal printed
axiom audits contain only propext, Classical.choice, and Quot.sound.

Let c(q) be compositeProxyTwo(q), and let

    T(B) = sum_{q>=B} c(q),
    E(alpha) = sum_{n>=0} primeInputErrorTwo(alpha,n),
    E_B(alpha) = sum_{n<B} primeInputErrorTwo(alpha,n).

The new results are:

* compositeTail_tendsto: T(B) tends to zero.
* uniform_tail_bound: for every alpha>=1 and every B,

      0 <= E(alpha)-E_B(alpha) <= T(B).

  The bound is independent of alpha. The proof maps the input tail into
  the output tail using injectivity and n<=floor(alpha*n), then uses the
  existing summability over all composite outputs.
* partialError_tendstoUniformlyOn: E_B converges uniformly to E on [1,infinity).
* floorMul_eventually_eq, error_term_eventually_eq, and
  partialError_eventually_eq: each fixed finite floor/error pattern is
  locally constant at an irrational alpha>=1.
* continuousAt_totalError: E is continuous at every irrational alpha>1.
  The proof is in the ambient real topology, not merely the topology of
  the irrational slopes.

## Exact limitation

These results concern the composite error only. The complete prime proxy
also contains the genuine-prime indicator. The summable output envelope
used above does not dominate that indicator: the proxy is exactly one
at every genuine prime output. Uniform convergence or continuity of the
error therefore does not imply convergence, continuity, or divergence of
the full detector.

In particular, almost-everywhere/comeagre divergence of the full detector
cannot be transferred to a prescribed irrational point using this error
continuity theorem alone. No such transfer was asserted or proved.

A sufficient pointwise arithmetic lower bound is still missing. This file
is auxiliary development, not a replacement proof for Spec.lean.

Compilation:

    lake env lean -o .lake/build/lib/lean/Submission/CompositeErrorRegularity.olean \
      Submission/CompositeErrorRegularity.lean

CheckCompositeRegularityAPI.lean is an API-inspection scratch file with
intentionally unsuccessful checks; it must not be imported into a final proof.
