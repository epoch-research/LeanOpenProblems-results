# Injective tree-counting audit

## Outcome

No unrestricted embedding theorem was obtained. `Spec.lean` is unchanged. The following audit rules out importing a degree-sensitive counting result as a solution without checking its minimum-degree hypothesis. It also identifies an invalid displayed intermediate inequality in the available source; no claim that its main theorem is false is made.

## 1. Source and hypotheses

Mubayi and Verstraete, *The number of trees in a graph*, arXiv:1511.07274, is available at

    /corpus/src/1511.07274/1511.07274.tex

Its main theorem concerns a t-edge tree T and a graph G with **minimum degree at least t**. It claims the following lower bound for the number of labeled injective embeddings:

    2m product_v (d(v)-t+1)^((t-1)d(v)/(2m)).

The average-degree corollary retains the same minimum-degree hypothesis. Removing that hypothesis is not a permitted application of the theorem. In particular, d(v)-t+1 can be zero or negative in the density cores of the present problem, so the logarithmic proof cannot simply be continued to those cores.

The literal hypotheses of Spec do not imply that G contains any nonempty subgraph of minimum degree t. For example, set t=3 and G=K_{2,3}. Then n=5, m=6, and

    ((t-1)/2)n+1 = 6 = m.

Every nonempty subgraph has a vertex of degree at most two: if it contains a vertex of the three-side, that vertex has at most two neighbors; otherwise it has no edges. Thus no deletion procedure can produce the minimum degree required by this counting theorem. This is not a conjecture counterexample: K_{2,3} contains both three-edge tree shapes.

## 2. A displayed entropy step cannot be used as written

The source constructs a probability P on injective embeddings by sequential greedy choices, and defines an upper weight

    p(f) = (2m)^(-1) product_{internal roles u}
                          (d(f(u))-t+1)^(-(d_T(u)-1)).

It states P(f)<=p(f). The weight p need not be a probability. One displayed line then asserts

    |Emb(T,G)| >= product_f P(f)^(-P(f))
                >= product_f p(f)^(-p(f)).

The second inequality is false even for a complete graph. Take t=4, G=K_5, and any fixed labeled four-edge tree T. Every injection is an embedding, so there are 5!=120 embeddings. Each greedy embedding has probability 1/120, whereas p(f)=1/20 because all d(v)-t+1 equal one. Consequently

    product_f P(f)^(-P(f)) = 120,
    product_f p(f)^(-p(f)) = 20^6 = 64,000,000.

This violates the displayed intermediate inequality. The subsequent replacement of the common factor by 2m also requires normalization: its actual exponent in that product is sum_f p(f)=6, not one.

This calculation does **not** refute the stated main counting bound. For this example, the latter bound is only 20, which is less than 120. It does mean that the displayed proof cannot be imported verbatim as a rigorous entropy argument, independently of the already-fatal minimum-degree mismatch for Spec.

## 3. Remaining mathematical requirement

A global positive lower bound for injective embeddings at average degree greater than t-1 would establish the conjecture. None was derived here. Homomorphism counting, unconditional tree-walk stationarity, and positivity under minimum degree at least t do not supply it. The previous weighted-recurrence reports already distinguish unconditioned stationarity from the nonstationary law after conditioning on injectivity.

No Lean proof was added on the basis of this source. Neither proof nor disproof is ready for submission.
