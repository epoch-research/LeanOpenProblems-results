# A cyclic-group construction test

## Status

Erdős 66 remains **unproved and undisproved** in this workspace. `Spec.lean`
has not been altered; its original `sorry` remains. These are auxiliary results.

## Motivation

The previously constructed flat sets live in elementary-abelian additive groups.
A quadratic extension's multiplicative group is cyclic, so it is natural to test
unions of parallel affine lines in that extension instead.

With alpha^2 = nu, a product of line points has coordinates

    (x + u alpha)(y + v alpha) = (xy + nu uv) + (vx + uy) alpha.

For a target s+t alpha and u,v nonzero, eliminate y=(t-vx)/u. The equation is

    v x^2 - t x + u(s - nu uv) = 0.

Its discriminant is

    Delta = t^2 - 4uvs + 4nu(uv)^2.

## Checked results in `CyclicLineExplore.lean`

- `line_product_equation_iff`: the elimination identity.
- `line_product_count`: the root count is 1 + chi(Delta), in odd characteristic.
- `lineProductCount_identity`: summing over u,v groups the error by uv=w.
- `weightedProductFiber_eq`: if m_U(w) counts pairs uv=w, the weighted fiber is

      M_U(w) = chi(w) m_U(w).

- `weightedProductFiber_l1`: for 0 not in U,

      sum_w |M_U(w)| = |U|^2.

- `lineProductCount_weighted_identity`: the corresponding grouped count is

      R_U(s,t) = |U|^2 + sum_w M_U(w) chi(t^2/w - 4s + 4nu w).

- `lineProductCount_triangle_bound`: the direct triangle estimate gives only

      |R_U(s,t) - |U|^2| <= |U|^2.

All these statements compile and their axiom checks use only `propext`,
`Classical.choice`, and `Quot.sound`.

## Limitation

This does NOT show that all line-union constructions fail. It shows that the
specific additive-fiber cancellation estimate from `FiniteFieldExplore.lean`
does not carry over: multiplicativity makes the character weight constant on
each product fiber, so the total variation is the full main term.

No replacement estimate or compatible integer-prefix construction was found.
Even a flat cyclic construction would still require controlling the division
between wrapped and unwrapped integer representations.
