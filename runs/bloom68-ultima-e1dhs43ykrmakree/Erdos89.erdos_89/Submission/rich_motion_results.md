# Results of the rich-motion investigation

**The sharp planar conjecture remains unresolved.** The proved result is an insufficiency theorem for a precise, fairly strong relaxation of the suggested argument.

## Main negative theorem

For arbitrarily large powers of two `t`, there is an abstract balanced edge-colored `n`-vertex model with

```
n = 2^t,    D = n/t,    r_d = t(n-1).
```

It has an indexed family of actual vertex subsets `Q_g` satisfying:

- `sum_g a_{g,d}=r_d^2`, `sum_d a_{g,d}=k_g(k_g-1)`, with even integer entries;
- `#{g:k_g>=k} <= 12 n^3/k^2`;
- one identity row, and every other row has `k_g<=sqrt(n)` and `D(Q_g)>=k_g/16`;
- **every** half-size subset obeys `K(Q)<=2K(P)/3`, hence contraction defect at least `5t^2/9`;
- all multiway source-domain intersection identities, their exact point-cardinality row sums, and their weighted Gram inequalities;
- partial bijections of ordered edges with a unique label for every equal-colored source/target edge pair, giving the specified support-only entropy inequality for every reweighting.

The construction uses a probabilistically proved balanced coloring and explicit affine two-design families over `F_n`. All nonidentity rows even have a linear per-color count bound. The usual numerical `O(|Q|^(4/3))` unit-distance bound holds on every subset.

Nevertheless `D sqrt(log n)/n -> 0`. With constant `r_d`, support-uniform weighting is a global rescaling; each of `t/2` dyadic row strata retains mass comparable to `D/t`.

**Scope:** the edge maps are not required to assign a consistent image to a shared point. They are not asserted to come from Euclidean motions, and do not satisfy a proved coherent inverse/composition law. This theorem does not refute the sharp conjecture or rule out a proof using that additional geometry.

## Exact positive inequality for genuine planar motions

Write `b_{g,h,d}=r_d(P intersect g^{-1}P intersect h^{-1}P)`. The matrices

```
C^d[g,h] = a_{h g^{-1},d},    B^d[g,h] = b_{g,h,d},    v^d[g] = a_{g,d}
```

satisfy

```
C^d >= B^d >= v^d (v^d)^T / r_d       (PSD order).
```

Thus, for arbitrary real `z_g` and `W_g=sum_d a_{g,d}/r_d^2`,

```
sum_{g,h} z_g z_h W_{h g^{-1}}
 >= sum_d (sum_g z_g a_{g,d})^2 / r_d^3
 >= (sum_g z_g W_g)^2 / W_id.
```

The first PSD difference counts contributions of source edges outside the original point set. It is actual coherent composition information, not determined by intersections of the `Q_g` inside `P`.

A separate dyadic autocorrelation example shows why positive definiteness plus a weak-l1 tail alone still permits a full logarithmic loss. An actual collinear planar construction has a full rich-motion set of size `Theta(q^2)`, including half-turns, with product set of size `Theta(q^4)`. Thus bounded approximate-group structure is not automatic from richness.

## Files and checks

- `rich_motion_joint_table.md`: complete statements, constructions, proofs, and scope distinctions.
- `verify_rich_motion_joint_table.py`: exact combinatorial/rational checks; entropy spot-checks use floating logarithms.
- `rich_motion_verification.txt`: saved successful test output.

Run with `python3 verify_rich_motion_joint_table.py` (uses NetworkX).

The checks include 4,681 rows and 14,400 uniquely labeled ordered-edge correspondences at `n=16`; all low-order domain moments at `n=4`; exact geometric Gram identities on a six-point planar grid; dyadic kernels; and full rich-set product growth. Integer parameter checks go through `t=2048`. These checks supplement, not replace, the asymptotic proofs. No Lean files were modified.
