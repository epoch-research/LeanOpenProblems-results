# Exact parity kernels: the unrooted conjecture is false

## Verdict

**There is a 44-vertex counterexample with both bipartition classes strictly larger than `c`.** The counterexample and its numerical hypotheses are fully Lean-proved in the separate file `Submission/TreeExactKernelCounterexample.lean`.

No specification, shared kernel, or shared cut source was modified. The counterexample has no host-graph or ES assumptions.

## 1. Counterexample and short proof

Construct `T₇`:

* Join two hubs `x,y` by an edge.
* Attach seven support vertices to each hub.
* Attach two leaves to each support.

Thus

\[
 n=44,\quad k=43,\quad |A_T|=|B_T|=22,\quad\Delta(T)=8.
\]

Take **`c=19`**. All requested hypotheses hold: `1≤19≤min(22,22,⌊43/2⌋)`.

An exact kernel would have `|U|=19`, `|W|≥19`, hence **`|R|≤6`**. For a connected nonempty core, the kernel conditions force `U` to be exactly the odd-distance set. Classify the core by its retained hubs.

### Both hubs belong to `R`

Let `a` count retained supports and `b` retained leaves. Then

\[
 |R|=2+a+b,\qquad |U|=14+a-b.
\]

Each omitted support contributes one odd vertex; a retained support contributes its unretained leaves. Exactness requires `a−b=5`, so `|R|≥7`, impossible.

### Exactly one hub belongs to `R`

Connectivity places the whole core on that hub's side. Let `a,b` again count retained supports and leaves. The entire opposite side contributes fifteen odd vertices, giving

\[
 |R|=1+a+b,\qquad |U|=22+a-b,\qquad b\le2a.
\]

Exactness requires `b=a+3`. Thus `a≥3` and `|R|=4+2a≥10`, impossible.

### Neither hub belongs to `R`

Connectivity places `R` inside one three-vertex cherry. The possibilities are a singleton, a support–leaf edge, or the whole cherry. Their odd counts are respectively **22, 21, 20**, never 19.

These cases exhaust all global connected cores. There is **no prescribed-root or nested-core restriction**.

The obstruction is sharp: both hubs and any four supports, with no leaves, give

\[
 (|R|,|U|,|W|)=(6,18,20).
\]

An exact 19-odd core exists at size seven (both hubs and five supports), but removes only 37 vertices, one short of the required 38.

### Formal certificate

`TreeExactKernelCounterexample.lean` imports only the shared `TreeParityKernel`. Namespace `TreeExactKernelCounterexample` contains:

* `isTree`, `edge_card`, `card_vertices`, `color_card`, `maximum_degree`, `admissible`;
* `no_exact_unrooted`:
  ```lean
  ¬ ∃ R U W : Finset V,
      IsParityKernel T 19 R U W ∧ U.card = 19
  ```
* `odd_le_eighteen`: every existing kernel at `c=19` has at most 18 odd vertices;
* `at_most_witness`: an explicit kernel with cardinalities `(6,18,20)`.

The proof uses structural connectivity and local count inequalities. Finite auxiliary checks use kernel-checked `decide`, not `native_decide`. Its axiom audit contains only `[propext, Classical.choice, Quot.sound]`.

## 2. Infinite family and exact attainable intervals

Let `T_d` have `d≥1` two-leaf supports at each hub. Put

\[
 n=6d+2,\qquad m=3d+1=|A_T|=|B_T|.
\]

For exact odd count `c`, write `t=m−c`. The classification gives the complete minimum-core-size profile. Take the minimum over applicable rows:

| Retained hubs | Allowed `t` | Minimum core size |
|---|---|---|
| 0 | `0,1,2` | `t+1` |
| 1 | `−d≤t≤0` | `1−t` |
| 1 | `0≤t≤d` | `1+3t` |
| 2 | `1−d≤t≤d+1` | `d+3−t` |
| 2 | `d+1≤t≤3d+1` | `3t−3d−1` |

**Derivation.** With one hub, `t=b−a` and `|R|=1+a+b`; with two, `t=d+1−a+b` and `|R|=2+a+b`. In both cases `0≤b≤2a`, with `a≤d` or `a≤2d`. Minimizing over `a` gives the table. Each minimum is realized by choosing the indicated supports and leaves.

The removal bound is `|R|≤2t`. In the admissible range `1≤c≤3d`, one-hub cores never work. Zero-hub cores supply `t=1,2`; two-hub cores work exactly when `t≥⌈(d+3)/3⌉`. Consequently:

\[
 \boxed{c\text{ is exactly attainable in }T_d
 \iff c\in[1,\lfloor8d/3\rfloor]\cup\{3d-1,3d\}.}
\]

For `d=7`, this is `[1,18]∪{20,21}`, with the admissible gap at 19. Gap lengths grow without bound. Thus even the admissible good-cardinality spectrum need not be an interval.

For the **fixed** removal budget 38 in `T₇`, the complete odd spectrum of cores of size at most six is

\[
 [13,18]\cup[20,27].
\]

### Necessary size of an additive correction

For `d≥7`, set `c=3d−2`; the core budget is six. Zero- or one-hub cores have odd count greater than `c`. A two-hub core retains at most four supports, so the largest odd count at most `c` is exactly

\[
 |U|_{\max}=2d+4,\qquad c-|U|_{\max}=d-6=\Delta(T_d)-7.
\]

Any universal fallback `|U|≥c−f(Δ)` must therefore satisfy

\[
 \boxed{f(\Delta)\ge\Delta-7\quad\text{for every }\Delta\ge8.}
\]

This is a necessary bound, not a sufficient additive theorem. No universal sufficient `f(Δ)` is established here.

## 3. A proved stronger absorption cut remains available

Every parity kernel of a tree satisfies

\[
 \boxed{|U|+|W|=\sum_{u\in U}d_T(u).}
\]

Every edge outside `T[R]` has exactly one endpoint in `U`; these edges number `(n−1)−(|R|−1)=n−|R|`. Thus the existing kernel already obeys

\[
 |U|\ge\left\lceil\frac{2c}{\Delta(T)}\right\rceil.
\]

If `ℓ` counts leaves, put `E=Σ_v(d_T(v)−2)_+=ℓ−2`. The identity also gives `2c≤2|U|+E`, hence

\[
 |U|\ge c-\left\lfloor\frac{\ell-2}{2}\right\rfloor.
\]

Both bounds apply to every existing kernel. Use

\[
 L=\max\left\{\left\lceil2c/\Delta(T)\right\rceil,
 c-\left\lfloor(\ell-2)/2\right\rfloor\right\}.
\]

The color demand in `B` is `n−|U|≤n−L`; the demand in `A` remains at most `c`. The supplied `colored_tree_extension` therefore works with A-to-B crossdegree **`k+1−L`** instead of `k`, and B-to-A crossdegree `c`.

The separate, fully checked `TreeExactKernelBounds.lean` supplies:

* `degree_sum`, `odd_card_lower`, `odd_card_lower_excess`, and the leaf/excess identity;
* `extend_kernel_copy_of_lower`, accepting any proved `L≤|U|`;
* `isContained_of_degree_cut`, the complete density-funded conditional ES reduction with A-to-B threshold `k+1−⌈2c/Δ(T)⌉`.

The core-edge budget `k−2c`, cut-density budget, and ordinary smaller-parameter ES induction interface are unchanged. For subcubic targets the threshold is `k+1−⌈2c/3⌉`. The leaf correction is additive in the number of leaves, not a proved additive function of maximum degree alone.

The counterexample blocks the universal **exact-kernel route** to `k+1−c`; it does not refute an independent host embedding theorem with that threshold.

## 4. Positive cases and the smaller rooted obstruction

Exactness holds for `c=1,2`, the admissible endpoints `c=m,m−1` where `m` is the smaller class size, and trees with at most three leaves. It also holds when the smaller class contains no leaves, including the arbitrary-root interior version for that family. Paper proofs are retained in `TreeExactKernelPositiveCases.md`; the at-most-three-leaves and degree-two results are Lean theorems in `TreeExactKernelBounds.lean`.

The arbitrary-prescribed-root strengthening already fails on eight vertices: take `0—1—2—3`, attach two leaves to each endpoint, set `c=3`, and require `1∈R`. Both classes have size four, but the only allowed cores `{1}`, `{0,1}`, `{1,2}` have odd counts 4, 5, 2. This rooted obstruction and an unrooted exact certificate are fully proved in `TreeExactKernelRootCounter.lean`.

## 5. Verification and reproducibility

`Submission/TreeExactKernelChecks.py counterexample`:

* independently enumerates all **7,591 connected cores of size at most six** in the 44-vertex counterexample, using BFS odd-distance counts;
* verifies spectrum `[13,18]∪[20,27]`, exact DP minimum `f(19)=7`, and the `(6,18,20)` certificate;
* checks the entire closed-form profile against exact DP for `d=1…100`: **20,400 states**, maximum order 602.

Earlier exact tests found no failure among all **9,114,283 nonisomorphic trees through 22 vertices** (83,485,889 parameters) or 12,903 previously tested structured/random trees. Those families missed this obstruction. The DP was independently validated against all connected subsets on 985 trees through 12 vertices, including 11,003 rooted profiles. The structural and Lean proofs, not the tests, establish the counterexample.

```sh
python3 Submission/TreeExactKernelChecks.py counterexample
python3 Submission/TreeExactKernelChecks.py verify 12
lake env lean Submission/TreeExactKernelCounterexample.lean
lake env lean Submission/TreeExactKernelBounds.lean
lake env lean Submission/TreeExactKernelRootCounter.lean
```

Counterexample logs: `TreeExactKernelCounterexample.log` and `TreeExactKernelCounterexampleAudit.log`. Other completed checks and audits are under `Submission/TreeExactKernel*.log`. All three formal files compile with no `sorry` or extra axioms; independent import/admissibility smoke checks also pass.
