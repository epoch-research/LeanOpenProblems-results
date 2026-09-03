# E74Parity: verified API

Status: complete. `Submission/E74Parity.lean` imports only `Submission.E74Basic`
and exports 40 theorems in namespace `E74`. The requested command succeeds with
no errors or warnings:

```sh
lake env lean -o .lake/build/lib/lean/Submission/E74Parity.olean Submission/E74Parity.lean
```

`E74ParityChecks.txt` contains the exact Lean-printed signatures of every export
and the axiom audit of every theorem. A verification file at
`/tmp/E74ParityCheck.lean` imports `E74Parity`, `E74Walk`, and `E74Bounds` together
and checks 21 usage examples; it compiled without errors or warnings. No naming
collisions with those modules were found. No `sorry`, `admit`, or custom `axiom`
occurs in `E74Parity.lean`; every theorem's axiom dependencies are contained in
`{propext, Classical.choice, Quot.sound}`.

## Main entry points and explicit argument order

The ordinary walk-label identities do not require `DecidableEq V` or finiteness.
The remaining API uses `[DecidableEq V]`, consistently with the frozen definitions.
Theorems mentioning `badEdges` use `[Fintype V]`, as that definition requires;
`exists_shortSupport` and `exists_minimalSupport` need only `[Finite V]`.

- `walkXor_append a w q`, `walkXor_reverse a w`, `walkXor_copy a w hu hv`,
  `walkXor_mapLe a hGH w`, and `walkXor_transfer a w h` are simp lemmas.
- `walkXor_congr w h` takes `h : ∀ e ∈ w.edges, a e = b e`. The labels are
  implicit and need not agree anywhere else.
- `walkXor_twist_congr w h` takes `h : ∀ e ∈ w.edges, e ∈ S ↔ e ∈ T`.
- `walkXor_eq_foldr a w` and `walkXor_eq_of_edges_eq a w q h` identify sums
  using edge lists, including multiplicities and walks in different graphs.
- `twist_of_mem h`, `twist_of_not_mem h`, `twist_eq_false_iff`, and
  `twist_eq_true_iff` simplify membership labels. They apply directly to
  `e = s(u, v)`. The imported `walkXor_nil` continues to simplify nil sums.
- `twist_badEdges p huv` states
  `twist (badEdges G p) s(u, v) = (p u ^^ p v)` for `huv : G.Adj u v`.
- `walkXor_eq_endpoints p w ha` telescopes any total label agreeing with
  endpoint XOR on graph edges.
- `walkXor_twist_badEdges p w` states
  `walkXor (twist (badEdges G p)) w = (p u ^^ p v)`.
- `walkXor_twist_badEdges_closed p w` is a simp lemma giving `false` on every
  closed walk. `shortSupport_badEdges G L p` gives
  `ShortSupport G L (badEdges G p)` for every `L`.
- `exists_minimalSupport G L : ∃ S, MinimalSupport G L S` minimizes cardinality
  using `Nat.find_spec` and `Nat.find_min'`.
- For `hS : MinimalSupport G L S`, `hS.card_le hT` compares with any short
  support, and `hS.card_le_badEdges p` gives `S.card ≤ (badEdges G p).card`.

## Certificates

```lean
exists_badEdge_not_mem_of_short_walkXor_ne_false
    (p : V → Bool) (hD : D ⊆ badEdges G p) (w : G.Walk v v)
    (hw : w.length ≤ L) (hxor : walkXor (twist D) w ≠ false) :
    ∃ e ∈ w.edges, e ∈ badEdges G p ∧ e ∉ D
```

`exists_badEdge_not_mem_of_walkXor_ne_false p hD w hxor` is the stronger
length-unrestricted closed-walk version. More generally,
`ShortSupport.exists_edge_not_mem hS hD w hw hxor` works for any short support
`S` and subset `D ⊆ S`. For nonclosed walks and arbitrary labels use
`exists_edge_of_walkXor_ne`; for nested supports use
`exists_edge_mem_sdiff_of_walkXor_twist_ne hST w hxor`.

## Restriction and pruning

For `hS : ShortSupport G L S`:

- `hS.mono_length hML` lowers the length scale.
- `hS.of_le hHG hSH` restricts to `H ≤ G` if `(S : Set (Sym2 V)) ⊆ H.edgeSet`.
- `hS.mask Z hSZ` specializes this to the masked graph; the survival hypothesis
  is `(S : Set (Sym2 V)) ⊆ (E74.mask G Z).edgeSet`.
- `hS.mask_of_disjoint_ends hSZ` instead assumes
  `Disjoint (ends S : Set V) Z`.
- `hS.congr hT hxor` replaces `S` by `T`, assuming `T` consists of graph edges
  and every short closed walk has the same twisted sum for `T` as for `S`.
- `hS.congr_edges hT hmem` needs only membership agreement on the edges of
  short closed walks.
- `hS.sdiff A hxor` proves `ShortSupport G L (S \ A)` if each such walk's
  twisted sum is unchanged. There is no need to assume `A ⊆ S`.

The optional XOR API is included:

```lean
walkXor_xor a b w :
  walkXor (fun e => a e ^^ b e) w = (walkXor a w ^^ walkXor b w)

-- Requires `open scoped symmDiff` for the notation.
walkXor_twist_xor_twist S T w :
  (walkXor (twist S) w ^^ walkXor (twist T) w) =
    walkXor (fun e => decide (e ∈ S ∆ T)) w
```

`hS.of_symmDiff hT hzero` replaces `S` by `T` if the indicator sum of `T ∆ S`
is false on every short closed walk. All sums retain repeated traversals.

## Frozen files and integration notes

No changes were made to `E74Basic.lean` or `Spec.lean`. Their SHA-256 values
before and after the work agree:

- `E74Basic.lean`: `cae69612907bdb31341dd2e04ff7b0bf398618e5bc9f9eee9d8bae77c03b3dd3`
- `Spec.lean`: `44689cfa736a0b3061406f42584d7a35e9fc26775a10cf878bf73200c73e6d38`

No unfinished proofs or outstanding correctness issues. Inside namespace
`E74.ShortSupport`, qualify the graph definition as `E74.mask` to distinguish
it from the support-restriction theorem `ShortSupport.mask`.
