# Reversible insertion on unordered states

This continuation does NOT settle Erdos 773 or improve the actual Sidon
exponent. Spec.lean remains unchanged, with its sole sorry at line 17287
for 0<epsilon<1/3 and its proved eventual N^(2/3) endpoint.

## Verified counting lemma

ReversibleInsertionCapacity.lean imports only FormalConjecturesUtil and
contains no admissions. Its three principal audits use only propext,
Classical.choice, and Quot.sound. It has a built olean.

Let F be a downward-closed family of subsets of an N-element universe,
and F_k its k-element level. For k<N, level_ratio proves

  (k+1)*|F_(k+1)| <= (N-k)*|F_k|.

This is obtained from Mathlib's local LYM inequality and the inclusion of
the shadow of F_(k+1) in F_k.

Assign each next-level state T a unique parent parent(T) in F_k.
children_sum proves that the sum of all assigned child counts is exactly
|F_(k+1)|. Consequently, if F_k is nonempty and EVERY state has at least
D assigned children, uniform_branching_bound proves

  D*(k+1) <= N-k.

exists_small_branch gives a state whose assigned child count satisfies
this inequality. The parent assignment need not be surjective, and the
argument does not presume equal fiber sizes.

## Relevance and exact scope

In an ordered-state reconstruction, a deleted old root's position requires
information in addition to its numerical value. An unordered state avoids
that particular position record, but a successful insertion is not uniquely
reversible from the resulting set. A fixed unique-parent repair cannot
simply assume N available reversible choices uniformly at level k: the
verified counting bound applies to any downward-closed state family.

This is NOT a general impossibility theorem for entropy-compression
algorithms. In particular, a specially restricted reachable family might
not be downward closed, branching can vary from state to state, and an
algorithm can keep additional state or records. None of those alternatives
was shown to produce a near-linear square-Sidon set in this continuation.

Reviewing suffix deletion and interval-indexed states did not produce a
valid new entropy saving. No such informal calculation is used in a Lean
proof or claimed as an unrestricted obstruction.

## Logs and main file

  /tmp/reversible-insertion-capacity.log
  /tmp/spec-reversible-insertion-check.log

The main file recompiled without errors, retaining the expected admission
warning. Its hash is still
257d2e55d464b8ea5a35ca7f1257dc2f59e682772c2f52fa771ee4bfdf9b8940.
The exact original statement and sole import have not been changed.
No complete proof or disproof is available; no partial proof was submitted.
