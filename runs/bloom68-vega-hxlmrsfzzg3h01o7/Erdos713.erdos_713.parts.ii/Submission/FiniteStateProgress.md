# New progress: a finite-state coding obstruction, not a counterexample

## Status and scope

**No counterexample to the target was found.** There is no explicit fixed
ordinary bipartite H with a proved irrational extremal exponent here, and no
claimed global extremal upper bound or exact all-n leading constant for such
an H. `Submission/Spec.lean` and all pre-existing submission files are
unchanged. Neither the asserted theorem nor its placeholder disproof is
imported or used.

The new result rules out a broader recursive/coding mechanism than fixed
coordinatewise tensor powers: **arbitrary fixed synchronous finite-state
adjacency rules on pairs of words**, including state-dependent transitions
and finite memory across coordinates. This is new progress in this workspace;
no claim of priority over the literature is made.

The local corpus distinguishes the forward conjecture from inverse
realizability. For example, `/corpus/src/2007.02975/turan_exponent.tex`, lines
11–27, states the exact-positive-constant forward assertion as a conjecture,
then separately discusses the Bukh–Conlon finite-family Theta result and
single-graph rational realizability. It does not supply a disproof.

## 1. Construction class and the new theorem

Fix finite nonempty alphabets X,Y of sizes a,b and a deterministic automaton
M with s>=1 states, initial state q0, accepting states F, and transition
function on X x Y. For each k, form the **ordinary bipartite simple graph**
G_k with disjoint vertex classes X^k and Y^k. The pair (x,y) is an edge iff M
accepts their synchronously zipped word. Extra nonedges or labels are not
part of the forbidden relation.

Let H be any fixed finite bipartite graph. If every G_k is ordinary H-free,
then, for every k>=0,

    e(G_k) <= (a^k+b^k) P_s(k),

    P_s(k) = sum_{r=0}^{s-1} binom(k,r) s^(2r+1) (ab)^r,

where binom(k,r)=0 for r>k. In particular,

    e(G_k) <= C (k+1)^(s-1) v(G_k),
    C = s^(2s) (ab)^(s-1).

If max(a,b)>=2, then

    e(G_k) = O(v(G_k) (log v(G_k))^(s-1)).

Consequently, for **every** alpha>1,

    e(G_k) / v(G_k)^alpha -> 0.

Thus this construction class cannot even supply the requested superlinear
power lower construction, much less prove an extremal asymptotic. The theorem
does NOT say that all ordinary H-free graphs admit such an automaton.

### Quantitative finite certificate

There is an effective alternative. Either the component condition used in
this bound holds, or the automaton pumps ordinary K_(t,t) copies, for every
t>=1, at a word length at most

    3(s-1) + (4s^2-2) ceil(log_2 t).

This is a genuine ordinary injective copy. If H has h vertices, one may take
t=h; H embeds in K_(h,h), including its isolated vertices.

Absence of this pumping certificate is **not** equivalent to H-freeness.
It certifies the counting bound, not avoidance. This distinction is important
both in the proof and in the executable checker.

## 2. Complete proof of the general counting theorem

### 2.1 Collisions and biclique pumping

A *left collision at q* consists of two closed paired words u0,u1 from q
to q with equal Y projections and distinct X projections. They necessarily
have the same positive length. A *right collision* is the symmetric notion.

Suppose an accepting path can visit a left-collision state p and then a
right-collision state q. Fix a word A from q0 to p, B from p to q, and C from
q to an accepting state. For an integer m>=0, choose independently a binary
word i of length m and a binary word j of length m. The concatenation

    A u_(i1) ... u_(im) B v_(j1) ... v_(jm) C

is accepted. Its X projection depends only on i, and its Y projection depends
only on j. The 2^m X projections are distinct: the horizontal blocks have
fixed equal length and distinct X projections, so the first differing block
can be recovered. The same argument proves distinctness of the Y projections.
All lengths agree, and the vertex classes are disjoint by their sum tags.
This is an actual injective K_(2^m,2^m), not a noninjective homomorphism.
Taking subsets gives K_(t,t) when t<=2^m. The reverse order of collisions is
handled by exchanging X and Y.

All finite bipartite H occur in a sufficiently large balanced biclique,
so if every G_k is H-free no accepting path can meet both types of collision.

### 2.2 Why collision detection has bounded witnesses

For a left collision at q, use a product automaton whose states are
(p1,p2,d), with d a Boolean recording whether the X projections have already
differed. Its paired transitions read the same Y letter on both runs; their
X letters can differ. Start at (q,q,0) and seek (q,q,1). This has at most
2s^2 states. A shortest successful path therefore has length at most 2s^2-1.
It supplies the two closed words of a left collision. The other kind is
symmetric. Restricting the product to a strongly connected component detects
exactly its internal collisions.

If two appropriate collision states are connected on an accepting path,
shortest entrance, connector, and exit paths each have length at most s-1.
Repeat each pair of collision loops ceil(log_2 t) times. The displayed bound
on the K_(t,t) witness length follows. None of this assumes a graph tensor
product or closure of H-freeness under a graph operation.

### 2.3 Endpoint uniqueness within a component

Call a strongly connected component left-branching if some state in it has
a left collision, and right-branching similarly. Discard components lying
on no accepting path.

In a component that is **not** right-branching, the following holds: fixed
endpoint states p,q and a fixed X word allow at most one Y word on a path
from p to q that stays in the component. Indeed, two different Y words with
the same X word could be followed by a fixed return path q->p. The result
would be a right collision at p. Equal suffix cancellation preserves the
inequality of the Y projections. The symmetric statement holds for a
component that is not left-branching.

By the pumping argument, a component path supporting an accepting run cannot
contain both a left-branching component and a right-branching component.
Therefore every accepted paired word has either:

* no right-branching component anywhere on its run; or
* no left-branching component anywhere on its run.

Components with neither kind of branching cause no difficulty; a run
through only such components belongs to both counting classes.

### 2.4 Encoding a run by a polynomial-sized skeleton

An accepting run crosses between components at most s-1 times: it cannot
return to a component after leaving it. Suppose it makes r crossings.
Record:

1. the r crossing positions among the k letters;
2. the states just before and just after each crossing;
3. the paired letter on each crossing;
4. the final state.

There are at most

    binom(k,r) s^(2r) (ab)^r s

such records. The initial state is fixed. The record and the whole X word
uniquely determine the whole Y word for a run of the first type, by applying
endpoint uniqueness to each of its internal component segments. Thus at
most a^k words of the first type correspond to each record. For runs of the
second type, use the Y word instead, giving at most b^k choices. Their union
has at most a^k+b^k words per record; disjointness is not needed.

Summing over r proves the claimed P_s(k) bound. Since r<=s-1,

    binom(k,r) <= (k+1)^(s-1),
    s^(2r+1)(ab)^r <= s^(2s-1)(ab)^(s-1),

and there are s terms, the stated constant C follows.

Finally, with d=max(a,b)>=2, v(G_k)>=d^k, so

    e(G_k)/v(G_k)^alpha
      <= C (k+1)^(s-1) d^(-k(alpha-1)) -> 0

for alpha>1. This completes the proof, including its quantitative bound.

### 2.5 Arbitrarily chosen H-free length subsequences do not evade the result

For this extension assume H has at least one edge, as it does in the target.
Even if the original G_k are not all H-free, there exist constants C_H,D_H
(depending on M,H) such that

    G_k H-free  ==>  e(G_k) <= C_H (k+1)^D_H v(G_k).

The constants here need NOT be the C,s-1 from the unfiltered theorem.
Consequently, no arbitrarily chosen H-free subsequence of these full word
graphs has a positive superlinear-power edge asymptotic either.

Here is a complete finite-state justification. The set of k for which G_k
contains an ordinary injective H-copy is a **unary regular language**:

* Fix a proper 2-colouring of H, specifying the host side of each vertex.
  Take a finite union over all proper colourings, so component flips and
  isolated vertices are included.
* At every coordinate, read a tuple of letters, one for each vertex of H.
  Run a copy of M for every required edge of H, with the X letter first.
* For every pair of H-vertices assigned to the same side, keep a Boolean bit
  recording whether their words have differed at any coordinate so far.
  Require all these bits to be true at acceptance. Opposite sides are
  automatically distinct because of the sum tags.
* Require every edge monitor to finish in F. Do not impose ANY condition on
  nonedges of H. This recognizes exactly ordinary injective H-copies.
* Forget which letter tuple was read, retaining only its length: every
  transition now reads the same unary letter. This is a finite unary NFA.
  Determinize it and complement its accepting set. The result recognizes
  exactly the lengths for which G_k is H-free, including all small lengths.

Take the product of M with that length recognizer. Its graph G'_k is G_k
at H-free lengths, and is the empty-edge graph otherwise. Since H has an
edge, EVERY G'_k is H-free. Apply the counting theorem to this fixed product
automaton, with some finite state count S. At original H-free lengths the
edge and vertex counts agree, proving the extension with D_H=S-1. This also
shows that the H-free set of lengths is ultimately periodic, although no
periodicity assumption on a proposed subsequence was made.

This extension is a written proof, not a Lean theorem. The executable checker
implements the unary product monitor for balanced bicliques, including all
injectivity bits. For ordinary C4 it is tested against direct finite-graph
copy enumeration, and its H-free-length filter is checked for absence of
mixed collision paths. It never equates induced exclusion with ordinary
exclusion.

## 3. Fully formalized strengthening for recurrent acceptance

There is a stronger and simpler special case, completely formalized as
`recurrent_free_linear_bound` and
`recurrent_free_edges_le_states_mul_vertices`.

Assume every accepting state can return to the initial state. If every G_k
is ordinary H-free for any one fixed finite bipartite H, then one of the
following bounds holds simultaneously for all k:

    e(G_k) <= s a^k,              or
    e(G_k) <= s b^k.

In particular, e(G_k)<=s v(G_k) for every k, with no asymptotic error.
Empty accepted language is included. The hypothesis applies, for example,
after unreachable states are discarded and the live part is one recurrent
component containing the initial state. A rejecting sink need not return to
the initial state.

Proof: if there is an accepted word and both kinds of collision occur at q0,
pump the two kinds there and append the accepted word, contradicting H-freeness.
Thus at least one kind of collision is absent at q0. Suppose right collisions
are absent. For a fixed X word, map each accepted neighbouring Y word to its
final automaton state. Two different Y words with the same final state could
be followed by its return word, producing a right collision at q0. Hence
this map is injective and every left vertex has degree at most s. Sum the
left degrees to obtain e(G_k)<=s a^k. The other case is symmetric.

## 4. Lean implementation and its precise verification boundary

New file: `Submission/FiniteStateObstruction.lean`.
It does not import any other submission file.

Kernel-checked results include:

* `wordGraph_isBipartite`: an ordinary simple bipartite graph on disjoint
  finite word classes (when the alphabets are finite).
* `LoopRectangle.completeBipartiteCopy`: an actual `SimpleGraph.Copy`, with
  injectivity proved by equal-length block decoding.
* `LoopRectangle.completeBipartite_isContained`: K_(t,t) at the precise pumped
  length whenever t<=2^m.
* `LoopRectangle.not_all_bipartite_free`: rejection for every fixed finite
  ordinary bipartite H, including disconnected H and isolated vertices.
* `left_projection_unique_of_return`, `right_projection_unique_of_return`:
  the endpoint uniqueness used in the component proof.
* `not_all_free_of_collisions`, `not_all_free_of_reverse_collisions`:
  rejection in both orders along an accepting path.
* `degree_left_le_states` and the two `card_edges_le_of_no_*_collision`
  theorems: finite ordinary edge bounds in the recurrent case.
* `recurrent_free_linear_bound` and
  `recurrent_free_edges_le_states_mul_vertices`: the complete recurrent-case
  result above, including empty accepted language.

The **general SCC decomposition, product-automaton witness-length bound,
P_s(k) enumeration, and unary H-free-length filtering are written
mathematical proofs in this document,
not claimed as Lean theorems**. The two central ingredients and the complete
recurrent special case are formalized. The executable checks below supplement
the proofs; they do not replace them.

## 5. Executable certificate checker and regression test

New file: `Submission/finite_state_obstruction.py` (Python standard library
only). It computes components, detects both kinds of collision by product BFS,
returns explicit ordinary biclique vertices, and verifies every cross-edge
and all required inequalities. Its no-certificate branch reports only the
counting bound and expressly does not certify H-freeness.

A state-dependent regression fixture has states 0,1,dead and binary inputs.
In paired-letter order 00,01,10,11 its transitions are

    state 0:     0,    0,    1, dead
    state 1:     1, dead,    0,    0
    dead:     dead, dead, dead, dead

The initial state is 0 and both live states accept. Every live state has
exactly three live transitions, so e(G_k)=3^k while v(G_k)=2^(k+1). This
apparently gives the irrational exponent log_2(3) on construction sizes,
but it is emphatically **not an H-free candidate**. At state 0 use

    horizontal loops:  00 00       and 10 10,
    vertical loops:    00          and 01.

The first pair has fixed right word 00 and different left words 00,11;
the second has fixed left word 0 and different right words 0,1.
Consequently K_(2^m,2^m) occurs at length 3m. This concrete certificate is
also formalized in Lean as `Examples.contextCertificate`, with
`Examples.context_contains_K33` proving an ordinary K_(3,3) at length 6.
It is a validation fixture for the new obstruction, not a reused proposed
scrambled-cube construction.

## 6. Verification

Commands from `/workspace/leanproject`:

    lake env lean Submission/FiniteStateObstruction.lean
    python3 -m py_compile Submission/finite_state_obstruction.py
    python3 Submission/finite_state_obstruction.py --self-test

The script checks all 1,024 two-state binary DFAs (fixed initial state,
all transition tables and accepting sets), 200 seeded larger automata, and
9 fixtures. Results:

    1,233 automata checked
      925 with verified biclique-pumping certificates
      308 with no mixed accepting component path
    57,471 accepted edges checked for the skeleton-encoding injection
    20,020 dynamic-programming edge-count bounds checked

Each positive certificate is tested at t=1,2,3,5. Additional independent
fixed-loop checks verify K_(t,t) for t=2,3,5,9,17 at lengths 3,6,9,12,15.

The additional C4 length-profile tests cover five machines, compare 25
presence decisions with direct injective-copy enumeration, and verify 165
filtered edge counts. Each computed unary profile reaches a provable cycle.
All five H-free-length product automata have no mixed collision path, as
required by the subsequence argument.

Logs:

    /tmp/FiniteStateObstruction.build.log
    /tmp/FiniteStateObstruction.strict.log
    /tmp/FiniteStateObstruction.tests.log
    /tmp/FiniteStateObstruction.inspect.log

The final Lean compilation succeeds. Its printed axiom audits contain
only `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.
The original-file preservation manifest is `/tmp/FiniteStateObstruction.before.json`.

The unchanged target SHA-256 is

    539915b676ef3724fc90d170c6fa72d18c53a9289bbba9f6990a852d500c0c4d

## 7. What this does and does not settle

This excludes fixed finite-memory word adjacency as a source of superlinear
power constructions on full exponentially growing word sets. It also applies
to regular restrictions on vertex words after intersecting their recognizers
with the relation automaton: the record count may be multiplied by the
actual number of allowed left and right words, instead of a^k+b^k. In
particular, the same obstruction holds when those allowed word counts grow
exponentially along the proposed construction sizes. Merely deleting isolated
words does not evade the record argument asymptotically. If H itself has
isolated vertices, first remove them: once the allowed host has at least
v(H) vertices, any ordinary copy of the nonisolated part extends to H using
unused allowed vertices. This handles the otherwise potentially problematic
extra isolated vertices introduced by padding a restricted domain.

The unary length-filter argument also covers arbitrary H-free subsequences
of the accepted full-word graphs, not merely all-length H-free families.

It does **not** rule out unbounded-memory encodings, nonregular vertex
selection from a denser accepted graph, state spaces growing with depth,
or recursive geometries not represented by synchronous finite automata.
Nor does the absence of collisions prove ordinary H-freeness.

For the original request, all essential existence steps remain missing:

1. an explicit fixed finite ordinary bipartite H and an irrational alpha;
2. a valid H-free lower construction at exponent alpha;
3. a matching global upper bound for **every** ordinary H-free host;
4. equality of leading constants and convergence for **all** n, not just a
   geometric subsequence or Theta estimates.

No existence lemma for any of these missing steps has been invented. The
requested disproof remains unresolved.
