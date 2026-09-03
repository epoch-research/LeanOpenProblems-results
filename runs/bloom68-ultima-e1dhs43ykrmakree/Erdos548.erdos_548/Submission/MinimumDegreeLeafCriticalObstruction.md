# The minimum-degree leaf-root candidate is false, even for a subcubic target

## Outcome

**No unrestricted Erdős–Sós closure is obtained.** The newly proposed stronger assertion fails: a full positive-density critical host can have a unique minimum-degree vertex that cannot receive **any** leaf of a low-maximum-degree target.

The construction below has `k=17`, `Delta(T)=3 <= floor(k/2)=8`, and `e(G)=8|G|+1`. It satisfies all the proper-induced-set bounds, the minimum-degree bounds, the strict post-deletion density, and the stated weighted incidence inequalities. Every leaf-deleted target embeds in `G-p`, but none has its corresponding parent in `N_G(p)`, even allowing arbitrary role changes.

**This is not an Erdős–Sós counterexample:** a full T-copy avoiding p is explicit. It refutes the proposed universal minimum-degree leaf-root/list closure, not an argument that additionally exploits genuine T-freeness. No such additional argument is established here.

## 1. Explicit host and its unique minimum-degree vertex

Take disjoint sets A and B with

    |A|=10,  |B|=40.

Let H be the complete bipartite graph on A and B. Add one vertex p, adjacent to precisely nine vertices of B. Write L for those nine vertices. There are no other edges.

Then

    n(G)=51,
    e(G)=10*40+9=409=8*51+1.

The host bipartition is `(A union {p}, B)`, of orders 11 and 40. Its degrees are

    d(p)=9,
    d(a)=40                    for a in A,
    d(b)=11                    for b in L,
    d(b)=10                    for b in B minus L.

Thus p is the **unique** minimum-degree vertex, and

    delta(G)=9=ceil(17/2),
    delta(G)<=17-2,
    Delta(G)=40>=17.

There is no alternative minimum-degree vertex available to the proposed selection rule.

## 2. Full criticality, proved for all induced vertex sets

Here `a=(k-1)/2=8`. First examine an arbitrary induced set Q in H. Put

    x=|Q intersect A|,  y=|Q intersect B|.

Its surplus is

    e_H(Q)-8|Q| = xy-8(x+y) = (x-8)y-8x.                 (1)

The full H has surplus zero. Every nonempty proper Q has surplus at most -2:

* If `x=0`, then `y>=1` and (1) is at most -8.
* If `1<=x<=8`, the coefficient of y is nonpositive, so (1) is at most `-8x<=-8`.
* If `x=9`, (1) is `y-72<=40-72=-32`.
* If `x=10`, properness forces `y<=39`, and (1) is `2y-80<=-2`.

Now let S be any nonempty proper vertex set of G.

If p is absent, S is a subset of H, so `e_G(S)<=8|S|`, including the equality case `S=V(H)`.

If p is present, put `Q=S minus {p}`. When Q is empty, the surplus is -8. Otherwise Q is a nonempty proper subset of H, and

    e_G(S)-8|S|
      = [e_H(Q)-8|Q|] + |Q intersect L| - 8
      <= -2+9-8
      = -1.

Consequently

    e(G)=8n(G)+1,
    e_G(S)<=8|S|  for every nonempty proper S.

This is full positive-density criticality, not just a minimum-degree or whole-graph density check.

It also proves, for every nonempty X in G,

    I_G(X)>=8|X|+1>8|X|,

using the complementary induced-set bound (with the empty complement handled by the whole-graph edge count).

## 3. Explicit subcubic target

Start with the path on six vertices

    u1-u2-u3-u4-u5-u6.

Subdivide each of its five edges once, introducing w1,...,w5. Add:

* two leaves at u1;
* two leaves at u6;
* one leaf at each of u2, u3, u4.

The resulting tree T has ten subdivision-path edges plus seven leaf edges, hence 17 edges and 18 vertices. Every vertex has degree at most three. In particular,

    Delta(T)=3<=floor(17/2)=8.

Its bipartition classes are

    U={u1,...,u6},                         |U|=6,
    V={w1,...,w5} union the seven leaves,  |V|=12.

All seven leaves belong to V. The original path endpoints now have degree three, so there are no leaves in U.

## 4. No choice of target leaf can map to p

An embedding of a connected tree into a bipartite graph must send each entire target bipartition class into one host bipartition class. This follows from parity along the unique target paths and does not require the copy to be induced.

If any target leaf maps to p, its whole 12-vertex class V must map into the host class `A union {p}`, which has only 11 vertices. This contradicts injectivity.

Thus there is **no** T-copy with any target leaf at p. Since p is the unique minimum-degree host vertex, both existential choices in the candidate assertion have been exhausted.

This obstruction survives every role change: it is a bipartition-capacity obstruction, not a failure of a particular local switching scheme.

## 5. The post-deletion hypotheses hold, but every desired marked near-copy fails

Deleting p leaves `H=K_(10,40)`, with

    |H|=50,
    e(H)=400 > (17-2)*50/2 = 375.

Hence the strict density required for induction on the 16-edge tree `T-ell` holds. Indeed no induction theorem is needed to verify unrooted containment here: send U into A and `V minus {ell}` into B.

For every target leaf ell, its parent belongs to U. The connected tree `T-ell` has bipartition class orders 6 and 11. If its corresponding parent were sent to any vertex of

    N_G(p)=L subset B,

its entire 11-vertex opposite class would have to map into A, which has only ten vertices. This is impossible. Therefore, for **every** leaf ell and **every** possible embedding of `T-ell` in H, the corresponding parent lies outside L.

The exact weighted incidence condition also holds. For every nonempty `X subset V(H)`, the only incident edges lost on deleting p are its edges to `X intersect L`. Thus

    I_H(X)
      = I_G(X)-|X intersect L|
      >=8|X|+1-|X intersect L|
      >8|X|-|X intersect L|.

So neither minimum-degree extremality, varying the leaf, the unrooted near-copies, nor these exact weighted inequalities can imply the proposed universal marked-copy conclusion.

The existing near-greedy nonleaf-root lemma does not apply: here `q=e(T-ell)=16`, whereas `delta(H)=10<q-1=15`. The parent is a nonleaf of `T-ell`, but that does not repair the degree deficit.

## 6. Why this does not disprove Erdős–Sós

A complete T-copy lies entirely in H: map the six vertices of U injectively to A and the twelve vertices of V injectively to B. All required cross edges exist.

Accordingly, the counterexample rules out a **stronger rooted statement**. It does not rule out deriving a contradiction from a genuinely T-free host using additional consequences of T-freeness. Such a proof would need to use more than the supplied density/minimum-degree/deletion-list hypotheses; no global argument providing that extra step is established in this attempt.

## Verification and scope

The all-subset criticality and all-leaf rooting obstructions above are analytic proofs. A direct construction check independently verified the vertex and edge counts, degree classes, target connectedness and bipartition, the identities of all seven leaves, and an explicit full T-embedding avoiding p. No host/tree search, subset enumeration, or backtracking embedding search was performed.

Only this report was added. No Lean source was edited and no partial formalization was attempted. `Submission/Spec.lean` retains SHA-256

    674e59904bc58eb7e92883f5bf20dc5070fa9ec90e1640117895768922c0c103.
