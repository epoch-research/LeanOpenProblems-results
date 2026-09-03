# A deterministic capacity-preserving anchor batch lemma

## Status

This is an auxiliary paper lemma, not a Lean proof of the Ramsey conjecture. It does not establish the hypotheses needed to split the entire remaining anchor class. `Submission/Spec.lean` is unchanged.

The argument was obtained in the focused anchor-reconfiguration investigation and independently checked below. A further proposed punctured-target construction in the read-only agent's truncated report has **not** been audited and is not used here.

## Setup

Let `P` be the adjacency matrix of a bipartite host with disjoint parts `A,B`, both of size `N`. Suppose

\[
\|P-J/2\|_{\mathrm{op}}\le K\sqrt N.
\]

Let `H` be any bipartite target with parts `X,Y`; the lemma does not need cube geometry. Choose an anchor `b_* in B`, a row pool `A_0 subset N_P(b_*)`, and an injection

\[
g:J\longrightarrow B\setminus\{b_*\},\qquad J\subseteq Y.
\]

For every `x in X`, put

\[
D_x=A_0\cap\bigcap_{y\in J\cap N_H(x)}N_P(g(y)),
\]

and assume these domains are nonempty. Let `Z` be a nonempty subset of `Y\J` and define

\[
r_x=|N_H(x)\cap Z|.
\]

Set

\[
\Gamma_Z=\max_{a\in A_0}
 \sum_{x:a\in D_x}\frac{4^{r_x}}{|D_x|},
\]

\[
\Lambda_Z=16K^2N\max_{y\in Z}
 \sum_{x\in N_H(y)}\frac{4^{r_x-1}}{|D_x|}.
\]

The exponent in the second expression is nonnegative whenever a term is present.

## Theorem

If

\[
\Gamma_Z\le1,\qquad \Lambda_Z<N-|J|-|Z|,
\tag{1}
\]

then `g` extends to an injection of `J union Z` into `B\{b_*}`, and all of `X` can be injected into `A_0` respecting every edge to this extended odd image. Moreover the odd labels of `Z` can be added one at a time, and at every prefix all of `X` has an actual simultaneous injective matching in its current domains.

Mapping the remaining labels of `Y` to `b_*` gives a full homomorphism whose only possible collisions are at the anchor. If at most one label remains there, this is an actual injection of `H`.

### 1. A bound valid for every adaptive domain

For any nonempty `D subset A`, put `u=1_D`. The spectral assumption gives

\[
\sum_{b\in B}\left(|N_P(b)\cap D|-|D|/2\right)^2
 =\|(P-J/2)^T u\|_2^2\le K^2N|D|.
\]

Consequently

\[
\#\{b:|N_P(b)\cap D|<|D|/4\}
 \le\frac{16K^2N}{|D|}.
\tag{2}
\]

This is deterministic and quantified over **every** set `D`. In particular it remains valid for domains produced by the previous choices in an adaptive construction.

### 2. Choosing genuinely unused odd images

Order `Z` arbitrarily. After a prefix has been embedded, let `k_x` be the number of embedded labels of that prefix adjacent to `x`, and let `D'_x` be its actual remaining domain. Maintain

\[
D'_x\subseteq D_x,\qquad |D'_x|\ge4^{-k_x}|D_x|.
\tag{3}
\]

For the next odd label `y`, (2) and a union bound show that at most

\[
16K^2N\sum_{x\in N_H(y)}\frac1{|D'_x|}
 \le16K^2N\sum_{x\in N_H(y)}\frac{4^{r_x-1}}{|D_x|}
 \le\Lambda_Z
\]

columns retain less than one quarter of any affected domain. The middle bound uses `k_x <= r_x-1` for these affected labels, since `y` itself has not yet been assigned.

At this step the old images, the previous new images, and the anchor exclude at most `|J|+|Z|` columns in total. By (1), some column is neither excluded nor bad. Assign it to `y` and intersect every affected domain with its neighborhood. This preserves (3), does not reuse an image, and avoids the anchor.

### 3. Simultaneous actual even-side matchings

At any prefix and every `a in A_0`, (3) yields

\[
\sum_{x:a\in D'_x}\frac1{|D'_x|}
 \le\sum_{x:a\in D_x}\frac{4^{k_x}}{|D_x|}
 \le\Gamma_Z\le1.
\tag{4}
\]

For any `S subset X`, sum these fractional weights over the union of the **current** domains:

\[
|S|=\sum_{x\in S}\sum_{a\in D'_x}\frac1{|D'_x|}
 \le\left|\bigcup_{x\in S}D'_x\right|.
\]

Thus Hall's condition holds for this single, already chosen domain system. Hall supplies one injection of all even labels into their current domains. The entire matching may change between prefixes; no even image is frozen unnecessarily. This proves the theorem.

## Arbitrary reconfiguration batches

Given an old separated set `J_old`, choose any batch `Z` of odd labels and freeze only

\[
J=J_{\mathrm{old}}\setminus Z.
\]

Define the domains using that frozen restriction. If (1) holds, all of `Z` can be reassigned and the number of separated labels increases by exactly

\[
|Z\setminus J_{\mathrm{old}}|.
\]

Old images belonging to `Z` have been freed and are not charged as occupied resources. All even images may change.

## A coarser sufficient criterion

If

\[
|D_x|\ge L,\quad
\max_a\sum_{x:a\in D_x}|D_x|^{-1}\le\rho,\quad
r_x\le s,
\]

and every odd target degree is at most `d`, it suffices that

\[
4^s\rho\le1,\qquad
\frac{16K^2N4^{s-1}d}{L}<N-|J|-|Z|.
\]

## Remaining endpoint

For the cube, the result is a genuine capacitated augmentation criterion. It is **not** a proof that its two hypotheses hold for a batch containing all remaining anchored labels. Repeated application is not automatic: domain restriction can raise the normalized column loads in (4), and the reciprocal-domain sum can become too large. Neither an unconditioned common-neighborhood estimate nor a convex combination of good partial states supplies the missing renewal of these actual capacities.
