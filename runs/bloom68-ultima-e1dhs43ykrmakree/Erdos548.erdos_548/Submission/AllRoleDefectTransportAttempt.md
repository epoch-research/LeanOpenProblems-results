# All-role defect transport: a full-closing attempt, not a proof

## Outcome

**No unrestricted Erdős–Sós closing argument was obtained.** This attempt uses all target roles and permits defects at arbitrary target edges. It does not prescribe a host vertex for a leaf, parent, or other target role. The exact calculations below identify the loss term that remained uncontrolled; they do not claim that stationarity gives it a favorable sign.

No Lean source, including `Spec.lean`, was edited. No numerical Erdős–Sós search or partial formalization was performed.

## 1. The genuinely unrooted state space

Let T have k edges and q=k+1 vertices, and let G have n>=q vertices. For an injection f:V(T)->V(G), define

    D(f) = {uv in E(T): f(u)f(v) is not an edge of G},
    b(f) = |D(f)|.

All injections are allowed, not just embeddings of a particular leaf-deleted tree. Thus every role can move, and every target edge can carry a defect. T-freeness says b(f)>=1 for every state.

In a hypothetical counterexample chosen with k minimal, a copy of T minus a leaf exists by the smaller-parameter induction. Adding any unused host vertex as the missing leaf gives a state with exactly one defect: if that last edge existed, it would be a full T-copy. Thus the minimum defect count is exactly one. This use of minimality is not an assumption of the unrestricted theorem.

The original density inequality implies n>=q: if n<=k, simplicity would give e(G)<=n(n-1)/2<=n(k-1)/2.

## 2. Exact unused-vertex repair and its branch loss

Suppose D(f)={uv}. Take z outside f(V(T)) adjacent to f(v), and change only f(u) to z, obtaining g. The old defective edge uv becomes good. Every edge not incident with u remains good. Consequently

    b(g) = |{w in N_T(u) minus {v}: z is not adjacent to f(w)}|
         <= d_T(u)-1.                                      (1)

This is a legitimate shape-preserving operation on the fixed T; no target compression is involved.

* If d_T(u)=1, the operation completes T. Thus such a fresh neighbor cannot exist in a T-free graph.
* If d_T(u)=2, T-freeness and (1) force b(g)=1. The defect moves to the other incident target edge.
* If d_T(u)>=3, the operation can create more than one defect. A repair step need not stay in the minimum-defect layer.

The tree identity sum_u(d_T(u)-2)=-2 does **not** give a negative mean drift. Eligible repair rates are conditioned on the current defective edges, fresh host neighbors, and occupied images. No argument was found that balances those rates over the target roles.

## 3. Occupied-neighbor repair, including all displaced roles

Still suppose D(f)={uv}. If a neighbor z of f(v) is already occupied, write z=f(w). Then w is different from u and v. Swap the images of u and w, obtaining g. Again uv becomes good.

Put c=1 if uw is a target edge, and c=0 otherwise. The edge uw, when present, keeps its adjacency status under the swap. The only edges whose status can change are the

    d_T(u)+d_T(w)-2c

edges incident with u or w other than uw. Exactly one of them, uv, was initially bad and is now good. All edges outside this collection remain good. Hence

    b(g) <= d_T(u)+d_T(w)-2c-1.                            (2)

The extra d_T(w) term is a real occupation cost: displacing an occupied host vertex also moves its target role and can destroy that role's required adjacencies. Treating an occupied host edge as a free extension silently discards this term.

For general states and any swap, define g_count to be the number of target edges changing from bad to good, and l_count the number changing from good to bad. The exact identity is

    b(after)-b(before) = l_count-g_count.                  (3)

From a one-defect state a repairing swap has g_count=1. T-freeness therefore forces l_count>=1. If the new state also has one defect, then l_count=1 and the reverse swap is itself a repair. Accordingly, the repair graph restricted to the one-defect layer is undirected. Its stationary conservation identities cannot establish escape to a full copy: b is identically one on that layer.

## 4. An all-role, all-transposition identity

Pad T with n-q isolated target roles and extend f to a bijection pi onto V(G). Write C(pi)=k-b(pi) for the number of good target edges. Summing over every unordered transposition tau of target roles gives

    sum_tau [C(pi after tau)-C(pi)]
      = sum_{u in V(T)} d_T(u)*d_G(pi(u))
        -2(n-1)*C(pi).                                    (4)

Here isolated roles have degree zero.

Proof: fix a target edge ab and let A be its current good-edge indicator. Swapping a with each role other than a,b contributes

    d_G(pi(b))-(n-1)*A.

Swapping b instead contributes d_G(pi(a))-(n-1)*A. Swapping a with b, or swapping two other roles, does not change this edge's status. Sum over the target edges to obtain (4).

If T is absent and b(pi)=1, every transposition has C(after)<=k-1=C(pi). Therefore the valid necessary inequality is

    sum_u d_T(u)*d_G(pi(u)) <= 2(n-1)(k-1).                 (5)

This really includes every target role and all unused host positions. But its right-hand side scales with host order, rather than giving the required incident-edge budget. Neither (4) nor (5) implies the low-incidence certificate. Replacing their actual role marginals by d_G(v)/(2e(G)), or by a uniform marginal, would be an unjustified additional assumption.

## 5. Precisely what remains unproved

Let a=(k-1)/2 and assume the full critical conditions

    e(G)=a*n+eta, eta>0,
    e_G(S)<=a*|S| for every proper nonempty S.

Then for every nonzero nonnegative host potential beta, layer cake gives

    sum_{xy in E(G)} max(beta_x,beta_y)
      >= a*sum_x beta_x + eta*max_x beta_x.                (6)

The desired contradiction would be a beta derived from T-freeness with

    beta>=0, beta nonzero,
    sum_{xy in E(G)} max(beta_x,beta_y) <= a*sum_x beta_x.  (7)

Equivalently, one must derive a nonempty X with I_G(X)<=a*|X|. This was **not** derived.

In the attempted defect transport, the missing implication is a global comparison bounding the total good-edge losses in internal-role and occupied-role repairs by the incident-edge budget. Equations (1)-(3) expose those losses explicitly. Criticality controls host edges meeting sets, not whether a replacement vertex simultaneously satisfies the several adjacencies required by an internal target role. Passing to all defect layers makes those moves legitimate but supplies no bound on their losses; restricting to one defect loses the needed moves and yields only reversible, constant-defect transport.

Thus no transport with the required accounting, no low-incidence certificate, and no full T-augmentation was established. The residual low-maximum-degree case remains unresolved here. This is a failed global closing route, not a proved stronger rooted statement or an Erdős–Sós counterexample.

## Verification and preservation

Equations (1) and (2) were audited by listing every target edge whose status can change; (3) is the exact gain/loss partition; (4) was independently derived edge by edge, including the isolated roles and the endpoint transposition. Equation (5) uses actual global minimality of the defect count, not local optimality. Equation (6) integrates the critical incident-set inequalities.

`Submission/Spec.lean` has SHA-256

    674e59904bc58eb7e92883f5bf20dc5070fa9ec90e1640117895768922c0c103.
