# Hall entropy closure attempt: joint heat-baths and a single-closure invariant

## Outcome and scope

**No proof of `R(Q_d)=O(2^d)` is obtained. No Ramsey constant or submitted theorem claim is made. `Submission/Spec.lean` is unchanged.**

This continues the *specific* joint-colour Hall-certificate argument in `CubeTwoColourGlobalCompletion.md`, which was read in full, including (7.5)--(7.6). The continuation gives a new proved iterative invariant, not a new sufficient conjecture:

* Nested **joint** heat-baths of the uniform-injection law have an exact entropy-production identity. All previously released variables are resampled together with the next batch. The total production is the actual fibre deficit, not that deficit plus an unaccounted dual total correlation.
* In the reverse, possibly adaptive exposure process, a nonnegative **completion-density potential** pays for the actual conditional KL loss at every step. The conditional next-batch law is completion-weighted, generally **not uniform**. Its weights retain the entire original canonical fibre.
* Signed residual constraints on rows whose last unrevealed neighbours enter the current batch give literal unary/complementary-pair cube extractions. Several disjoint such units can be priced jointly, with exact falling-factorial pool sizes. This produces the global inequality (5.4), with **no `Gamma` term**.
* There is an exact price for avoiding repeated conditioning: each labelled certificate row closes once. The common-pair price furnished by the existing clique-count lemma contributes at most `8m/d` over a whole exposure path. This is a structural calculation on the actual cube constraints, not a new bad-boundary construction. It prevents mistaking the new ledger for a completion by the old coarse catalogue comparison.

The final unresolved operation is to obtain a sufficient *closed-residual* surplus, or an actual augmentation, from the simultaneous Hall-circuit/equality information in both colours and all host partitions. The invariant does not prove that strong information coupling supplies the required residual sets, nor that weak coupling gives tensorization or a positive good-sector mass.

---

## 1. The same global countercolouring problem

Write

\[
 h=2^d,\qquad m=2^{d-1},\qquad E\dot\cup O=V(Q_d).
\]

We work with `d>=3`. The entropy identities themselves are dimension-free, and the audit also covers valid dimension-two price instances. Nothing below supplies a dimension-uniform conclusion by ignoring the smaller dimensions.

Suppose, for the contradiction attempt, that a red-blue complete host `U` has neither colour of ordinary injective `Q_d`. For **every** partition

\[
 U=A\dot\cup B,\qquad |A|=a\ge m,\quad |B|=b\ge m,
\]

and every injection `f:E -> A`, both exact list systems

\[
 L_{f,c}(y)=B\cap\bigcap_{x\in N_Q(y)}N_c(f(x))
\]

fail Hall. Use exactly the canonical minimal joint key of the input manuscript,

\[
 K(f)=(S_R,T_R,S_B,T_B),\qquad
 T_c=L_{f,c}(S_c),\quad |T_c|=|S_c|-1.
\]

Fix a partition temporarily. Let `Omega=Inj(E,A)`, let `mu` be uniform on `Omega`, and let

\[
 P_k=\{f:K(f)=k\},\quad P=\mu(\,\cdot\mid K=k),\quad
 p_k=\frac{|P_k|}{(a)_m},\quad E_k=\log\frac{(a)_m}{|P_k|}.
\]

All nonempty fibres are retained. The input's exact catalogue bound remains

\[
 \sum_kp_k E_k=H(K)\le2\log\binom{b+m}{m-1}.             \tag{1.1}
\]

For `b=3m`, `a=N-3m`, this is at most `2m log(256/27)<4.50m`. No chosen fibre is assigned the entropy of a larger family.

The results below hold separately for every host partition. Thus arbitrary-colouring existence, not a stronger fixed-cut Ramsey assertion, remains the target. The available two-colour robust-core extraction and unrestricted rematching reductions are not altered or reproved. They do not themselves estimate the quantities below.

---

## 2. Actual entropy production under nested joint injection heat-baths

For `J subset E`, let `T_J` be the following heat-bath kernel on **full injections**: leave the labels in `R=E\J` fixed, and resample all labels of `J` uniformly and injectively from the host vertices not occupied by `R`.

Define

\[
 \nu_J=P T_J.
\]

Equivalently,

\[
 \nu_J(f)=
 \frac{P(F_R=f_R)}{(a-|R|)_{|J|}},\qquad
 V_J:=D(\nu_J\Vert\mu)=\log(a)_{|R|}-H_P(F_R).          \tag{2.1}
\]

The marginal in the numerator is the **actual** marginal of `P`, including all completion multiplicities. It is not uniform on its support in general.

### Proposition 2.1 — nested heat-bath production

If `J subset J'`, put `I=J'\J` and `R'=E\J'`. Then

\[
 T_JT_{J'}=T_{J'},\qquad \nu_JT_{J'}=\nu_{J'},           \tag{2.2}
\]

and

\[
\begin{aligned}
 V_J-V_{J'}
 &=D(\nu_J\Vert\nu_{J'})\\
 &=H(\nu_{J'})-H(\nu_J)\\
 &=\log(a-|R'|)_{|I|}-H_P(F_I\mid F_{R'})\ \ge0.
\end{aligned}                                                     \tag{2.3}
\]

**Proof.** The first resampling does not change the coordinates outside `J'`; the second uniformly resamples the whole of `J'`. This proves (2.2).

Under `nu_J`, the coordinates `R'` have their original `P` marginal. Given them, `I` has law `P(F_I | F_R')`, and the remaining coordinates `J` are uniform conditional on `R'` and `I`. Under `nu_J'`, `I union J` is a uniform injection. Its `I` marginal is uniform on `(a-|R'|)_(|I|)` choices, and its subsequent `J` conditional law is precisely the preceding uniform law. Conditional KL therefore cancels the latter law and gives the last expression in (2.3). Formula (2.1) and the entropy chain rule give the same difference of potentials. Since `mu` is uniform, this difference also equals the displayed increase of Shannon entropy. QED.

For a nested chain `empty=J_0 subset ... subset J_s=E`,

\[
 \sum_{t=0}^{s-1}D(\nu_{J_t}\Vert\nu_{J_{t+1}})
   =E_k,\qquad \nu_E=\mu.                               \tag{2.4}
\]

This is actual entropy production, not a log-Sobolev inequality used backwards. It works for arbitrarily strong coupling.

**Important restriction.** A sweep that only updates each new small block once is not asserted to end at `mu`. In (2.2), the entire growing released union is refreshed each time. Nor do the resulting `nu_J` remain in the old key fibre. They are comparison laws on ordinary injections, not claimed cube embeddings or new Hall fibres. The next sections use the original fibre's exact completion counts to keep track of all its constraints.

### Relation to the missing `Gamma`

For a fixed ordered partition `I_1,...,I_t` of `E`, reversing the above erasure order gives production terms

\[
 \delta_j=\log(a-|I_{<j}|)_{|I_j|}
                 -H_P(F_{I_j}\mid F_{I_{<j}}),\qquad
 \sum_j\delta_j=E_k.                                    \tag{2.5}
\]

For equal star sizes, subtracting (2.5) from the input's all-other-blocks-pinned deficits gives **exactly**

\[
 \sum_jD^{\rm all}_{k,j}-\sum_j\delta_j
 =\sum_j I_P(F_{I_j};F_{I_{>j}}\mid F_{I_{<j}})-\Xi
 =\Gamma_k-\Xi.                                        \tag{2.6}
\]

Thus no estimate `Gamma=O(H(K))` has been proved or used. We change both the conditional laws and the residual tests we are allowed to charge. The old local penalties in (7.6) cannot simply be substituted into (2.5).

---

## 3. An adaptive, finite completion-density invariant

The reverse formulation permits a nonanticipating choice of joint batches and avoids any ambiguity about constraints after a heat-bath.

At a positive node, a set `P_0 subset E` has been exposed as an actual injection `g:P_0 -> A`. Let

\[
 q=|P_0|,\quad n=a-q,\quad r=m-q,
\]

and retain the **whole** completion family

\[
 \mathcal F_g=\{f\in P_k:f|_{P_0}=g\},\qquad w_g=|\mathcal F_g|>0.
\]

Set

\[
 \rho_g=\frac{w_g}{(n)_r},\qquad
 \mathcal V_g=-\log\rho_g=\log(n)_r-\log w_g\ge0.       \tag{3.1}
\]

Choose a nonempty `I subset E\P_0`, of size `s`. The choice can depend on the host, `k`, and the entire exposed history, including its deterministically computed completion family. It **cannot** depend on which still-hidden completion was sampled. Unions of several remaining star atoms are allowed; the identity also allows finer or other batches.

For an injection `z:I -> A\im(g)`, let `w_(g,z)` be its number of completions in `F_g`. The next-batch law is

\[
 \pi_g(z)=\frac{w_{g,z}}{w_g},\qquad
 u_g(z)=\frac1{(n)_s},\qquad
 \delta_g=D(\pi_g\Vert u_g)=\log(n)_s-H(\pi_g).          \tag{3.2}
\]

Only `w_(g,z)>0` branches are used under `P`. All sums involving `V_(g,z)` below run over these positive-probability children. The reference law `u_g` includes **every** actual unused-pool injection, including branches with zero completions.

### Proposition 3.1 — exact potential recursion

\[
 \boxed{\quad
 \mathcal V_g=\delta_g+
              \sum_z\pi_g(z)\mathcal V_{g,z}.
 \quad}                                                 \tag{3.3}
\]

**Proof.** The exact density ratio is

\[
 \frac{\pi_g(z)}{u_g(z)}=\frac{\rho_{g,z}}{\rho_g},
 \quad\text{since}\quad (n)_r=(n)_s(n-s)_{r-s}.
\]

Take logarithms and average with the **true** probabilities `pi_g`. This proves (3.3). Alternatively, use `sum pi_g(z) log w_(g,z)=log w_g-H(pi_g)`. QED.

Every step exposes at least one label. Hence the process terminates in at most `m` steps. At a leaf, `w=1`, `r=0`, and `V=0`. Consequently

\[
 \mathbb E_{P}\sum_{g\text{ visited}}\delta_g=E_k.        \tag{3.4}
\]

This remains true for adaptive batch sizes and choices. There is no schedule-information tax because, for fixed `k`, the schedule is a deterministic function of already observed values. An anticipatory choice would not be covered by this proof.

All original row requirements, equality `T_c=L(S_c)`, minimality, and the canonical key-selection rule remain inside `w_g`. The argument never replaces `F_g` by a relaxed residual system. Residual systems below are used only for **upper bounds** on its next-batch support.

---

## 4. Exact closed residuals and joint positive prices

### 4.1 Which old clauses can be used at a prefix?

A labelled certificate row `(c,y)`, `y in S_c`, **closes at this step** if

\[
 \varnothing\ne J_y:=N_Q(y)\cap I,\qquad
 N_Q(y)\subseteq P_0\cup I.                             \tag{4.1}
\]

It has no neighbours in the still-hidden labels beyond `I`. Define its observed residual

\[
 K^g_{y,c}=(B\setminus T_c)\cap
          \bigcap_{x\in N_Q(y)\cap P_0}N_c(g(x)).        \tag{4.2}
\]

For every positive-probability next assignment `z`, and every completion `f` of it,

\[
 L_{f,c}(y)\setminus T_c
 =K^g_{y,c}\cap\bigcap_{x\in J_y}N_c(z(x))
 =\varnothing.                                         \tag{4.3}
\]

This is the input's signed residual equality on a different, rigorously specified domain. Rows not yet closed may constrain `pi_g` strongly through completion counts; we do **not** pretend their outside images are pinned.

### 4.2 Opposite-colour interactions in a genuine joint batch

Suppose a candidate `v` belongs to residuals of opposite-colour closed rows `y,z`. Then no common neighbour of `y,z` is in `P_0`, because its pinned image would be required to have both colours to `v`. Therefore

\[
 N_Q(y)\cap N_Q(z)\subseteq I.                           \tag{4.4}
\]

If the two rows share a moving variable and `y!=z`, the cube intersection formula says their **two** common even neighbours must both be in `I`. If `y=z`, the whole neighbourhood must be in `I`.

For a single star atom, distinct non-root rows cannot share its two-variable pair; a repeated non-root row has a pinned neighbour when `d>=3`. Thus (4.4) recovers the input's opposite-sign, non-root support disjointness. Joint batches can create opposite-sign interactions, but only when they release the full common-neighbour square (or the entire repeated row). This is a compatibility restriction, **not** an alternating 2-SAT propagation theorem. It gives no product decomposition across different candidates.

### 4.3 Unary units: actual cubes, then a support cap

For `i in I` and a desired colour `c`, set

\[
 W^g_{i,c}=\bigcup_{\substack{y\in S_{\bar c}\text{ closes}\\J_y=\{i\}}}
                         K^g_{y,\bar c}.                 \tag{4.5}
\]

Every possible `z(i)` is colour-`c` complete to `W^g_(i,c)`. If this set has size at least `m`, and at least `m` unused host vertices are colour-`c` complete to it, inject the two cube parity classes into those two sets. **All `dm` required source edges are then checked**, and the host images are distinct.

In a countercolouring, therefore, at most `m-1` unused host vertices are available at this position. After any other positions in a joint batch have been assigned, this remains a cap of `m-1`, not a statement about an independent coordinate marginal.

### 4.4 Common-pair units on a subset of a joint batch

Let `J subset I`, `2<=|J|=t<=d`. Suppose that in one colour `c`, for every pair `{i,j} subset J` there is a closing row `y_ij in S_c` with

\[
 N_Q(y_{ij})\cap I=\{i,j\},\qquad
 K\subseteq K^g_{y_{ij},c},\quad k:=|K|\ge m.            \tag{4.6}
\]

Star subsets are a natural source of such units. Condition (4.6) must be checked **after** choosing the whole joint batch: an additional moving neighbour outside the unit would invalidate it.

Put

\[
 D_* =\left\lfloor\frac{k-m}{d}\right\rfloor,\qquad
 q_* =\left\lfloor\frac{k}{D_*+1}\right\rfloor.
\]

If at least `m` currently available host vertices have colour-`c` degree at most `D_*` into `K`, map the even class to them. Each odd row then has at least `k-dD_*>=m` complementary-colour candidates in `K`, so greedy distinct assignment gives a literal colour-`bar(c)` cube.

Otherwise the number `g` of these low-degree host vertices is at most `m-1`. Exactly as in the input's Lemma 6.1, on an available pool of size `v` the number of possible injective assignments on this unit is at most

\[
 U(v,t,g,q_*)=
 \sum_{j=0}^{t}\binom tj(g)_{t-j}(v-g)^j\frac{(q_*)_j}{q_*^j}.       \tag{4.7}
\]

The proof does not require `t=ell`: an allowed unit is a clique in the graph of disjoint colour-`c` neighbourhoods in `K`; on the high-degree hosts its clique number is at most `q_*`. Apply the input's ordered-clique bound, choose the high-degree positions, and sum. Host collisions within the unit are forbidden; tests dropped between low- and high-degree parts only enlarge the count.

A history-uniform cap is the explicit positive rational number

\[
 C_{\rm pair}(v,t;m,q_*)=
 \min\left\{(v)_t,\ \max_{0\le g\le\min(v,m-1)}U(v,t,g,q_*)\right\}.
                                                               \tag{4.8}
\]

Here `v>=t`. Also `m>=d` and `d(D_*+1)<=k-m+d<=k`, so `q_*>=d>=t`. Positivity follows, for example, from the `g=0` term. The cap works after arbitrary earlier choices within the batch: deleting used host values does not enlarge the low-degree set past `m-1`.

### Proposition 4.1 — joint-unit price without a joint finite-population loss

At a node choose disjoint unary and common-pair units `J_1,...,J_l subset I`, all satisfying the **closed** residual tests above. Fix their order from the exposed data. Let

\[
 t_j=|J_j|,\qquad v_j=n-\sum_{i<j}t_i,
\]

and take

\[
 C_j=\begin{cases}
       \min(v_j,m-1),&J_j\text{ unary},\\
       C_{\rm pair}(v_j,t_j;m,q_j),&J_j\text{ a pair unit}.
     \end{cases}
\]

Then in a countercolouring

\[
 \boxed{\quad
 \delta_g\ \ge\ \Lambda_g:=
          \sum_{j=1}^{l}\log\frac{(v_j)_{t_j}}{C_j}\ \ge0.
 \quad}                                                 \tag{4.9}
\]

**Proof.** Expose the units in this order. For any values of previous units, the next has at most `C_j` injective choices. All unpriced positions together have at most

\[
 (n-\sum_jt_j)_{s-\sum_jt_j}
\]

choices. Hence the support of the actual completion-weighted `pi_g` has size at most the product of these bounds. Entropy is at most the logarithm of support size, whether or not the law is uniform. Divide that product into `(n)_s` and use the exact falling-factorial factorization. This proves (4.9). QED.

This counts several star units in a **single** actual injection batch; neither their host values nor their conditional laws have been made independent. There is no extra `beta(n,s)` for the whole joint batch. Finite-population effects internal to (4.7) are still present in (4.8), rather than discarded.

One may additionally use any correctly proved upper support count from the other closing rows, including high-arity roots and both signs. Nothing in the recursion presumes unary/common-pair units exhaust the information in `pi_g`.

---

## 5. The new global ledger and its terminating invariant

For any nonanticipating policy, retain all completion counts as in Section 3 and choose the observed disjoint units at each node. Define, along a path,

\[
 M_t=\mathcal V_{g_t}+\sum_{j<t}\Lambda_{g_j}.            \tag{5.1}
\]

Equations (3.3) and (4.9) prove

\[
 \mathbb E_P[M_{t+1}\mid g_t]\le M_t.                    \tag{5.2}
\]

This is a **finite supermartingale**, with a nonnegative remaining potential and at most `m` steps. Equivalently, repeated substitution, without any optional-stopping theorem, gives

\[
 \mathbb E_{F\mid K=k}\sum_{g\text{ visited}}\Lambda_g
 \le E_k.                                               \tag{5.3}
\]

Averaging over the actual key probabilities yields the promised replacement for (7.6):

\[
 \boxed{\quad
 \sum_kp_k\,
 \mathbb E_{F\mid K=k}\sum_{g\text{ visited}}\Lambda_g
 \le H(K)
 \le2\log\binom{b+m}{m-1}.
 \quad}                                                 \tag{5.4}
\]

There is **no `Gamma` or discarded `Xi`** here. The different falling-factorial baselines telescope exactly. There is also no covert maximization over unavailable outside assignments: every `g` is a positive-probability prefix in its own actual fibre.

More explicitly, let `epsilon_g=delta_g-Lambda_g>=0`. The complete ledger is

\[
 H(K)=\sum_kp_k\,\mathbb E_{F\mid K=k}\sum_g\Lambda_g
     +\sum_kp_k\,\mathbb E_{F\mid K=k}\sum_g\epsilon_g.
\]

The second term is unpriced **actual entropy production**. No claim is made that the observed units exhaust it. Other signed constraints and canonical-fibre restrictions remain in the completion weights, rather than being erased from the counting problem.

An explicit policy is available without an existence assumption: at each node enumerate the nonempty unions of remaining star atoms, the qualifying disjoint residual units, and their orders; select a maximum present price, with deterministic ties, and expose that batch. This terminates and obeys (5.1). It is a mathematical finite procedure, not asserted to be computationally efficient or to find a cube.

More generally, an exact finite dynamic program maximizes accumulated observed price: a leaf has value zero; at a node maximize

\[
 \Lambda_g+\sum_z\frac{w_{g,z}}{w_g}\,B(g,z)              \tag{5.5}
\]

over the allowed nonempty batches and observed unit packings. Induction using (3.3) proves `B(g)<=V_g`. There are no separately reselected host prices whose common monotonicity is being assumed. The single potential (3.1) pays every step.

Every expression in (5.4) is defined for each host partition. It remains valid after optimizing over **all** partitions or the two colour names. The inequalities do not provide a cube merely because such an optimization exists.

---

## 6. Exactly what the joint erasure loses: a proved row and pair-price budget

The following quantifies the limitation of this continuation without inventing another diagnostic colouring.

### Proposition 6.1 — each labelled row is available at one closure time

On any complete path, every `(c,y)` with `y in S_c` closes at precisely the step exposing its last unexposed neighbour(s). If at each step disjoint units are priced as in Proposition 4.1, and `u` is the total number of priced unary positions, then

\[
 \boxed{\quad
 u+\sum_{\text{pair units }J}\binom{|J|}{2}
 \le |S_R|+|S_B|\le2m.
 \quad}                                                 \tag{6.1}
\]

**Proof.** A counted unary position has a nonempty union in (4.5), so assign it one contributing labelled row. A pair unit consumes one closing labelled row for each of its pairs. These rows are distinct because their moving supports differ. Disjoint units cannot consume the same row: a nonempty support cannot belong to two disjoint units. Across steps a row closes once. This injects the items on the left into the labelled certificate rows. QED.

This statement does **not** discard rows from the completion counts. It bounds how often the particular *direct observed tests* of Section 4 may be used without returning to all-other-blocks conditioning.

### Proposition 6.2 — the existing clique-count price has a dimension-dependent ceiling

For every common-pair unit of size `2<=t<=d`,

\[
 \log\frac{(v)_t}{C_{\rm pair}(v,t;m,q_*)}
 \le -\log\frac{(q_*)_t}{q_*^t}
 \le\frac{t^2}{d}
 \le\frac4d\binom t2.                                  \tag{6.2}
\]

**Proof.** For `q=q_*>=d>=t`, the numbers `f_j=(q)_j/q^j` decrease with `j`. For **every** possible actual `g`,

\[
\begin{aligned}
 U(v,t,g,q)
 &\ge f_t\sum_{j=0}^t\binom tj(g)_{t-j}(v-g)^j\\
 &\ge f_t\sum_{j=0}^t\binom tj(g)_{t-j}(v-g)_j
   =f_t(v)_t.
\end{aligned}
\]

The last equality is the falling-factorial Vandermonde identity. Thus (4.8) is also at least `f_t(v)_t`, proving the first inequality. In particular, merely using the actual `g` in (4.7), rather than maximizing it, does not remove this ceiling.

Since `q>=d`, monotonicity and comparison with the integral give

\[
\begin{aligned}
 -\log\frac{(q)_t}{q^t}
 &\le\sum_{i=0}^{t-1}-\log(1-i/d)\\
 &\le d\int_0^{t/d}-\log(1-x)\,dx\\
 &=d\sum_{j\ge2}\frac{(t/d)^j}{j(j-1)}
 \le\frac{t^2}{d}.
\end{aligned}
\]

The integral is finite also at `t=d`; the series then sums to one after removing the factor `d`. The final inequality in (6.2) follows from `t>=2`. QED.

Combining (6.1)--(6.2) yields the pathwise bound

\[
 \boxed{\quad
 \sum_{\text{pair units}}\text{price}
 \le\frac4d(|S_R|+|S_B|)\le\frac{8m}{d}.
 \quad}                                                 \tag{6.3}
\]

It bounds the price supplied by the **universal clique-count expression**, not the actual conditional KL losses and not every possible sharper use of pair data.

There is a further direct geometric limitation. If `d=ell>=4` is a power of two and all batches are unions of whole atoms of one star partition, every row meets an atom in zero, two, or `d` variables. It therefore never has a singleton moving support at closure. In that regime the unary contribution in (6.1) is identically zero. Refining a batch or changing the available geometry may create unary rows, but their large residual-set sizes still require proof.

**Interpretation, with the inequality directions kept straight.** An `O(m/d)` ceiling cannot by itself force a strict excess over the input's `4.50m` *upper allowance* by taking the host constant larger. This does not say the actual `H(K)` is at least a constant times `m`; it may be much smaller. Nor does it rule out sharper signed counts, useful root constraints, or Hall-tree information. It shows exactly why erasing `Gamma` and reusing the old pair lemma is not already a completion.

---

## 7. The precise unresolved final step

The proved chain is now

\[
 \text{all-colour/all-partition Hall failure}
 \ \Longrightarrow\ \text{actual joint fibres and (1.1)}
 \ \Longrightarrow\ \text{(3.3), (4.9), and (5.4)}.
\]

A literal cube is produced whenever one of the unary or low-degree complementary extraction branches fires. Otherwise the supermartingale invariant holds, with every source edge and every canonical-fibre completion still accounted for.

What is **not proved** is a way to make the expected accumulated price in (5.4) exceed the actual `H(K)`, or to augment to a good injection by another mechanism. The missing structural use can be located more narrowly than in the original ledger:

1. **Supply at a nonanticipating prefix.** The old all-other-blocks-pinned residual sets need not be observed residuals at the closure step. One must obtain sufficiently many large sets (4.5), or stronger usable joint signed constraints, with the remaining neighbours actually exposed. Equations (6.1)--(6.3) quantify the amount the existing common-pair bound can contribute in a one-pass policy.
2. **Unused exact Hall information.** Equality `T_c=L(S_c)`, minimality, and the Hall-circuit tree remain in the weights `w_g`; the direct prices used so far exploit only `L(S_c) subset T_c`. No argument turns the positive common-neighbour incidences of the tree into additional expected price or an improving injection. Conditioning on an injection-dependent tree would require its real information cost.
3. **Joint signed coupling.** Equation (4.4) identifies where opposite-colour interactions may actually appear after coarsening. Neither a strong-coupling-to-common-residual implication nor an approximate tensorization bound follows from it. The actual host vertex must realize all candidate bits simultaneously. There is no LLL good-sector construction here.

These are a record of the remaining proof operations, **not hypotheses being added to Erdős181 or proposed sufficient conjectures**. The robust-core condition has not been projected into them, and no forbidden low-waste cut has been obtained. Global optimization over partitions, fibres, or price policies does not establish the strict surplus on its own.

The improvement over (7.6) is a valid **different ledger with a terminating invariant**: conditional information is paid by actual nested injection entropy production, rather than bounded by ordinary key entropy or dropped. Its accompanying row-budget theorem also explains why that improvement alone does not settle the problem.

---

## 8. Exact audit and file integrity

Run from `/workspace/leanproject`:

```sh
python3 -u Submission/check_cube_hall_entropy_closure.py
```

Output is saved in `Submission/CubeHallEntropyClosureVerification.txt`.

The audit uses **integer and rational arithmetic**, including entropy checks. Each logarithmic expression is represented by its rational coefficients on prime logarithms. Identities are equality of these vectors; inequalities tested by the program clear coefficient denominators and compare integer products. It does not use floating-point entropy tolerances.

Recorded checks include:

* **405** complete nested-erasure chains and **771** exact joint heat-bath production identities, including equality with both KL to the next heat-bath law and actual Shannon entropy increase; **405** additional exact comparisons with the old `Gamma-Xi` ledger;
* **584** actual bipartite host colourings: all `2^9` cross-colour relations in the smallest range, and 72 further dimension-three relations;
* **8,874** exact adaptive potential recursions and joint-unit count/entropy-price bounds, with **9,264** complete certificate-row schedules; these include **1,027** multi-atom reveal nodes and **362** nonuniform completion-weighted next-batch laws;
* **26,737** exact signed closed-row residual equalities, **406** observed unary units, and **2,070** observed common-pair units;
* **56,112** joint-batch opposite-sign intersection checks through dimension eight, **1,448** single-star non-root disjointness checks, and **1,042** further square-closure checks in the actual prefix fibres;
* **41,261** exact joint-injection counts for two pair units, from all `2^16` relations on `4+4` host vertices, and **1,215** exact pair-price ceiling inequalities;
* **24,395** literal unary/complementary cube extractions, checking every required edge and distinctness in the two host pools.

The whole-cover checks include a `GOOD` key whenever an injection already extends in either colour. They check **584** key-entropy identities without pretending those finite hosts are global countercolourings. The asymptotic no-cube implication and a sufficient residual surplus are neither assumed nor tested. The analytic `t^2/d` integral estimate is proved in Section 6; the executable's corresponding ceiling tests check its preceding exact rational inequality.

No Lean files were edited. `Submission/Spec.lean` retains SHA-256

```
9cb89c42b7983ce8600b21cf6ffe9861fee7d6baca58206d9fa2d51c0636203b
```

**Final status:** a new exact joint-resampling/closed-residual supermartingale and its quantitative row budget are proved and audited. A global cube augmentation or a sufficient entropy surplus, and hence the requested Ramsey bound, remain unresolved.
