# Erdős 371: calibrated entropy, a valid reversal chain rule, and an explicit prime-residue obstruction

## Result and scope

This does **not** prove Erdős 371. It gives a precise algebraic failure of the proposed information-theoretic amplification, rather than merely invoking the nonadditivity of deterministic copies.

The new conclusions are:

1. Subtracting the two known marginal information costs leaves a **signed conditional interaction information**. A three-state circulation construction makes it negative while every conditional pair has a nonzero current. The construction accommodates any specified, nonconstant, strictly positive conditional one-point laws, including admissible single-prime Dickman calibration laws.
2. There is a correct positive alternative: divergence from the symmetrized law. It removes all reflection-even information, not just marginal calibration. Its conditional chain rule is proved below.
3. Nevertheless, an explicit finite model with **independent uniform prime residues**, **exact shared pair copies on every zero-residue event**, **zero one-point calibration even conditional on the entire residue vector**, and **zero unconditioned currents** has nonzero conditioned current at every prime. Its correctly conditioned, log-prime-weighted reversal production is still **Theta(log X)** over any fixed power interval of primes. Thus that cost is not exclusively a marginal Dickman effect.
4. The missing chain-rule correction is a difference of **posterior total correlations of the prime residues**. Unconditional residue independence does not remove it. With prime 2 revealed first, all subsequent conditional reversal innovations in the model are exactly zero, even though every other prime still has the same nonzero conditioned current.

This is an obstruction to a universal entropy inequality from those properties, **not** a countersequence satisfying the full all-integer smooth-function structure. The arithmetic overlap geometry of all the pairs, and consistency across actual counting prefixes, are not built into the finite model. An entropy proof exploiting additional arithmetic structure is not ruled out.

No Lean file, especially `Submission/Spec.lean`, is edited or used as a theorem.

## 1. Frozen cutoffs and the calibration that really occurs

Fix `0<a<b<1` and write

\[
 F_X(n)=1_{P(n)\le X^a},\qquad G_X(n)=1_{P(n)\le X^b}.
\]

Encode their nested values by a three-state variable `z_X(n)`:

* state 0: `(F_X,G_X)=(1,1)`;
* state 1: `(F_X,G_X)=(0,1)`;
* state 2: `(F_X,G_X)=(0,0)`.

For every `k<=X^a` and every positive n, exactly

\[
 z_X(kn)=z_X(n).                                           \tag{1}
\]

Indeed `P(kn)=max(P(k),P(n))`, and `P(k)<=X^a`. More generally, `P(k)<=X^a` suffices even when `k>X^a`.

Let `N` be uniform on `[1,X]`, let `p<=X^a` be prime, and put `M=floor(X/p)`. Then

\[
 \mathcal L\big((z_X(N),z_X(N+p))\mid p\mid N\big)
 =\mathcal L\big(z_X(U),z_X(U+1)\big),\quad U\sim[1,M].      \tag{2}
\]

There is no dilation approximation here. The first marginal is exactly

\[
 \mu_{X,M}=\frac1M\big(\Psi(M,X^a),
       \Psi(M,X^b)-\Psi(M,X^a),\ M-\Psi(M,X^b)\big).         \tag{3}
\]

The second marginal differs by total variation at most `1/M`.

The Dickman calibration, writing `M=X^t`, is

\[
 \mu(t)=\big(\rho(t/a),\ \rho(t/b)-\rho(t/a),
                         1-\rho(t/b)\big),                \tag{4}
\]

with `rho(u)=1` for `u<=1`. Thus `p=X^theta` changes the marginal from `mu(1)` to `mu(1-theta)`, not to itself. On a compact exponent interval where the entries are positive, the usual smooth-number asymptotic is uniform. For example one can take

\[
 0<\alpha<\beta<\min(a,1-b).
\]

Prime partial summation then gives the concrete leading calibration cost

\[
 \sum_{X^\alpha<p\le X^\beta}\frac{\log p}{p}
 D\big(\mu(1-\log p/\log X)\,\|\,\mu(1)\big)
 =\log X\int_\alpha^\beta D\big(\mu(1-t)\|\mu(1)\big)\,dt
   +o(\log X).                                            \tag{5}
\]

This is positive of order `log X` whenever the calibration is nonconstant. The Bernoulli event `p|N` already incurs this leading term in its marginal mutual information: the nonzero-event complement contributes only `O(1/p^2)` when the limiting marginal stays in the interior of the simplex.

Equations (1)--(5) do **not** compare the current of the prefix `X/p` with the current of the prefix X. Such a comparison is a separate issue; none is assumed here.

## 2. Exact subtraction algebra, and a stronger repair

All information quantities below use natural logarithms. First let `A,B,R` be arbitrary finite random variables. An exact entropy expansion gives

\[
 \boxed{
 I((A,B);R)-I(A;R)-I(B;R)
       =I(A;B\mid R)-I(A;B).}                             \tag{6}
\]

The terms subtracted on the left really are the averaged marginal KL calibrations. For example,

\[
 I(A;R)=\sum_r\Pr(R=r)
                 D(\mathcal L(A\mid R=r)\|\mathcal L(A)).
\]

Consequently knowing them exactly does not make (6) nonnegative.

### 2.1 A negative residual with prescribed calibrations and nonzero current

Let `R=r` have probabilities `pi_r`, and prescribe positive equal endpoint marginals `mu_r` on three states. Suppose they are not all identical. Let

\[
 C=\begin{pmatrix}0&1&-1\\-1&0&1\\1&-1&0\end{pmatrix},
 \qquad P_r^\varepsilon=\mu_r\otimes\mu_r+\varepsilon C.     \tag{7}
\]

For sufficiently small nonzero epsilon all entries are positive. Every row and column sum of C is zero, so the prescribed marginals are unchanged. For the frozen-cutoff current test

\[
 j(i,j)=F(i)G(j)-G(i)F(j)=1_{(i,j)=(0,1)}-1_{(i,j)=(1,0)},
\]

one has `E_{P_r^epsilon} j=2 epsilon` for every r.

Put `m=sum pi_r mu_r` and `B_0=sum pi_r mu_r tensor mu_r`. At epsilon zero the right side of (6) is

\[
 -D(B_0\|m\otimes m)<0.                                   \tag{8}
\]

Strictness follows from

\[
 B_0-m\otimes m=\operatorname{Cov}(\mu_R)\ne0.
\]

Continuity of entropy proves that (6) remains negative for sufficiently small nonzero epsilon. This is not restricted to artificial uniform marginals: the `mu_r` may be the two explicitly prescribed interior marginal laws on `p|N` and `p` not dividing N, with weights `1/p` and `1-1/p`.

### 2.2 Product calibration does not commute with forgetting a residue

There is a legitimate stronger repair. Define a **consistent joint reference**

\[
 \mathsf C_{RAB}(r,i,j)=\pi_r\mu_r(i)\mu_r(j),\qquad
 \mathsf C_{AB}=\sum_r\pi_r\mu_r\otimes\mu_r=B_0.
\]

The KL chain rule gives

\[
 \boxed{
 D(P_{RAB}\|\mathsf C_{RAB})-D(P_{AB}\|\mathsf C_{AB})
 =\mathbb E_{P_{AB}}D(P_{R\mid AB}\|\mathsf C_{R\mid AB})
 \ge0.}                                                   \tag{9}
\]

This is a real positive inequality, unlike (6). But its coarse reference is the **mixture of conditional products**, not the product of the coarse marginals. In general, for a coarsening S of R,

\[
 \mathbb E(\mu_R\otimes\mu_R\mid S)
   -\mu_S\otimes\mu_S
       =\operatorname{Cov}(\mu_R\mid S).                  \tag{10}
\]

Rebuilding a product reference after every conditioning or scale change therefore changes the reference family and invalidates the proposed telescoping. Formula (10) is the exact calibration-compatibility defect.

One can keep the consistent references in (9), or go further and remove **all reflection-even information**. The next section does the latter. The prime-amplification obstruction survives that stronger repair.

## 3. A genuinely positive current-specific functional

For a pair law P let `P^T` be its transpose and `S(P)=(P+P^T)/2`. Define

\[
 \mathcal A(P)=D(P\|S(P))
             =H(S(P))-H(P),\qquad
 \mathcal K(P)=D(P\|P^T).                                  \tag{11}
\]

The first quantity is the Jensen--Shannon divergence of P and its transpose; `0<=A(P)<=log 2`. The second may be infinite, but is finite in every model used below. If `|j|<=1` is antisymmetric and `delta=E_P j`, Pinsker gives

\[
 \boxed{\mathcal A(P)\ge\delta^2/2,\qquad
        \mathcal K(P)\ge2\delta^2.}                       \tag{12}
\]

If P has equal endpoint marginal mu, there is also the exact Pythagorean identity

\[
 D(P\|\mu\otimes\mu)
   =\mathcal A(P)+D(S(P)\|\mu\otimes\mu).                 \tag{13}
\]

To prove it, `log(S(P)/(mu tensor mu))` is symmetric, so its integral against P equals its integral against `S(P)`.

Thus (6) is the sum of a reversal-information increment and a change in **symmetric pair correlation**, not solely a reversal-information increment. In (7) the latter change is exactly the negative constant in (8).

### 3.1 The correct conditional chain rule

Let Z be any finite object with a fixed involution T, and R any residue vector. Introduce an independent fair orientation bit O; observe `Y=T^O Z`, keeping R unchanged. Conditional on O the two joint laws are `L(R,Z)` and `L(R,TZ)`. Their symmetrization is the observation law. Therefore

\[
 \mathbb E_R\mathcal A(\mathcal L(Z\mid R))
       -\mathcal A(\mathcal L(Z))=I(O;R\mid Y)\ge0.         \tag{14}
\]

For an ordering `p_1,...,p_m` of prime residues, the actual additive increments are

\[
 \boxed{\Delta_i^{\mathcal A}=I(O;R_{p_i}\mid Y,R_{p_1},\ldots,R_{p_{i-1}}),
 \quad\sum_i\Delta_i^{\mathcal A}=I(O;R\mid Y)\le\log2.}   \tag{15}
\]

For KL versus transpose, write `P=L(R,Z)`, `Q=L(R,TZ)` and

\[
 K_i=D(P_{Z,R_{p_1},\ldots,R_{p_i}}
                 \|Q_{Z,R_{p_1},\ldots,R_{p_i}}).
\]

The corresponding exact increment is

\[
 \boxed{\Delta_i^{\mathcal K}=K_i-K_{i-1}
 =\mathbb E_{P_{Z,R_{<i}}}
       D(P_{R_{p_i}\mid Z,R_{<i}}\|Q_{R_{p_i}\mid Z,R_{<i}})\ge0.} \tag{16}
\]

Neither formula permits replacing the posterior conditioning by the unconditional prime law.

### 3.2 Why independent residues do not tensorize reversal information

Even if the residues are exactly independent before observation, they need not be independent conditional on Y. Let

\[
 \operatorname{TC}(R\mid V)=\sum_i H(R_{p_i}\mid V)-H(R\mid V).
\]

Expanding conditional entropies gives the exact redundancy identity

\[
 \boxed{\sum_i I(O;R_{p_i}\mid Y)-I(O;R\mid Y)
     =\operatorname{TC}(R\mid Y)
          -\operatorname{TC}(R\mid Y,O).}                 \tag{17}
\]

Unconditional independence sets `TC(R)=TC(R|O)=0`, **not** either term on the right of (17). Single-endpoint Dickman calibration says nothing that makes this difference vanish. The following model evaluates it without any marginal calibration at all.

## 4. An exact independent-prime/shared-copy model

Fix any finite set of distinct primes and `0<gamma<1`. Let `R_p` be independent and uniform on `Z/pZ`. Independently choose `U` uniform on `Z/3Z` and a sign S with

\[
 \Pr(S=+1)=(1+\gamma)/2.
\]

Define one common ordered pair W by

\[
 W=(U,U+1)\quad(S=+1),\qquad W=(U+1,U)\quad(S=-1),
\]

where addition is modulo 3. Call its law `P_gamma`. For each prime, independently conditional on the residues, choose a sign `E_p` by

\[
 \Pr(E_p=+1\mid R_p=0)=1,\qquad
 \Pr(E_p=+1\mid R_p\ne0)=\frac{p-2}{2(p-1)}.              \tag{18}
\]

Finally put

\[
 Z_p=W\quad(E_p=+1),\qquad Z_p=W^T\quad(E_p=-1),
 \qquad Z=(Z_p)_p.                                        \tag{19}
\]

The involution T transposes every coordinate pair simultaneously.

### 4.1 Exact properties

1. **Shared copies on every divisibility event:** `R_p=0` implies `Z_p=W`. If several zero residues occur, all those observed pairs are the very same W, not independent samples.
2. **Zero calibration at every one-point level:** conditional on the *whole* residue vector, each endpoint of each `Z_p` is uniform on three states. Hence every one-point marginal calibration, including its conditional-chain versions with only residues previously revealed, is exactly zero.
3. **Unconditioned reflection:** integrating out `R_p` in (18) gives `Pr(E_p=+1)=1/2`. The `E_p` are independent fair signs unconditionally. Hence the full vector Z and TZ have the same law.
4. **Persistent signed residue error:** for the cutoff current test in Section 2,

\[
 \mathbb E j(Z_p)=0,\quad
 \mathbb E(j(Z_p)\mid R_p=0)=\gamma/3,\quad
 \boxed{\mathbb E[(p1_{R_p=0}-1)j(Z_p)]=\gamma/3.}          \tag{20}
\]

In particular, the model already has vanishing unconditioned gap currents at every prime, a stronger statement than needing an average of those currents to vanish.

### 4.2 Explicit per-prime divergence and bounded joint divergence

Set

\[
 k(\gamma)=\gamma\log\frac{1+\gamma}{1-\gamma},\qquad
 \phi(\gamma)=\frac{1+\gamma}{2}\log(1+\gamma)
             +\frac{1-\gamma}{2}\log(1-\gamma).
\]

Direct calculation gives `K(P_gamma)=k(gamma)` and `A(P_gamma)=phi(gamma)`.

Conditional on `R_p=0`, the p-th pair has law `P_gamma`; conditional on any nonzero residue it has law `P_{-gamma/(p-1)}`. All other pair orientations are independent fair signs when their residues have not been exposed, so they add no reversal information to this single-residue calculation. Thus, writing `P=L(R,Z)` and `Q=L(R,TZ)`,

\[
 \boxed{d_p:=D(P_{R_p,Z}\|Q_{R_p,Z})
 =\frac{k(\gamma)}p+
       \left(1-\frac1p\right)k\left(\frac{\gamma}{p-1}\right).} \tag{21}
\]

Likewise

\[
 \boxed{a_p:=I(O;R_p\mid Y)
 =\frac{\phi(\gamma)}p+
       \left(1-\frac1p\right)\phi\left(\frac{\gamma}{p-1}\right).} \tag{22}
\]

For the **joint** law there are bounds independent of the number of primes:

\[
 \boxed{\left(1-\prod_p(1-1/p)\right)k(\gamma)
       \le D(P\|Q)\le k(\gamma),}                         \tag{23}
\]

and identically with `A(P), phi(gamma)` in place of `D(P||Q), k(gamma)`.

**Proof of (23).** For each fixed residue vector, producing all of Z is one randomized channel applied to W, and transposing the output is the same channel applied to `W^T`. Data processing bounds its divergence by `k(gamma)`. If at least one residue is zero, choose its first zero coordinate. That coordinate recovers W exactly, so reverse data processing gives equality. Average over the independent residues. The Jensen--Shannon version uses the same channel and symmetrized source. QED.

This calculation uses the actual joint law; no additivity over copies is assumed.

## 5. Log weights still cost log X after perfect marginal calibration

Take the primes in a fixed power band

\[
 \mathcal P_X=\{p:X^\alpha<p\le X^\beta\},\qquad 0<\alpha<\beta.
\]

One may impose `beta<a` if desired. Since `k(t)=O(t^2)` and `phi(t)=O(t^2)` near zero, (21)--(22) and the prime harmonic sums give

\[
 \boxed{\sum_{p\in\mathcal P_X}(\log p)d_p
       =(\beta-\alpha)k(\gamma)\log X+o(\log X),}          \tag{24}
\]

\[
 \boxed{\sum_{p\in\mathcal P_X}(\log p)a_p
       =(\beta-\alpha)\phi(\gamma)\log X+o(\log X).}       \tag{25}
\]

Here the error from the second terms of (21)--(22) is bounded by a constant times `sum_{p>X^alpha} log p/p^2=o(1)`. The leading term uses `sum log p/p=(beta-alpha)log X+o(log X)`.

It is important not to stop at this failure of single-residue additivity: **the correctly conditioned chain still has the logarithmic cost**. Mertens' prime product estimate gives

\[
 \prod_{p\in\mathcal P_X}(1-1/p)=\alpha/\beta+o(1).
\]

All weights lie between `alpha log X` and `beta log X`. From the genuine nonnegative increments (16) and the joint bounds (23), for any ordering of this prime band,

\[
 \boxed{
 \alpha(1-\alpha/\beta+o(1))k(\gamma)\log X
 \le\sum_{p\in\mathcal P_X}(\log p)\Delta_p^{\mathcal K}
 \le\beta k(\gamma)\log X.}                              \tag{26}
\]

The same assertion holds for the bounded, current-specific functional:

\[
 \boxed{
 \alpha(1-\alpha/\beta+o(1))\phi(\gamma)\log X
 \le\sum_{p\in\mathcal P_X}(\log p)\Delta_p^{\mathcal A}
 \le\beta\phi(\gamma)\log X.}                            \tag{27}
\]

Thus even after removing **all** one-point calibration, and even using the positive chain rule that discards reflection-even information, the weighted production can be Theta(log X). One global orientation signal is being assigned weights of size log X; chain-rule boundedness of its total information does not remove those weights.

### 5.1 A particularly sharp failure of an innovation lower bound

Include prime 2 and reveal it first. Equation (18) makes `E_2` a deterministic function of `R_2`. From `Z_2` and `R_2` one recovers W. Consequently

\[
 \Delta_2^{\mathcal K}=k(\gamma),\quad
 \Delta_p^{\mathcal K}=0\ (p\ne2),
\]

and similarly with phi for the orientation-entropy increments. Nevertheless every prime has conditioned current `gamma/3` and positive `d_p,a_p`.

In particular there is **no** universal inequality

\[
 \Delta_p^{\mathcal A}\ge\frac c p
   |\mathbb E(j(Z_p)\mid R_p=0)|^2                         \tag{28, false}
\]

for a fixed `c>0`, even with independent prime residues, exact copies on zero residues, zero unconditioned currents, and every individual endpoint independent of the whole residue vector. The lower bound furnished by (12) concerns the individual conditional pair law, not a new chain-rule innovation after earlier copies are seen.

### 5.2 This is not an artifact of uniform or singular marginals

Replace the source law `P_gamma` by any finite nonreversible pair law P with equal marginal mu and finite `D(P||P^T)`. Keep (18)--(19). All the copy and zero-calibration properties remain true, with mu replacing the uniform marginal. For example, for any positive three-state mu one can take the full-support law

\[
 P=\mu\otimes\mu+\varepsilon C.
\]

Writing `P_t=S(P)+t(P-P^T)/2`, formula (21) becomes

\[
 d_p=\frac{\mathcal K(P)}p+
             (1-1/p)\mathcal K(P_{-1/(p-1)}),
\]

whose second term is `O(1/p^2)`. The same power-band conclusions follow. Hence a prescribed Dickman marginal at one frozen base scale can be used. This extension does **not** claim that the model reproduces the whole varying family (4), or the overlapping values of a single arithmetic sequence; those are outside the countermodel's scope.

### 5.3 Independent orientation bits reintroduce a reflection-even copy cost

Using one independent transposition bit per pair instead of the global bit O does not repair current-specific additivity. Let W have the **reversible** law `P_0`, and take m identical copies `Z=(W,...,W)`. Every current is zero and global reversal entropy is zero. But independently transposing the m coordinates changes the conditional orientation support, for each unordered edge, from two common directions to `2^m` relative-direction patterns. Its entropy gain is exactly

\[
 H(\text{independently transposed copies})-H(Z)
       =(m-1)\log2.
\]

All individual endpoint marginals remain uniform. Thus the additive multi-bit symmetrization counts a large **reflection-even dependence among copies**, even for zero-current data. It is not a calibration-free, current-only entropy production of the original copies.

## 6. Prefix length still has no entropy monotonicity

The conditional-refinement monotonicity in (15)--(16) is not monotonicity under increasing the natural counting prefix. Here is an exact finite example, with equal marginals at every indicated prefix and no endpoint error.

Concatenate closed walks `0->1->2->0` (forward) and `0->2->1->0` (backward), starting every walk where the previous one ended. Use three forward and one backward walk, then two backward walks, then two forward walks. At edge-prefix lengths 12, 18, and 24, respectively, the pair laws are

\[
 P_{1/2},\qquad P_0,\qquad P_{1/4}.
\]

Both endpoint marginals are exactly uniform at all three lengths, whereas reversal entropy takes the values

\[
 \phi(1/2)>0,\qquad 0,\qquad\phi(1/4)>0.
\]

Thus it decreases and then increases with no one-point calibration change. More generally prefix mixing only gives the convexity inequality

\[
 \mathcal A(\lambda P+(1-\lambda)Q)
       \le\lambda\mathcal A(P)+(1-\lambda)\mathcal A(Q),
\]

not an ordering of the entropies of the two prefixes. This example is not asserted to satisfy arithmetic dilation invariance; it identifies what cannot follow from entropy algebra alone.

## 7. Consequence for the proposed all-scale route

There is a sound positive inequality, (9), if the calibrated reference is consistent under projection. There is an even more current-specific sound inequality, (15), obtained by symmetrizing the whole law. Neither gives the desired all-scale conclusion by the proposed amplification:

* subtracting individual marginal KLs gives (6), with the explicit signed defect (8)--(10);
* replacing that by positive reversal production requires the **posterior** chain in (15) or (16), not the sum of unconditional prime contributions;
* independent prime residues do not remove the posterior redundancy (17);
* the exact shared-copy model disproves the needed innovation bound (28), and its correctly conditioned log-weighted production is still Theta(log X), despite every one-point calibration term being zero;
* refinement monotonicity does not supply an ordering across `X/p` and X.

An arithmetic success would need additional control of posterior residue dependence or genuinely fresh current information after earlier copies are observed, together with a valid comparison at the original natural scale. The known one-point Dickman rescaling laws do not provide either estimate through a chain-rule identity. This is a precise failure of the suggested information-theoretic implication, not a proof that every entropy approach or the full smooth-function hypothesis is insufficient.

## Verification record

`python3 Submission/CalibratedEntropyVerification.py` passes. Its probability, independent-residue, conditional one-point-marginal, and shared-copy assertions use exact rational arithmetic. It also checks the frozen smooth identity (2) on actual integers, a full-support nonuniform version of the model, the total-correlation correction (17), and KL/JS identities numerically.

For `gamma=1/2` and primes `(2,3,5,7)`:

* joint transpose KL: `0.549306144334`;
* sum of the four one-prime transpose KLs: `1.042943209054`;
* correct conditional KL increments: `(0.549306144334,0,0,0)`.

For the prescribed-marginal circulation example in the script, the current is `0.0002`, while the marginal-subtracted increment is `-0.001837003503`. Its legitimate reversal production is nonnegative (`0.000000020582`); the symmetric mixture correlation is `0.001837024085`.

These numerical checks are sanity checks for the analytic finite proofs above, not formal proofs of an asymptotic number-theoretic estimate. The power-band assertions (24)--(27) follow from the proved finite formulas and the usual prime harmonic/product asymptotics.

`Spec.lean` remains SHA-256 `d48bb112dcd4fd5c98dae80077b7384df62a14ef9a919fe7d476b9c5ace427bb`.
