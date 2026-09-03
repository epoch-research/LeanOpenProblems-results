# Critical-scale continuation: positive bounds and remaining gaps

Neither theorem in `Spec.lean` is proved. This is an unformalized mathematical checkpoint, not a submission. No finite example, relaxed profile, coding equivalence, or geometric obstruction below is a disproof of Erdős 241.

## 1. Finite smoothing inequality (independently checked)

Assume c is a valid universal constant such that every nonnegative probability density f supported in an interval of length W satisfies

    integral (f*f)^2 >= c/W.

For a strong integer B3 set A in [0,N], n=|A|, and integer L>=1, one then has

    c n^3 <= (N+L)(2+4n^2/L).

Proof: let u_L=L^(-1)1_[0,L], g=sum_{a in A}u_L(.-a), and w=u_L*u_L*reverse(u_L)*reverse(u_L). Periodization gives sum_{t in Z}w(t)=1; the triangular convolution gives max w=w(0)=2/(3L). Let rho(t) count ordered a+b-c-d=t. Its four-distinct part is 4m(t), where the audited strong-B3 matching bound is m(t)<=n/2. The remaining ordered quadruples have total number at most 6n^3. Thus

    integral (g*g)^2=sum_t rho(t)w(t)<=2n+4n^3/L.

The lower bound applied to g/n, supported on [0,N+L], proves the result. The case n=0 is trivial; cancel n only when n>0.

Taking L=ceil(N^(5/6)), together with n=O(N^(1/3)), gives n^3 <= (2/c)N+O(N^(5/6)). Alternatively L=ceil(n sqrt(2N)) gives

    c n^3 <= 2N+4 sqrt(2)n sqrt(N)+4n^2+2.

### Published analytic input, not independently recertified

Martin–O'Bryant, `/corpus/src/math_0410004/SSPCRT.2.tex`, lines473–571, give a piecewise-linear kernel certificate implying c=22983/40000=0.574575. The parent read the proposition, support normalization, and corollary: their bound 1.14915 is for support width1/2, hence the factor1/2 here is necessary. Their numerical Fourier-norm certificate has NOT been independently recomputed or Lean formalized.

Conditional on that published analytic bound, the interval corollary is

    n^3 <= (80000/22983+o(1))N,       80000/22983=3.4808337... .

No priority claim is made. This is only a small improvement over the quoted 7/2, not the desired constant1. Optimizing only c cannot settle the target: the uniform density on a unit interval has autoconvolution energy2/3, so c<=2/3 and this method's coefficient2/c is at least3.

## 2. An elementary aggregate energy envelope (independently checked)

Let n,N>0, Q=sum_t m(t)=6 binom(n,4). The span inequality gives m(0)=0 and

    0<=m(t)<=c_N(|t|),       c_N(x)=nN/(2N+x).

Then

    sum_t m(t)^2 <= n^2 N (1-exp(-Q/(2nN))).

Proof: set beta=(n/2)exp(-Q/(2nN)). For 0<=z<=c, convexity yields

    z^2 <= beta z + max(c(c-beta),0).

The positive-part function of x obtained from c_N(x) is decreasing. Summing over nonzero integer t is bounded by twice the integral over x>=0. Its support ends at b=nN/beta-2N. Direct integration gives

    2 integral_0^b c_N = Q,
    2 integral_0^b c_N^2 = n^2N-2nN beta.

After adding beta Q, the mixed terms cancel. This is a finite inequality without a discretization error. For Q=0 the same formulas have b=0.

Using the independently audited repeated-energy allowance,

    E4(A)<=16n^2N[1-exp(-(n-1)(n-2)(n-3)/(8N))]+168n^4.

For lambda=n^3/N, its leading coefficient is

    E4/n^5 <= (16/lambda)(1-exp(-lambda/8))+O(1/n).

The function (1-exp(-x/8))/x is decreasing for x>0. Consequently n^3>=N implies the valid finite estimate

    E4 <= 16(1-exp(-1/8))n^5+168n^4 < 1.880050n^5+168n^4.

For 0<eta<1, nearly saturated matchings satisfy

    |{t:m(t)>=(1-eta)n/2}| <= 4eta N/(1-eta),
    sum_{m(t)>=(1-eta)n/2} m(t) <= 2nN log(1/(1-eta)).

These follow by restricting |t|<=2eta N/(1-eta) and integrating the same decreasing cap.

### Exact gap: mesoscopic concentration

The aggregate energy envelope does not improve the leading 2n in the smoothing inequality: a set of o(N) small displacements can carry near-saturated matchings and dominate a kernel of width n^2 << L << N, while contributing only o(n^5) to global energy. No critical-scale joint matching bound was proved.

A simple exact relaxed profile shows why the audited macroscopic order constraints alone do not force lambda=1. Let mu be uniform on [0,1] and

    g(t)=2/3-t^2+|t|^3/2             (|t|<=1),
    g(t)=(2-|t|)^3/6                (1<=|t|<=2),
    g(t)=0                          otherwise.

It is the density of mu*mu*reverse(mu)*reverse(mu). At lambda=2, the candidate multiplicity profile m(Nt)/n=g(t)/2 satisfies the uniform-quantile cap (2-|t|)/4: for 0<=t<=1,

    (2-t)-2g(t)=2/3-t+2t^2-t^3 >=14/27,

and for 1<=t<=2 the inequality follows from (2-t)^2<=1. Its mass is the required lambda/4, and its normalized energy is

    lambda integral g^2 = 302/315 < 1.

Thus it also satisfies both audited fourth-energy upper bounds. This is ONLY a feasible continuous relaxation, NOT an actual strong-B3 family; no microscopic additive realizability is asserted.

### Extension: interval cores, all deletion profiles, and arbitrary smoothing

The same lambda=2 relaxation survives more than the full-set cap. This paragraph concerns continuous profiles only, not realizable finite B3 sets.

Write U=1_[0,1]. For an interval J contained in [0,1] of length ell>0, let h=1_J. Then

    g_h(t)=(h*h*reverse(h)*reverse(h))(t)=ell^3 g(t/ell).

The core has relative mass ell and effective cubic ratio lambda_J=2ell^2<=2. Its proposed normalized multiplicity is q_h=g_h/2. The previously checked inequality 2g(v)<=2-|v| implies

    q_h(t)<=ell(2-|t|/ell)/4       for |t|<=2ell.

Indeed, the ratio-two core expression would be ell*g(t/ell)/2, and q_h is ell^2 times that expression. Thus every interval core satisfies its own uniform-quantile cap. Empty cores are trivial. Translations of J do not change this fourfold difference convolution.

Deletion inequalities also hold for every measurable subprofile 0<=h<=U, not just interval cores. Let delta=integral(U-h). Telescope the four convolution factors. Each of the four nonnegative difference terms is bounded in sup norm by delta times the maximum of a threefold signed convolution of U, namely3/4. Hence

    0<=g_U-g_h<=3delta,
    0<=q_U-q_h<=3delta/2<=2delta.

This matches, with slack, the normalized discrete bound that deleting delta*n vertices destroys at most2delta*n fixed-displacement representations. It does NOT assert an unproved quantile cap for every noninterval subprofile.

Finally let u be any nonnegative probability density of compact interval support, and w=u*u*reverse(u)*reverse(u). By associativity and reflection of convolution,

    integral g_U(t)w(t)dt = integral ((U*u)*(U*u))(x)^2 dx.

The right side is the actual autoconvolution energy of the probability density U*u. Thus every valid analytic lower bound applied to that density is automatically satisfied by the proposed rho-profile4q_U=2g_U. All nonnegative weighted upper bounds following from the verified pointwise cap are also satisfied. Merely changing the smoothing kernel, or combining these interval-core and deletion inequalities, cannot reject this relaxation at cubic ratio2.

What remains absent is a collection of actual integer labels whose triple sums are injective. The relaxed multiplicities were not shown to arise from such labels. This extension therefore identifies a limitation of the present proof strategy, not a counterexample to the conjecture.


## 3. The Lee-code bridge is an equivalence, not an amplification

Put H7={z in Z^n:sum z_i=0 mod7}. If a full-rank lattice L<=H7 has no nonzero vector of l1-norm<=6 and H7/L is cyclic of order M, the classes of e_i-e_n are n distinct strong-B3 elements. A triple collision gives a balanced lattice vector of norm<=6. The index in Z^n is 7M.

Conversely, translate a strong cyclic-B3 set so that b_n=0 and restrict to the subgroup generated by its differences, of order M. Define

    L={z:sum z_i=0 mod7, sum z_i b_i=0 modM}.

The homomorphism Z^n -> C7 x C_M is surjective: e_n supplies the first factor and e_i-e_n generate the second. Hence index(L)=7M. Any vector of norm<=6 in L is balanced, and its equal positive/negative parts can be padded by b_n=0 to triples. B3 forces that vector to vanish. Moreover H7/L is C_M.

Therefore a determinant below (7-eta)n^3 by a fixed proportion, with the required cyclic height kernel, is exactly another form of a cyclic fixed-excess construction. It is not a free conversion of arbitrary good codes or a proved finite-seed amplification. The construction inspected in arXiv:2111.03343 starts from Bose–Chowla sets and gives determinant7(n^3-1), returning asymptotic constant1.

## 4. Finite-geometric candidates: precise conversion failures

### Cyclic Singer quadrangles and orbit-line labels

Let an abelian group G act on a triangle-free partial linear space (its incidence graph has no6-cycle), let O be a free point orbit, and let S={g:p^g lies on L}. If H=Stab(L) is trivial, three distinct a,b,c in S produce the obligatory commutative hexagon in the induced development, contradicting the incidence condition. Thus |S|<=2.

If H is nontrivial and S nonempty, then S is one H-coset. Indeed, for a,b in S and nonzero h in H, L and L^(b-a) share the distinct points p^b,p^(b+h), so partial linearity makes b-a belong to H. H-invariance supplies the reverse inclusion.

Consequently a thick GQ cannot have a cyclic point-regular Singer group: all lines through the identity would be subgroups of the same order, but a cyclic group has only one such subgroup. This elementary argument was checked independently; it does not exclude all noncyclic Singer groups.

A different genuine cyclic symmetry exists for the Bamberg–Lee–Momihara–Xiang hemisystems (`/corpus/src/1512.00962/1512.00962.tex`): C_((q^3+1)/4), for q=3 mod4. It is semiregular, with many point orbits, not a cyclic point-regular action. The natural orbit-line labels are still covered by the preceding lemma. A new nonlinear multi-orbit label construction has not been supplied.

Even arbitrary integer lifts of an order-d subgroup coset in C_M remain in one residue class modulo M/d. If n lifted values have actual span L and are strong B3, then

    binom(n+2,3)<=floor(3Ld/M)+1.

For the orbit-line cosets d<=q+1 and M=(q^3+1)/4, this forces n^3/L=O(q^(-2)) for unbounded n. This statement concerns actual lifts, not merely modular collisions.

### The tempting half-volume partial geometry

A one-block abelian development pg(s,s,2) with k=s+1 labels D has a B2 set satisfying ordered signed counts r_D(x)=2k-1 on D and r_D(x)=2 off D. Its group order is

    v=k+k(k-1)^2/2 ~ k^3/2.

Every reduced diagonal value 2a-b (a!=b) lies outside D. It has one diagonal representation; since off-diagonal representations come in swapped pairs and the total is2, its second representation is also diagonal. Thus the map (a,b)->2a-b is exactly two-to-one on distinct ordered pairs of D.

For a strong-B3 subset A of size n this map must be injective. Hence

    n(n-1)<=k(k-1)/2,       limsup n^3/v<=1/sqrt(2)<1.

This blocks cyclic pruning of this exact development, but modular collisions alone would NOT rule out efficient integer lifts. No unbounded cyclic development with the required parameters was found; the inspected known van Lint–Schrijver example has group F3^4, where 3a=3b immediately prevents any strong-B3 subset of size2. No lift construction settling the integer case was obtained.

The dense B3+ construction in `/corpus/src/1306.4941/1306.4941.tex` is also not a solution: it takes two translates of one Bose set and has many nontrivial two-sum collisions. In any nonempty set, B2 plus B3+ would already imply strong B3 by cancelling a shared term. The construction does not supply B2, nor a repair at fixed cubic gain.

## Status

The missing result is still a uniform sharp interval bound or an explicit unbounded family with fixed cubic excess. None of the coding, geometric, or analytic deductions above supplies it. `Spec.lean` has not been changed and neither admitted target was used.
