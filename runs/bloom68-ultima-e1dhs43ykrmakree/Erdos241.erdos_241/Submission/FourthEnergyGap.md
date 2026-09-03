# An audited fourth-energy gap — not a solution of Erdős 241

Status: mathematical auxiliary argument, independently checked at the counting/algebra level; not Lean formalized. Neither theorem in `Spec.lean` is discharged. In particular, the coefficient below is **not** an interval extremal constant.

Let A be an integer strong B3 set, including repeated summands, and n=|A|. Write E_j(A) for the number of ordered equalities of two j-term sums. Then

    E4(A) <= (2 - 1/2552)n^5 + 169n^4.

## Pair differences and repetitions

Let m(t) count ordered (P,Q) of disjoint unordered two-element subsets of A with sum(P)-sum(Q)=t. Then

    sum_t m(t)=6 binom(n,4),      m(t)<=n/2.

At a fixed t, positive pairs have disjoint supports, and negative pairs do too: sharing a same-sign element cancels to a B3 equality, which identifies the representations. Deleting k elements therefore removes at most 2k representations at each t.

There is a coordinate permutation identifying 16 sum_t m(t)^2 with a subset of ordered fourth-energy solutions. This subset contains every eight-distinct solution, but also some repeated-position solutions. Consequently

    0 <= E4 - 16 sum_t m(t)^2 <= R(A) <= 168n^4,

where R counts solutions with a repeated position. For a prescribed opposite-side repeated position, the count is n E3. For a same-side repetition, fix its common value a and put rho(s)=#{(x,y,z) in A^3:x+y-z=s}. The remaining count is sum_s rho(s)rho(2a-s)<=sum_s rho(s)^2=E3 by Cauchy–Schwarz. Thus each of the 28 position pairs contributes at most n E3, and

    E3=6n^3-9n^2+4n<=6n^3.

## Five-set flags

For a five-set B, let F(B) count its two-subsets P for which sum(B)-2sum(P) has a reduced representation x+y-z by three distinct exterior points. Such a representation is unique, up to exchanging x,y, by B3. A flag (B,P) determines an unordered collision {C,D} of disjoint four-sets with equal sums.

Each collision has 2*binom(4,3)*binom(4,2)=48 flags and contributes 2*(4!)^2=1152 ordered energy solutions. Thus

    E4*(A)=24 sum_B F(B)<=240 binom(n,5)<=2n^5,

where E4* denotes eight-distinct solutions. For two specified vertices in a collision, exactly 16 flags contain both if they are on the same side, and 18 if they are on opposite sides. Since at most 10 binom(n-2,3) flags contain a fixed pair, the number of ordered eight-distinct energy solutions containing that pair is at most

    720 binom(n-2,3)<=120n^3.

## The span inequality

Sort A as a_1<...<a_n and set Phi(r)=sum_{i=1}^r(a_{n+1-i}-a_i). Union the positive supports and negative supports of all m=m(t) representations. Both unions have size 2m, so

    m|t|<=Phi(2m)=Phi(n-2m).

For positive diameter L this implies

    m(t)<=nL/(2L+|t|).

A core T of n-k elements of diameter L gives

    m_A(t)<=m_T(t)+2k<=(n-k)L/(2L+|t|)+2k.

## Concentration dichotomy

Assume n>=352, k=floor(n/176), and let L be the minimum diameter of any n-k points of A. L>0. Put tau=L/14 and Delta=(n-88k)/58>0. For |t|>=tau, the core bound yields m(t)<=n/2-Delta.

### Case A

No interval of length L/7 contains n-2k points. For each ordered (a,b,c), at least 2k choices of d have |a+b-c-d|>=tau. At most 6n^3 ordered quadruples have a repeated position. Dividing by four gives

    sum_{|t|>=tau}m(t)>=(2k-6)n^3/4.

Use the cap n/2 everywhere and the improved cap on this tail:

    E4<=2n^5-8k Delta n^3+24 Delta n^3+168n^4.

Writing k=n/176-r, 0<=r<1, gives the exact cancellation

    8k Delta n^3=n^5/2552-(352/29)r^2 n^3.

Since Delta<=n/58 and n>=176, the error is at most (168+14/29)n^4.

### Case B

An interval J of length L/7 contains at least n-2k points. The interval 4J-3J has length L; put S=A intersect (4J-3J). Then |S|<=n-k. There is no tie loophole: an L-interval containing n-k+1 distinct points would have its first n-k points of strictly smaller diameter than L.

Every **eight-distinct** collision not contained in S has at least two points outside J. Otherwise its sole outside point would equal four J-points minus three J-points and so belong to 4J-3J. There are at most 2k outside points. The fixed-pair bound and the separate repeated-position allowance give

    E4(A)<=2(n-k)^5+240k^2 n^3+168n^4.

With x=k/n in [1/352,1/176],

    2(1-x)^5+240x^2 <= 2-10x+260x^2 <= 2-8x <= 2-1/44.

This has more leading saving than required. For n<352, the crude bound E4<=2n^5+168n^4 absorbs the extra n^5/2552 within n^4. This proves the stated error 169n^4 for every n.

## Scope and the unresolved target

For A contained in [1,N], Cauchy–Schwarz only gives E4>=n^8/(4N-3). Combined with this result, its direct consequence is

    n^3/N <= 8-1/638+o(1),

which is weaker than the elementary cubed constant 6 and the cited literature constant 7/2. It does not imply n^3/N<=1+o(1), and gives no unbounded fixed-excess construction. A sharp interval transference or a new construction is still missing. No admitted target theorem was used.
