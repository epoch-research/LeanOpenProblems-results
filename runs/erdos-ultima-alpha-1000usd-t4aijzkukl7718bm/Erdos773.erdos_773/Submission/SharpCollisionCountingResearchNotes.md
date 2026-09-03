# Primitive counting and a sharper actual logarithmic lower bound

This continuation does NOT settle Erdos 773. Spec.lean and its sole admission
for 0 < epsilon <= 1/3 are unchanged. No proof submission has been made.

## Six new verified modules

1. PrimitiveSquareCollisions.lean
2. ParityTriangleCount.lean
3. PeriodicCollisionWeights.lean
4. SharpSquareCollisionCount.lean
5. SquareSupportCounting.lean
6. SharpLogarithmicLowerBound.lean

None imports Spec.lean. All compile without admissions or warnings, have
built .oleans, and the printed audits use only propext, Classical.choice,
and Quot.sound. The finite residue and rational-bin calculations use
kernel-checked decide or norm_num, not native evaluation.

## Exact primitive parametrization

For 1 <= a < b < c < d <= N and a^2+d^2=b^2+c^2, there are unique positive
u,v,g,w with v<u and gcd(u,v)=1 such that

    2a + ug = vw,       2b = vw + ug,
    2c + vg = uw,       2d = uw + vg.

Here g=gcd(b-a,d-c). The exact admissibility conditions are

    ug < vw,
    (u+v)g < (u-v)w,
    uw+vg <= 2N,
    vw+ug = 0 mod 2,    uw+vg = 0 mod 2.

`parameters_card` proves a bijection, not merely a covering bound.
`SquareSupportCounting.edges_card` then proves that the ordered quadruple
count is exactly the cardinality of SquareCollisionCodegrees.edges [1,N].
Each unordered four-distinct-root collision support is counted once.

## Parity and triangle counts

For coprime u,v:
- If both are odd, g and w must have the same parity.
- If their parities differ, both g and w must be even.
- Both u and v even is impossible.

For a finite set of positive-first-coordinate lattice points satisfying

    C*g <= w,    w+r*g <= A,    A>=0,    D=C+r>=1,

the verified bounds are

    both even:       count <= A^2/(8D) + A/2,
    both odd:        count <= A^2/(8D) + A/2 + 1/2,
    matching parity: count <= A^2/(4D) + A + 1/2.

They are proved by counting parity-restricted fibers in real intervals and
summing arithmetic progressions. No independence theorem is assumed.

The two admissibility inequalities give C=u/v or C=(u+v)/(u-v), with
r=v/u and A=2N/u. Their area factors involve

    shape1(x)=x/(1+x^2),
    shape2(x)=(1-x)/(1+2x-x^2).

Twenty rational bins, using shape1 below the 2/5 switch and shape2 above,
have total upper-step height at most 123/32.

## Small-prime sieve and periodic averaging

The parity multiplicity is 1 for opposite parities and 2 for both odd.
It is set to zero when both u,v are even or share the factor 3 or 5.
This weight is periodic modulo 30 in both variables, is <=2, and satisfies

    sum_{0<=u,v<30} weight(u,v) = 768.

If row(u)=sum_{v<30} weight(u,v), the verified estimates include

    sum_{v in S} weight(u,v)
       <= row(u)*((U-L)/30+1)

for an integer set S in a real interval [L,U], and

    sum_{1<=u<=M} row(u)/u
       <= (768/30)*(1+log M)+1800.

The integer lattice boundary errors contribute O(N^2), with explicit
constants throughout.

## Actual collision bound

For E4(N)=|SquareCollisionCodegrees.edges [1,N]|, the final finite theorem is

    E4(N) <= N^2*((41/500)*(1+log(2N))+244).

For every eta>0, eventually

    E4(N) <= (41/500+eta)*N^2*log N.

In particular, eventually

    E4(N) <= (83/1000)*N^2*log N,

where 83/1000 < 1/12. This is an upper bound on the number of collision
supports, NOT an upper bound on M(N).

## Improved actual Sidon lower bound

`SharpLogarithmicLowerBound.four_obstructions_bound` injects the four-point
obstructions on square values into images of the unordered root supports.
It yields the finite alteration inequality

    M(N) >= p*N - p^3*|squareAPs(N)| - p^4*E4(N),   0<=p<=1.

Thus the fourth-order term no longer counts ordered presentations or
trivial collisions.

`finite_log_lower` assumes N>=8000000000, log N>=2, and
E4(N)<=(1/12)N^2 log N. Put R=(N log N)^(1/3) and p=3/(2R).
The existing AP bound implies |squareAPs(N)|<=24 R^3, so its deletion
cost is at most 81. The four-edge cost is at most (9/32)*p*N.
The numerical height bound gives R<=N/2000 and p*N>=3000, providing
sufficient slack.

`eventual_log_lower` combines this with the proved collision estimate to give

    eventually M(N) >= N/(N log N)^(1/3)
                    = N^(2/3)/(log N)^(1/3).

This removes the factor 1/8 from the older bound and replaces the harmless
1+log(2N) or 1+log(4N) expressions by log N. It is a genuine improvement
of an actual Sidon lower bound, but NOT an exponent improvement.

## Remaining gap

No logarithmic independent-set gain was proved in this continuation.
The available Mathlib search did not locate the required sparse-hypergraph
independence theorem. A sharp theorem suitable for the bounded-codegree
four-uniform collision hypergraph would need to be established, with all
constants, nonuniform degrees, and three-root obstructions accounted for.
The new leading collision coefficient alone does not supply such a theorem.

Even proving epsilon=1/3 would not settle the original conjecture for
0<epsilon<1/3. No actual lower exponent above 2/3 or fixed-power upper
loss for the original maximum was obtained.

## Logs

- /tmp/primitive-square-collisions.log
- /tmp/parity-triangle-count.log
- /tmp/periodic-collision-weights.log
- /tmp/sharp-square-collision-count.log
- /tmp/square-support-counting.log
- /tmp/sharp-logarithmic-lower-bound.log
