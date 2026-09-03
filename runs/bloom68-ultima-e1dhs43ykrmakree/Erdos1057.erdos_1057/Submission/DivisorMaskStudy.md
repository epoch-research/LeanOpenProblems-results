# Divisor-distribution mask: mathematically audited information obstruction

Status: informal research, not a Lean proof of either target theorem. The exact finite theorem and its analytic estimates have survived independent mathematical audit; none is kernel-checked. The optimized exact repair remains unproved. This only models the data for candidate primes congruent to 1 modulo d; it does not model primality or every reduced residue class.

## Exact finite statement (informally audited)

Fix 0 < gamma < 1/4 and B > 0. For sufficiently large real x, put y=x^gamma, D=floor(sqrt(x)/(log x)^B), I={n in N: x/2<n+1<=x}, and A=li(x)-li(x/2). There exist weights v(n) supported on I such that

- 0 <= v(n) <= 1;
- v(n)=0 whenever all prime factors of n are <= y;
- for every integer 1<=d<=D, sum_{n in I,d|n} v(n)=A/phi(d), exactly.

Consequently no signed divisor sum W(n)=sum_{d<=D} lambda_d 1_{d|n} which is a pointwise minorant of the y-smooth indicator on ALL of I can have sum lambda_d/phi(d)>0. This conclusion does not cover a minorant valid only when n+1 is prime.

## 1. Completely multiplicative mask

Let k(t)=1 for 1<t<2 and zero otherwise. Define, with additive convolution on the positive real line,

h(t)=sum_{j>=1} (t/j) k^{*j}(t), chi(t)=1-h(t).

The sum is locally finite, and h=g+k*h, where g(t)=t k(t). Thus h=0 for t<1, h=t on (1,2), and for t>2,

h(t)=integral_1^2 h(t-u) du.

Induction gives 0<=h<=2. For every t>2, 0<h(t)<2, with uniform strict inequalities on compact subsets of (2,infinity). Use the natural endpoint values h(1)=h(2)=0, so chi(1)=1. The function is locally Lipschitz off {1,2}, with a globally bounded almost-everywhere derivative there. Indeed, (k*h)'=k'*h almost everywhere, with k' a finite signed measure. Renewal identities with reassigned endpoints would hold only almost everywhere.

Define a real completely multiplicative f_y by f_y(p)=chi(log p/log y). Then |f_y|<=1 and f_y(n)=1 for every y-smooth n. Therefore 1-f_y is nonnegative and vanishes on every y-smooth integer.

### Required uniform summatory lemma

For every fixed U>2 and epsilon>0, there is c>0 such that

sum_{n<=T} f_y(n) = O_{U,epsilon}(T exp(-c sqrt(log y)))

uniformly for y^(2+epsilon)<=T<=y^U.

Proposed proof: write ell=log y and K(z)=integral_1^2 exp(-zt)dt. The renewal identity gives

integral_0^infinity h(t)/t exp(-zt)dt = -log(1-K(z)), Re z>0.

The Euler product and PNT with a de la Vallee Poussin error then give

F_y(s)=zeta(s)(1-K((s-1)ell))(1+O(exp(-c2 sqrt(ell))))

on Re s=1+1/log T and |Im s|<=exp(c1 sqrt(ell)), with c1 sufficiently small. Prime-power errors are O(1/y), and the prime-to-integral error is controlled by the bounded variation/derivative of h. Here Re((s-1)ell)>=1/U, so the logarithm stays uniformly away from its singularity.

The inverse summatory function for zeta(s)(1-K((s-1)ell)) is

M_y(T)=floor(T) - (1/ell) integral_y^(y^2) floor(T/v) dv.

For T>=y^2 its linear terms cancel, so M_y(T)=O(1+y^2/ell). Average the summatory function on [T,T+Delta], use the Perron kernel ((T+Delta)^(s+1)-T^(s+1))/(Delta*s*(s+1)), and choose H=exp(c1 sqrt(ell)), Delta=T/sqrt(H). The tails are O(T log T/sqrt(H)); removing the average costs O(Delta+1) because |f_y|<=1. This should prove the lemma.

## 2. Positive weights with the prime-predecessor local densities

Let C2=product_{p>2}(1-1/(p-1)^2) and

w(n)=2*C2*1_{2|n}*product_{p|n,p>2} (p-1)/(p-2).

For odd squarefree r define a(r)=product_{p|r}1/(p-2), with a(1)=1 and zero otherwise. If d0=lcm(d,2), then

w(d0*m)=w(d0)*sum_{r|m,(r,d0)=1}a(r),

(w(d0)/d0)*sum_{(r,d0)=1} a(r)/r = 1/phi(d).

Using a(r)<=tau_3(r)/r yields uniformly

sum_{n<=Z,d|n}w(n) = Z/phi(d)+O(log^C(2Z)),
sum_{n<=Z,d|n}w(n) <= Z/phi(d),
0<=w(n)<=n/phi(n)=O(log log(3n)).

Complete multiplicativity gives the exact masked expansion

sum_{n<=Z,d|n}w(n)f_y(n)
 = w(d0)f_y(d0) sum_{(r,d0)=1}a(r)f_y(r)
        * sum_{m<=Z/(d0*r)}f_y(m).

Choose a fixed theta>1/2 with theta+2*gamma<1. Split r at a small fixed power x^rho so that Z/(d0*r)>=y^(2+epsilon) for d<=x^theta and Z comparable to x. Apply the summatory lemma to small r and the convergent a(r)/r tail to large r. This gives errors of size O((x/d)exp(-c sqrt(log x))) after absorbing logarithmic factors.

Define the preliminary weights on I by

v0(n)=w(n)(1-f_y(n))/log(n+1).

Partial summation should therefore give, for all d<=x^theta,

sum_{n in I,d|n}v0(n)=A/phi(d)+e_d,
|e_d| <= (x/d)*epsilon_x,

epsilon_x=O(exp(-c sqrt(log x))). The same estimates apply uniformly to partial prefixes of I. The weights are nonnegative, vanish on smooth n, and are O(log log x/log x).

## 3. Exact correction via disjoint arithmetic fibres

Set R_t=A/phi(t)-sum_{n in I,t|n}v0(n) for all EVEN t<=2D. Define

c_k=sum_{j<=2D/k}mu(j)R_{kj}, for even k<=2D.

Finite Mobius inversion gives sum_{k<=2D,t|k}c_k=R_t for every even t<=2D. Also

|c_k| <= (x/k)*epsilon_x*O(log x).

For each even k<=2D, let F_k={k*p in I: p is prime and p>2D}. Since B>0, every prime p in the relevant interval satisfies p>2D when x is large. PNT uniformly on these dyadic intervals gives

|F_k| >= c*x/(k log x).

The fibres F_k are pairwise disjoint: a representation k*p=k'*p' with k,k'<=2D and primes p,p'>2D forces p=p', k=k'. For any d<=D and n=k*p in F_k, d|n iff d|k.

On every fibre, log p/log y lies in a fixed compact subset of (2,infinity), because gamma<1/4. Thus |f_y(p)|<=1-c_gamma, and

v0(k*p) >= c'_gamma/log x.

Add c_k/|F_k| to v0 at every point in F_k. The absolute per-point correction is O(epsilon_x log^2 x), much smaller than c'_gamma/log x, so the corrected weights stay in [0,1]. They stay supported on non-y-smooth integers (not y-rough integers: these are even). For d<=D, let t=lcm(d,2)<=2D. Since all supported points are even, divisibility by d is equivalent to divisibility by t and phi(t)=phi(d) whenever d is odd. The Mobius identity gives the required exact corrected moment.

## 4. Approximate global variant and optimized cutoff

The same renewal construction can instead take k(t)=2/t on 1<t<sqrt(e). Then 0<=t k(t)<=2, integral k=1, |chi|<=1, and the summatory mean vanishes, with PNT-sized error, beyond y^(sqrt(e)+epsilon). This permits approximate divisor distribution to every fixed level theta with theta+sqrt(e)*gamma<1. Exact moment repair has NOT been justified throughout that larger range: chi(t)=1 for sqrt(e)<t<2, so some correction fibres can lose their lower bound.

Dyadically gluing the uncorrected (or uniform-kernel corrected) weights, with a smoothness exponent eta>gamma, should give a single sequence a(m) with PNT and full residue-1 BV remainders at all large scales, while a(m)=0 whenever P+(m-1)<=m^eta. The allowed theta is below 1-2eta for the uniform kernel, or below 1-sqrt(e)*eta for the optimized kernel. In particular gamma<1/(2sqrt(e)) permits a level strictly above 1/2 in the approximate construction.

The independent audit verified standard PREFIX Brun-Titchmarsh compatibility with constant 2, using the accurate individual main term for d below a fixed level >1/2 and the pointwise upper bound a(m)<=(2+o(1))w(m-1)/log m for larger d. It did not verify an arbitrary-short-interval or all-residue extension. The optimized kernel also has chi(1+sqrt(e))=-1; strict |chi|<1 on every t>2 is specific to the uniform kernel.

## Scope and open task

The exact finite construction would decisively rule out a BV-main-term-positive divisor-only minorant valid on all integers. It does not settle the actual prime problem. Neither the Carmichael conjecture nor its negation has been proved. Submission/Spec.lean must remain untouched unless a complete valid proof of one target is obtained.
