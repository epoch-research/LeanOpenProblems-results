# Two-scale pair minorant — not a settlement

Submission/Spec.lean remains unchanged and retains its original sorry.
No positive prime-pair lower bound or irrational counterexample has been
obtained.

## New verified file

Submission/TwoScalePairMinorant.lean
Namespace: Erdos972TwoScalePairMinorant.

Let S_t(n) denote the existing smoothed Mangoldt function. Define

    lowerWeight(t,n) = 2 S_t(n) - (8/7) S_(2t)(n),
    upperWeight(t,n) = (4/3) S_t(n).

For t>0 and t log n<=1/4, two_scale_sandwich proves

    lowerWeight(t,n) <= Lambda(n) <= upperWeight(t,n),
    upperWeight(t,n) >= 0.

The non-prime-power lower bound uses the stronger Euler-product inequality

    product_{p|n, p prime}(1+exp(-t log p)) >= 4-2t log n

for positive nonunits that are not prime powers. Two distinct prime factors
p,q have log p+log q<=log n, and exp(x)>=1+x bounds all three nonconstant
terms in (1+exp(-t log p))(1+exp(-t log q)). The other factors are >=1.
Thus S_(2t)(n)>=(7/4)S_t(n) in the specified window.

For prime powers the exact single-factor formula is used. It gives
S_(2t)(n)>=(7/8)S_t(n), while the earlier scalar error bound gives
S_t(n)>=(3/4)Lambda(n). Cases n=0,1 are retained.

## Genuine finite pair minorant

Define

    P_t(m,n) = (32/63) * [
      7 S_t(m) S_t(n)
      -3(S_(2t)(m) S_t(n) + S_t(m) S_(2t)(n))].

pairMinorant_le proves, for t>0 and both t log m,t log n<=1/4,

    P_t(m,n) <= Lambda(m) Lambda(n).

It uses the valid real inequality

    l V + U r - U V <= x y

when l<=x<=U, r<=y<=V and U,V>=0. In particular it does not multiply two
signed one-sided inequalities as though their lower bounds were nonnegative.

pairMinorantSum_le proves the actual floor-map comparison: for alpha>=1,
t>0, and t log(floor(alpha*N))<=1/4,

    sum_{0<n<=N} P_t(n,floor(alpha*n))
        <= mangoldtCorrelation(alpha,N).

There is NO positive lower bound on the left side in this file.

## Arithmetic estimate still missing

If the three normalized smooth correlations in the displayed expression
could all be replaced by 1, the scalar expression would be 32/63>0. This
is only an algebraic benchmark, not a proved joint-limit theorem.

The existing fixed-positive-parameter mean results do not supply those
estimates at t log(floor(alpha*N))<=1/4. In particular, one cannot choose
N after fixing t to satisfy a mean theorem and then assume that this upper
bound on N still holds. No uniform mixed-parameter lower bound in the
critical window was obtained. The proper-prime-power error would also have
to be accounted for before concluding simultaneous primality.

## Verification

The new file compiles to
.lake/build/lib/lean/Submission/TwoScalePairMinorant.olean.
The three principal declarations audit with only propext, Classical.choice,
and Quot.sound. The file contains no sorry declarations. No imports or
statements in Spec.lean were changed, and no incomplete proof was submitted.

## Follow-up quantitative tail-budget review — no new theorem

The existing absolute tail approximation was checked against the relaxed
finite window of the pair minorant. No positive sum estimate resulted.

For alpha>=1, t>0, D<=N and t log(floor(alpha*N))<=1/4, monotonicity of
the natural logarithms gives t log D<=1/4, hence

    damping(t,D) >= exp(-1/4).

The nonnegative kernelMass(t/2) includes its (1,1) term, equal to one.
Consequently the expression used for the normalized smooth-tail energy
upper budget,

    damping(t,D) * kernelMass(t/2) / t^2,

is at least exp(-1/4)/t^2. Along diverging input cutoffs, the admissibility
condition forces t->0, so this particular budget cannot certify a small
normalized smooth-tail error.

This is a comparison of BUDGET EXPRESSIONS, not a lower bound on the
actual tail or on the error of the signed pair minorant. No cancellation
between the three signed correlation errors was discarded as negligible,
and no general impossibility claim about other estimates is made.

No additional Lean declaration, sufficient lower bound, or irrational
counterexample was obtained in this review. Spec.lean is unchanged and
unresolved. No incomplete proof was submitted.

## Later extension: actual fixed-parameter mixed means

`ProgressMixedSmoothMean.md` records two new verified files. They establish
all-cutoff mixed smooth means and the actual two-scale fixed-t mean, whose
outer limit is 32/63. This advances the earlier algebraic benchmark to an
ITERATED limit, not to a moving-parameter theorem. The same fixed-t main
term is also proved after deleting all prime inputs and prime outputs.
The sufficient lower bound in the finite minorant window remains missing.
