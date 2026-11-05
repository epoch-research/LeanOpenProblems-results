# Unbounded auxiliary factors remain the pointwise obstacle

**Status.** `AuxiliaryEscape.lean` is a sorry-free Lean development importing
`AdjacentFactor.lean`, **not** `Spec.lean`. It proves an infinite *limitation on
bounded-divisor searches*, constructs soluble hard primes in that same
congruence class, and certifies a false Jacobi-symbol converse. **It neither
proves nor refutes the proposed all-hard-prime claim**, and does not prove the
Erdős–Straus conjecture.

## The exact proposed strengthening

For `p=24k+1` and `h_i=4i+3`, put

    M_i=((4i+3)p+1)/4=6k(4i+3)+i+1.

The index condition in the question, `i≤(6k−3)/7`, is equivalently
`7i+3≤6k`. The previously proved
`AdjacentFactor.simple_typeI_iff_auxiliary_divisor` states that finding
`q>1`, `q|M_i`, `q≡−1 (mod h_i)` for some index in this bound is **equivalent**
to the *restricted* Type-I criterion: some `p/4<x<p/2` and positive `c|x`
satisfy `4x−p | 4c+1`. It implies an ordered solution but is stronger than
the necessary-and-sufficient full alternative `c|x²` **or** a Type-II
divisor. The coprimality of adjacent `M_i` does not itself decide this factor
congruence.

## A uniform *all-index* obstruction to any fixed bound on `q`

The Lean lemma `eligible_auxiliary_not_dvd_six_k` proves for every `k,i,q`

    q>1, q|M_i, q≡−1 (mod 4i+3)  ⟹  q ∤ 6k.              (1)

Indeed `q|6k` and `q|M_i` imply `q|i+1`; on the other hand
`q≡−1 (mod 4i+3)` implies `q≥4i+2>i+1`. For a fixed integer `B`, if
`k=B!s` then **no eligible divisor `q≤B` occurs at any index**: each
positive `q≤B` divides `B!`, contradicting (1). This is
`no_bounded_auxiliary_divisor_of_factorial`.

Dirichlet's theorem supplies, for every `B,N`, a prime `p>N` with
`p≡1 (mod 24B!)`; hence `p=24k+1` with `k=B!s`.
`hard_primes_escape_bounded_auxiliary_divisors` formally proves that **all**
indices `i` and eligible divisors `q|M_i` for this prime satisfy `q>B`.
This is an infinite pointwise result, not a finite-search extrapolation.
It rules out proof strategies that require an eligible factor below an
*absolute* cutoff `B`, even if they are allowed to inspect arbitrarily many
adjacent factors. It does **not** rule out factors growing with `p`.

## The obstructing congruence class still contains infinitely many solutions

The theorem `soluble_hard_primes_escaping_bounded_auxiliary_divisors` proves
something stronger than a disclaimer: for every `B,N`, there is a prime
`p>N` congruent to `1 (mod 24(B+2)!)` **with an eligible index-zero divisor
`q>B` and `Good p`**. It also verifies that *every* eligible divisor at
*every* index of this prime exceeds `B`.

Here is an explicit progression used in the formal proof. Set

    F=(B+2)!=2(u+1),  u=F/2−1,
    q=6u+5=3F−1,  r=30u+29=15F−1,  v=5u+4,
    L=24F,  p₀=Lv+1,  A=Lq.

Then `M₀(Fv)=18Fv+1=qr`, or equivalently `3p₀+1=4qr`.
The residue `p₀` is coprime to `A`: it is `1 (mod L)`, and if a prime
factor divided both `p₀` and `q`, it would divide `3p₀+1=4qr` and hence
`1`. Thus Dirichlet supplies arbitrarily large primes
`p=p₀+A w`. Put `k=F(v+qw)`; then

    p=24k+1,    M₀(k)=q(r+18Fw),    q≡2 (mod 3).

Every eligible divisor `≤B+2` is excluded by (1), so in particular
`q>B`. The existing certified auxiliary-divisor construction gives, with
`c=r+18Fw` and `t=(q+1)/3=F`, the **strictly ordered** identity

    4/p = 1/(tc) + 1/(qtc) + 1/(pqc).

For example `B=0,w=0` gives the prime `p=193`, `q=5`,
`(x,y,z)=(58,290,27985)`; for `B=1,w=0`, `p=2017`, `q=17`.
These examples are illustrations; the all-`B` assertion is the Lean-checked
Dirichlet theorem. This construction does not cover arbitrary hard primes.

## An actual nonresidue is **not** an eligible factor

`jacobi_nonresidue_not_eligible_193` is an exact certified counterexample
to the erroneous converse of the necessary Jacobi sign lemma. The *prime*
`p=193=24·8+1` has the in-range index `i=5` (`7·5+3≤6·8`) with

    h_5=23,   M_5=1110=2·3·5·37,
    5|M_5,    (5/193)=−1,

but **every divisor** of `1110` has residue among
`{1,2,3,5,6,7,10,14,15,19} (mod 23)`, never the required `22`.
This is only a *local* failure: `i=0`, `M_0=145=5·29`, has the genuine
eligible `5≡−1 (mod 3)`, hence the ordered solution above. A Jacobi
nonresidue must not be silently counted as a divisor in the target class.

## Verification and remaining work

`lake env lean Submission/AuxiliaryEscape.lean` and
`lake build Submission.AuxiliaryEscape` pass. `#print axioms` on its four
principal declarations and the Jacobi example lists only Lean's ordinary
`propext`, `Classical.choice`, `Quot.sound` (no `sorryAx`). `Spec.lean` was not
changed. Neither the all-index absence of *bounded* `q`, the index-5
Jacobi example, nor local neighboring-factor coprimality gives a hard prime
with **no** eligible `q` of unrestricted size over the complete range
`7i+3≤6k`.

If the proposed stronger assertion fails for some prime, that would **not**
by itself disprove the ordered Erdős–Straus conjecture: `CoveringGap.lean`
requires excluding **both** complete alternatives at **every**
`j<6k`, where `x_j=6k+1+j`, `a_j=4j+3`:

    ∃c>0: c|x_j² ∧ a_j|4c+1,
      OR
    ∃d: 0<d<x_j ∧ d|x_j² ∧ a_j|x_j+d.

A valid universal proof must provide an actual divisor for *each* hard
prime; a refutation of the stronger claim must give a **certified prime**
with **all** the permitted auxiliary indices ruled out. No such proof or
prime is supplied here.
