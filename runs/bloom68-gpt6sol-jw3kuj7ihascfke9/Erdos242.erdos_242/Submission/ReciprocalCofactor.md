# Reciprocal cofactor axis: exact new factor test, not an all-prime proof

**Status:** `ReciprocalCofactor.lean` proves the elementary equivalence below without `sorry`; it does **not** show that any arbitrary prime has a witness. Neither `TypeIIOffsetBound.lean` nor `Spec.lean` was edited. The numerical tests are reproducible with `python3 Submission/ReciprocalCofactorAudit.py` and must not be interpreted as universal evidence. By `TypeIIOffsetBound.full_square_axis_iff_typeII`, the axis being studied is *exactly full Type II* on hard primes, not just the restricted `d∣m` subfamily.

## Change the search direction: factor `4vp+1`

Put `h=4m−1` and `m²=dv` with `m,d,v>0`. Then `h+1=4m`, `16m²=1+h(h+2)`, and the identity

    4v(p+4d) = (4vp+1) + h(h+2)

implies `h∣p+4d` if and only if `h∣4vp+1`: in the reverse direction cancel `4v`, which is coprime to `h` since `v∣m²` and `gcd(4m−1,4m)=1`. This is proved in Lean as `typeII_reciprocal_congruence`; it does not require `p` to be prime. Moreover `4d<p` is *exactly* `4m²<vp`. Therefore, for every `p≡1 (mod 24)`, `full_square_axis_iff_reciprocal` proves

    FullSquareAxis(p)  iff
    exists m,v>0: v∣m², 4m²<vp, (4m−1)∣4vp+1.        (1)

The `m≤(p−1)/6` condition follows from the other constraints, by the existing Lean theorem `full_square_axis_bound`; it has not been dropped without justification. Neither (1) nor its Lean proof asserts that the right side holds for every prime.

If `v=∏q^e`, set `ρ(v)=∏q^ceil(e/2)`. Prime exponents give `v∣m²` iff `ρ(v)∣m`. Thus (1) has an exact **factorization-only** formulation: some `v>0` makes `F_v=4vp+1` have a positive factor `h≥3` such that

    h≡−1 (mod 4ρ(v))  and  (h+1)²<4vp.          (2)

Indeed take `m=(h+1)/4`, `d=m²/v`; conversely any original witness yields (2). This tests suitably small factors of the shifted number `4vp+1`, rather than enumerating all `d∣m²` and testing `p+4d`. It is a second genuinely exact arithmetic search axis, **not** a consequence of quadratic nonresidue alone. For instance `p=193,m=3,h=11` has `(p/h)=−1` but `d∈{1,3,9}` produces none of the exact residues; a negative Jacobi character does not produce (2).

## Stress tests, including a false bounded-cofactor shortcut

All displayed `p` are prime, congruent to `1 mod 24` (trial-division primality is checked in the audit). The **least possible cofactor `v`** in (1) is obtained by exhaustively testing every `v` below it and every eligible `m` that is a multiple of `ρ(v)`; the first `m` at the least `v` is displayed. The audit independently checks both congruences, `d∣m²`, and `4d<p`.

| `p` | least `v` | `m` | `d=m²/v` | `h=4m−1` | `(4vp+1)/h` |
|---:|---:|---:|---:|---:|---:|
| 73 | 2 | 4 | 8 | 15 | 39 |
| 193 | 2 | 4 | 8 | 15 | 103 |
| 241 | 3 | 3 | 3 | 11 | 263 |
| 2521 | 9 | 12 | 16 | 47 | 1931 |
| 66529 | 2 | 10 | 50 | 39 | 13647 |
| 1726201 | 144 | 5748 | 229441 | 22991 | 43247 |

**Counterexample only to a proposed shortcut:** prime `p=1726201` has **no** cofactor `1≤v≤64`, despite having a full Type-II witness `(m,d,v)=(60,24,150)` with `239∣p+96`. It also has the displayed cofactor-144 witness. The audit's negative search at `v≤64` is complete because `m≤min((p−1)/6,⌊√((vp−1)/4)⌋)` and `ρ(v)∣m`; the latter two conditions list *all* possible `m`. This is not a counterexample to the full assertion, nor to Erdős–Straus. It refutes, for example, the tempting assertion that a bounded tiny complementary divisor always suffices. No claim that **every fixed** cofactor cutoff fails at some prime follows from this single example.

For an odd square `n=s²≡1 (mod 24)`, the entire full Type-II axis fails at **every** `m`, not merely in the script's sample checks (`s=5,7,11,1000001`). The known Jacobi argument: every prime factor of `m`, hence every `d∣m²`, has symbol `(d/h)=1` for `h=4m−1`. A putative witness would force `(n/h)=(-4d/h)=−1`, contradicting `(s²/h)∈{0,1}`. In particular, a theorem that tries to force the factor (2) *for all odd inputs* is false. Primality or at least a suitable nonsquare condition is indispensable.

## Why character sums still do not force a prime witness

For fixed `V≥1` and `p≡1 (mod 24)`, define `M_v(p)=min(⌊(p−1)/6⌋,⌊√((vp−1)/4)⌋)` and the exact count

    C_V(p)=Σ_{v≤V} Σ_{m≤M_v(p), ρ(v)|m} [4m−1 | 4vp+1].

Additive-character orthogonality gives `C_V=D_V+R_V`, where

    D_V(p)=Σ_{v≤V} Σ_{m≤M_v(p), ρ(v)|m} 1/(4m−1),
    R_V(p)=Σ_{v≤V} Σ_{m≤M_v(p), ρ(v)|m}
                (1/(4m−1)) Σ_{r=1}^{4m−2} exp(2πi r(4vp+1)/(4m−1)).

For fixed `V` and `p→∞`, `D_V(p)=(log p)/8·Σ_{v≤V}1/ρ(v)+O_V(1)`: write `m=ρ(v)t`, apply harmonic summation, and note that the square-root bound eventually dominates the linear `m≤(p−1)/6` bound. Nevertheless **`D_V` is not a pointwise lower bound**: every odd square has `R_V=−D_V` for all `V`, and the certified prime `1726201` has `R_64=−D_64`.

Even correcting the quadratic-character main term does not rescue this shortcut. For hard prime `p`, each eligible `h=4m−1` is less than `p`, so `(p/h)∈{±1}`; quadratic reciprocity shows `(v/h)=1` when `v∣m²`. The required residue `t=−(4v)⁻¹ (mod h)` has `(t/h)=−1`. Orthogonality of characters of `(ℤ/hℤ)×` gives an exact decomposition `C_V=M_V+E_V`, where the principal **plus Jacobi** terms are

    M_V(p)=Σ_{v≤V} Σ_{m≤M_v(p), ρ(v)|m} (1−(p/(4m−1)))/φ(4m−1),

and `E_V` includes **all remaining** characters (not merely one quadratic character). For the prime `1726201`, take `v=m=5`, `h=19`: `p≡13 (mod 19)` is a quadratic *nonresidue* (the residues are `1,4,5,6,7,9,11,16,17`), but the cofactor congruence fails. Hence this term alone makes `M_64≥2/φ(19)=1/9`, while the complete `v≤64` check gives `C_64=0` and `E_64=−M_64`. So even an explicitly positive *pointwise Jacobi-corrected* main term need not be a witness count. The simpler `p=193,m=3` similarly has the right negative sign but none of its exact `d∈{1,3,9}` works. Standard mean prime-distribution or positive main-term estimates still require a new *pointwise* bound on the full nonquadratic error that beats this cancellation. Neither the present argument nor existing mean estimates supply it.

**Verification:** `lake env lean Submission/ReciprocalCofactor.lean` and `lake build Submission.ReciprocalCofactor` succeed. `#print axioms` for both new theorems lists only `propext`, `Classical.choice`, and `Quot.sound`, not `sorryAx`. This remains a useful exact reparametrization plus a checkable barrier, **not** the universally quantified Type-II theorem.
