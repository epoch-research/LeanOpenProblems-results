# A genuine but non-covering induction on square-divisor certificates

**Status:** `QuarterDescent.lean` proves two restricted lifts to strictly ordered Erdős–Straus solutions, an easy-prime-to-hard-prime example, and a hard-prime-to-hard-prime example. It also *proves* that this particular induction cannot cover every hard prime: `p=97` has no compatible smaller-input certificate, despite both `Good 25` and `Good 97`. An alternative `n↦n+4` carry is obstructed. **No universal Erdős–Straus theorem, counterexample, or proof that the original `sorry` is fillable is claimed.** `Spec.lean` was neither imported nor changed.

## The conditional `q↦4q−3` lift

Take `q+a=4s` with `a>0` and `2s<q`. Put `p=4q−3` and `X=4s`. The new first-denominator modulus is exactly

    4X−p = 4a+3 =: b.

The *strict* first-denominator interval is automatic: `p<4X` and `2X<p` (the latter follows from the integer inequality `q≥2s+1`). In particular `p>q`, so a proof from an appropriate certificate for `q` really is a descent step, rather than circular reuse of a result for `p`.

**Type II: preserve the square divisor.** Suppose `0<d<s`, `d|s²`, and `s+d=a m`. We reuse `d` at `X`; then `d|X²`, `0<d<X`, and the *exact* Euclidean identity

    b m = (4s+d) + 3(m+d)

proves

    b | X+d   ↔   b | 3(m+d).                                    (II)

This equivalence, `quarter_typeII_divisibility_iff`, checks the genuine integrality requirement; the right side does **not** follow from the certificate for `q`. Given (II) and primality of `p`, `typeII_quarter_lift` and `good_of_typeII_quarter_lift` produce strictly ordered *integer* denominators using the fully proved `good_of_typeII` construction. Primality of `q` is not required for the certificate-level lift; obtaining a Type-II source certificate merely from `Good q` when `q` is composite is another unjustified step.

**Type I: multiply the square cofactor by four.** Suppose `c>0`, `c|s²`, `4c+1=a m`. Use `C=4c`, which divides `X²=16s²`. The exact identity

    b m = (4C+1) + 3(m+1)

proves

    b | 4C+1   ↔   b | 3(m+1).                                    (I)

`quarter_typeI_divisibility_iff`, `typeI_quarter_lift`, and `good_of_typeI_quarter_lift` prove this step and **both** ordered `Good q` and ordered `Good p`; no primality is needed in Type I. The source predicate permits the full `c|s²` branch, not merely `c|s`. `QuarterCompatible q s` explicitly includes the source square-divisor requirements *and* the additional congruence in either (I) or (II). `good_of_quarter_compatible` proves the conditional implication for prime `p=4q−3`. It does **not** assert compatibility at every prime and does not use `Good q → Good p` as an axiom.

## Exact positive cases, with strict order checked

* **Type II, a residual hard prime:** `q=1303` and `p=5209=4q−3` are primes. Set `s=327`, `a=5`, `d=3`, `m=66`; then `327+3=5·66`, `3|327²`, and `b=23|3(66+3)=207`. The target has `X=1308`, `b|X+d=1311`, and the certified strictly increasing decompositions are

      4/1303 = 1/327 + 1/85998 + 1/9373782,
      4/5209 = 1/1308 + 1/296913 + 1/129454068.

  `quarter_typeII_5209` checks both certificates, both primalities and both `Good` predicates; `quarter_5209_explicit_fractions` independently checks the numeric order and exact rational equalities. This `p` is `169 (mod 840)` and `6 (mod 11)`, while `p+4=5213=13·401` has only prime factors `1 (mod 4)` (`quarter_5209_residual_data`). Thus the example is not just the `d=1` divisor-of-`p+4` shortcut.

* **Type I between two hard primes:** `q=16633` and `p=66529=4q−3` are prime and `1 (mod 24)`. Take `s=4160`, `a=7`, `c=1300`, `m=743`; `4c+1=5201=7·743` and `b=31|3(743+1)=2232`. The target is `X=16640`, `C=5200`, `4C+1=20801=31·671`. The strictly ordered decompositions are

      4/16633 = 1/4160 + 1/9886656 + 1/51388984140,
      4/66529 = 1/16640 + 1/35712768 + 1/742479606960.

  `quarter_typeI_66529` checks both full square-divisor certificates, primes, and ordered `Good`; `quarter_66529_explicit_fractions` checks the displayed fractions and strict inequalities separately.

In both cases the standard `Classification.good_of_typeI`/`good_of_typeII` theorems establish **integrality of all quotients**, positive natural denominators, `x<y<z`, and the exact rational identity, not just a formal rational rescaling. The displayed triples were also independently recomputed with integer quotients and Python's exact `fractions.Fraction` arithmetic.

## Where induction *fails*, rather than merely remaining unproved

For `q=631`, `p=2521` (both prime), the smaller number has a Type-II certificate at `s=158`, `d=1`, `a=1`, `m=159`. The proposed target is `X=632`, `b=7`; the required `7|3(159+1)=480` fails. More strongly, `quarter_2521_no_target_fiber` proves **neither complete Type I nor complete Type II** works at this eligible `X`: every divisor of `632²=2⁶·79²` has residue `1,2,4 (mod 7)`, while both targets require residue `5`. `quarter_2521_naive_induction_fails` proves `Good 631` and `Good 2521`; the latter has a different certificate at `X=636`, `d=8`. A failed *fiber* is not a prime counterexample, and this result alone would not exclude other possible source denominators.

We can exclude **all** source denominators for one selected prime, rather than just one fiber. For `q=25`, `p=97` (a hard prime), the source first denominators satisfy `7≤s≤12`. `no_quarter_compatible_25` proves `¬∃s, QuarterCompatible 25 s` for **both full source types**. Its finite sublemma is proved by kernel-checked `decide` over `s:Fin 13`, `c:Fin 145`, `d:Fin 13`, and the outer proof establishes the bounds `c≤s²≤144` and `d<s<13`; no infinite search is silently truncated. But

    4/25 = 1/7 + 1/60 + 1/2100,
    4/97 = 1/28 + 1/194 + 1/2716,

with strict order (`quarter_97_good_but_no_lift`). Indeed `quarter_25_no_source_fiber` proves both source types fail at `s=7` (all divisors of `7²` are `1 mod 3`), whereas `quarter_97_target_28_both_types` proves **both target types succeed** at `X=28`, using `C=56` or `d=2`. Thus even a *successful lifted first denominator* need not arise by preserving the source square divisor. In particular, **asserting that every hard prime has a `QuarterCompatible` source is false**, not a hidden equivalent assumption waiting to be proved.

Another natural predecessor induction is `q=p−4`, `s↦s+1`: its modulus `a=4s−q` stays constant. For `q≡1 (mod 4)`, `a≡3 (mod 4)` and `a≥3`. Reusing a Type-II divisor would force `a|s+d` and `a|s+d+1`, hence `a|1`, impossible (`no_plus_four_reuse_typeII`). Reusing a Type-I cofactor would require it to divide both `s²` and `(s+1)²`, so it equals one, but no `3 (mod 4)` positive integer divides `4·1+1=5` (`adjacent_square_common_divisor_eq_one`, `no_plus_four_reuse_typeI`). These are obstructions **only to unchanged auxiliary factors**: changing the factor or first denominator remains possible.

## Exact open obligation

The proved equivalence `CoveringGap.all_good_iff_explicit_hard_cover` still requires, for *every* prime `p=24k+1`, an index `0≤j<6k`, with `x=6k+1+j` and `a=4j+3`, satisfying at least one of

    (I)  ∃ c>0, c|x² and a|4c+1;
    (II) ∃ 0<d<x, d|x² and a|x+d.

Our two conditional transfers certify this for some `p` but provably miss `p=97` **as an induction method**, not as a solution. The `n+4` unchanged-factor steps also fail. Nothing proved here constructs a required divisor at *some* eligible first denominator of **every** hard prime, or rules out all denominators of any prime. Adding a hypothesis that simply asserts such universal covering, or assuming the unrestricted `Good((p+3)/4)→Good(p)` transfer, would restate the outstanding conjecture; neither is used.

**Verification:** `lake env lean Submission/QuarterDescent.lean`, `lake build Submission.QuarterDescent`, and `python3 Submission/QuarterDescentAudit.py` succeed; the file's `#print axioms` reports only `propext`, `Classical.choice`, `Quot.sound` (some finite lemmas need fewer), **no `sorryAx`, no `Lean.trustCompiler`, and no new axiom**. `Spec.lean` retains its original `sorry` declarations and is not imported or edited.
