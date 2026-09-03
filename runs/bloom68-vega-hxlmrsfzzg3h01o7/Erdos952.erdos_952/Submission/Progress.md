# Erdős 952: verified partial progress

The unrestricted theorem and its negation in `Spec.lean` remain unproved. That
file has not been changed, including its imports and both theorem statements.

## Strongest completed Lean result

`WallBound.lean` proves:

```lean
Erdos952.no_bounded_step_sequence_of_bound_le_eight {C : ℤ} (hC : C ≤ 8) :
  ¬ ∃ x : ℕ → GaussianInt, Function.Injective x ∧
    ∀ n, Prime (x n) ∧ (x (n + 1) - x n).norm < C
```

It also proves `Erdos952.nine_le_bound_of_witness`. Thus an unrestricted witness
would necessarily have `C ≥ 9`. The strict inequality is important: the proof
excludes squared steps below 8, not squared steps at most 8.

All three main results in `WallBound.lean` have only the axioms `propext`,
`Classical.choice`, and `Quot.sound`. They do not depend on `Submission.Spec`.

## All-bound fixed-strip result

`StripBound.lean` also proves, for arbitrary integers `C`, `a`, and `b`:

```lean
Erdos952.no_bounded_step_prime_sequence_in_horizontal_strip (C a b : ℤ) :
  ¬ ∃ x : ℕ → GaussianInt, Function.Injective x ∧
    (∀ n, Prime (x n) ∧ (x (n + 1) - x n).norm < C) ∧
    (∀ n, a ≤ (x n).im ∧ (x n).im ≤ b)
```

`StripCRT.lean` constructs periodic translates of any finite pattern whose
points have fixed nonunit divisors of bounded norm. The moduli are pairwise
coprime Fermat numbers; their primality is not assumed. Applying this to a
rectangular crosscut and removing the finite exceptional prime set traps a
bounded-step prime tail in one finite rectangle.

Both modules were independently rebuilt with implicit variables disabled, and
their interfaces, edge cases, and exported axiom sets were checked. Their
proofs depend only on `propext`, `Classical.choice`, and `Quot.sound`.

This result requires confinement to a **fixed horizontal strip**. It does not
exclude paths with unbounded imaginary coordinates. Periodic CRT-translated
holes alone do not supply an enclosing moat for an unrestricted path.

## Sharp finite-residue packing

`ResiduePacking.lean` proves a generic, prime-independent obstruction: an
injective Gaussian path with `m+1` vertices, squared steps `< C`, and
`m^2 * C ≤ d.norm` must have `m+1` distinct labels whenever equal labels imply
that `d` divides the corresponding difference. Here `d ≠ 0`; both real and
integer bounds are supported. The constant is exactly `m^2`, without an
extra factor of two.

The source, its consumer tests, strict-threshold counterexample, and all
exported axiom audits were independently checked. Records are in
`.lake/build/ResiduePackingVerification.json` and
`.lake/build/ResiduePacking.parent-*.log`. This theorem does **not** supply the
small joint residue-image bound needed to settle arbitrary prime paths.

## Actual-prime step-context obstruction

The independent development in `../ResearchScratch/FreshPrimeRecurrence.lean`
proves that every position in an injective sequence of actual Gaussian primes
has a finite block of consecutive differences occurring only at that position:

```lean
FreshPrimeRecurrence.prime_steps_have_unique_context
    (x : ℕ → GaussianInt) (hx : Function.Injective x)
    (hp : ∀ n, Prime (x n)) (a : ℕ) :
    ∃ L > 0, ∀ n, FreshPrimeRecurrence.SameSteps x a n L → n = a
```

No step-size hypothesis is needed. In particular, no tail of such a sequence
has a recurrent step word. The finite-residue translation argument and all
exported conclusions were independently rebuilt and axiom-audited.

This does **not** prove the conjecture's negation. The companion development
`../ResearchScratch/BoundedNonrecurrentPath.lean` formally constructs an
injective path with squared steps below three and the same unique-context
property. Its points are not all prime. A recurrent word obtained by taking
limits of translated prime-path tails need not be realized by an actual
prime path at any integer translate.

Details and rebuild commands are in
`../ResearchScratch/FreshRecurrenceResult.md`; the independent parent audit is
`../ResearchScratch/FreshRecurrenceVerification.parent.json`.

## Same-bound removal of associate repetitions

The independent `../ResearchScratch/NonassociatePrimePath.lean` now proves
that any hypothetical witness can be replaced by a prime path with the same
initial vertex and the **same strict squared-step bound**, with no repeated
associate classes. Its distinct vertices are literally pairwise `IsCoprime`.

```lean
NonassociatePrimePath.exists_nonassociate_prime_path
    (x : ℕ → GaussianInt) (C : ℤ)
    (hx : Function.Injective x) (hp : ∀ n, Prime (x n))
    (hstep : ∀ n, (x (n + 1) - x n).norm < C) :
    ∃ y : ℕ → GaussianInt, y 0 = x 0 ∧
      (∀ n, Prime (y n)) ∧
      (∀ n, (y (n + 1) - y n).norm < C) ∧
      (∀ i j, Associated (y i) (y j) → i = j) ∧
      Function.Injective y ∧ Pairwise (fun i j => IsCoprime (y i) (y j))
```

The proof erases loops in the finite-fiber association quotient, then lifts
by cumulative unit rotations. Each new edge has exactly the squared norm of
an original consecutive edge. Directly deleting associated vertices would not
justify this assertion. A stronger exact lifting certificate does not require
primality or any step bound.

The parent read all source and independently rebuilt the module and its
consumer with implicit variables disabled and warnings treated as errors.
All twelve exported axiom checks use only the permitted foundations; neither
target theorem is even loaded by the consumer. Audit and hashes:
`../ResearchScratch/NonassociatePrimePathVerification.parent.json`.
This is a conditional reduction, not a proof or disproof of `Spec.lean`.


## Same-bound removal of repeated rational norm classes

`../ResearchScratch/CoprimeNormPrimePath.lean` strengthens the associate-only
reduction: a hypothetical witness can be replaced by one with the same root
and strict squared-step bound, whose integer norms are pairwise `IsCoprime`
and injective. The proof uses nonexpansive first-octant folding, finite-fiber
last-visit erasure, and one fixed symmetry to restore the root. Norms are
**not** claimed to be monotone.

The 312-line module and its consumer pass strict builds; six axiom checks use
only the permitted foundations. Neither target declaration is loaded.
Details: `../ResearchScratch/CoprimeNormPrimePathResult.md` and
`../ResearchScratch/CoprimeNormPrimePathVerification.json`.
This is another conditional reduction, not a settlement of `Spec.lean`.

## Proof components

- `FinitePotential.lean`: a general finite-potential obstruction.
- `SmallBound.lean`, `DiagonalArithmetic.lean`: Gaussian parity and nonunit-divisor facts.
- `DiscreteStream.lean`: explicit integer-grid integration of divergence-free currents.
- `WallCurrent.lean`: finite black walks give quotient currents.
- `WallObstruction.lean`: stream functions and a quarter-turn exclude infinite white king walks.
- `WallQuotient.lean`: the explicit quotient and sieve symmetries.
- `WallPrimeBridge.lean`: transfer from the white lattice to Gaussian primes.
- `WallData*.lean`: kernel verification of the 1,812,223-edge modular black wall.
- `WallBound.lean`: the combined unconditional partial theorem.
- `ProtectedWall.lean`: independently verified exact midpoint-filling and
  component correspondence, finite-fiber loop erasure, and a **conditional**
  next-scale obstruction. No protected-wall certificate has been supplied.

`ResearchCheckpoint.md` records the latest audit and the limitations of the
subsequent all-bound investigations. Its mathematical research notes are
separate from the Lean-certified results and do not settle the conjecture.

The wall data uses 443 chunks of packed natural numbers, each checked with
`decide +kernel`; no external checker or compiler-trust axiom is trusted by the
proof. The data certificate's independent provenance and build reports are in
`WallDataVerification.json`, `WallDataAudit.json`, and `WallDataBuildSummary.json`.
The modular wall's mathematical description is in `../sieve_d2/README.md`.

## Verification

With the compiled development dependencies present:

```sh
lake env lean Submission/WallBound.lean
lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false Submission/StripCRT.lean
lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false -DwarningAsError=true Submission/StripBound.lean
lake env lean .lake/build/StripCRTCheck.lean
lake env lean .lake/build/StripBoundCheck.lean
```

The parent strip-module checks and source hashes are recorded in
`.lake/build/StripVerification.json`; the individual logs have names
`.lake/build/StripCRT.parent-*.log` and `.lake/build/StripBound.parent-*.log`.

To rebuild the complete data certificate and development proof:

```sh
python3 Submission/WallDataCheck.py --full --jobs 8
for name in FinitePotential SmallBound DiagonalArithmetic DiscreteStream \
            WallCurrent WallObstruction WallQuotient WallPrimeBridge WallBound; do
  lake env lean -o ".lake/build/lib/lean/Submission/$name.olean" \
    "Submission/$name.lean" || exit 1
done
```

## Remaining gap

A fixed-width modular wall does not address arbitrarily large bounds. Larger
steps can cross it. Neither a scalable family of sufficiently thick walls nor
an alternative argument deciding the unrestricted statement has been proved.
No original-theorem or disproof claim has been submitted.
