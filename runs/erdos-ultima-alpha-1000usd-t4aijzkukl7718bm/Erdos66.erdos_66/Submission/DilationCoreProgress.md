# Dilation-invariant cores

The original conjecture is still unproved and undisproved. Spec.lean is
unchanged; no proof or disproof has been submitted.

## Checked necessary conditions

`DilationCoreExplore.lean` proves, for any hypothetical witness A:

* If m>0 and mB is contained in A, then for every epsilon>0, eventually

      count(B,N)/count(A,N) < 1/sqrt(m)+epsilon.

  The Lean expression for 1/sqrt(m) is sqrt(m)/m.

* If B is contained in A and is closed under multiplication by a fixed
  integer m>1, then

      count(B,N)/count(A,N) -> 0.

* If A=B union D with such a dilation-invariant B, then

      count(D,N)/count(A,N) -> 1.

  In particular a negligible augmentation cannot repair a dilation-invariant
  core, and a whole dilation-invariant set cannot be a witness.

* Closure under multiplication by all natural squares is an instance,
  already using the fixed dilation 4.

The proofs use the exact count ratio count(A,mN)/count(A,N)->sqrt(m),
and ordinary residue equidistribution. The image of B below N lies in one
residue class of A below mN. Iterating the dilation makes the allowable
relative mass tend to zero. No finite-state assumption on B is required.

## Construction review and remaining gap

Selecting arbitrary allowed squarefree kernels and taking their full square
closures cannot solve the conjecture, even if the selection uses unlimited
memory. The core theorem also excludes repairing such a set by an augmentation
of negligible counting mass.

This is a restriction on invariant cores, not a universal obstruction to
arbitrary A. Nonstationary digit constructions were reconsidered, but no
compatible family controlling all intermediate integer targets was obtained.
Coordinatewise products have the known cube peaks, while changing finite-field
encodings still lacks the needed mixed-count transfer. None of those speculative
steps is being asserted as a theorem.

## Verification

The file compiles and has a built olean. `DilationCoreAxiomCheck.lean` audits
all six main results. Each depends only on propext, Classical.choice, and
Quot.sound. No sorries or additional axioms occur in the new development.
