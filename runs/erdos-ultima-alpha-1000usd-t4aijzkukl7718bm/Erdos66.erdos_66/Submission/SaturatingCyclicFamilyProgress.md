# Finite saturation: adding a full-residue level

## Original task status

The original conjecture is not settled. `Submission/Spec.lean` is unchanged
and still contains its original `sorry`. No proof or disproof was submitted.

## New checked finite result

`SaturatingCyclicFamilyExplore.lean` compiles. It contains:

- `cyclicCount_total`: the total mixed cyclic count is |C|*|D|.
- `actualMean_error`: a uniform nominal-mean error also bounds the difference
  between the nominal mean and the exact cardinality mean |C|*|D|/M.
- `normalize_to_actualMean`: nominal relative error eta<=1/2 becomes exact-
  cardinality relative error at most 4eta.
- `saturate_mixed_flat`: append the full group to any bounded-index mixed-flat
  family. All new mixed counts are exact: C*G=|C| and G*D=|D|.
- `exists_saturating_family`: for each epsilon>0 and H there is beta>0,
  fixed BEFORE the arbitrarily large modulus, and nested C_i with C_0 empty,
  C_(H+1) full, old levels i,j<=H having nominal means beta*i*j and relative
  error <=epsilon, and ALL levels having relative error <=epsilon about the
  exact cardinality mean. Fixing beta before M is essential: the old levels
  remain genuinely sparse as M grows.
- `cardWeight_mul`: w(C)=|C|/sqrt(M) gives actualMean(C,D)=w(C)w(D).
- `saturating_carry_error`: after K outer repetitions, separate carry fibers
  have main terms r*w(C)w(D) and (K-r)*w(C)w(D), with error at most
  (K*eta+1+eta)*w(C)w(D), including the full-residue level.

The main results pass `SaturatingCyclicFamilyAxiomCheck.lean`, using only
propext, Classical.choice, and Quot.sound.

## Why examine saturation?

A proposed hierarchy could eventually erase every old residue restriction,
avoiding the obstruction to permanently retaining one nonuniform modular
pattern. The finite algebra does permit a full-residue level alongside the
sparse old family; the new mixed estimates do not require selecting a new
prime or guessing an unrelated-period root formula.

## What remains missing

This is NOT a placement theorem. Full residues in an integer block create
an actual interval of points. The new cardinality-normalized weights record
its large mass; that mass cannot be treated as the old sparse weight.

To use saturation in an infinite construction, one still needs a high-block
selection and density schedule controlling the weighted self-convolution
at every target, keeping the old accurate prefix, and avoiding gaps. No
such schedule has been proved. The full level is a discrete large jump,
not a continuum of automatically compatible intermediate levels.

Sparse Cartesian high-block selection is not covered by the previously
proved complete-period repetition obstruction, but this observation does
not establish that it works. Likewise, literal anchored parabola encoding
retains the already-proved initial-row gap; inserting the full OLD residue
level does not by itself remove that NEW-coordinate gap.

No original existential conclusion or universal negation follows from this
finite saturation step.
