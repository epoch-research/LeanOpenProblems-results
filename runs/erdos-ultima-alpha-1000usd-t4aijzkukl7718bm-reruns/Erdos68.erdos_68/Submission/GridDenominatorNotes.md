# Denominator bounds at grid changes (verified, not a settlement)

`GridDenominators.lean` proves two additional consequences of the existing
backward-grid lemma. They use only the permitted axioms.

For the indexing of `Development.lean`, if n>=1 and

    upperApprox (n+1) != upperApprox n,

then

    (upperApprox (n+1)).den does not divide (n+1)!,
    (upperApprox (n+1)).den >= n+2.

The theorem names are `upperApprox_change_den_not_dvd` and
`upperApprox_change_den_large`.

If the new denominator divided (n+1)!, the new rational value could be written
z/(n+1)!. The already verified `upperApprox_backward` would then force the old
approximation to equal the same value, contradicting the change. A positive
denominator at most n+1 divides (n+1)!, proving the numerical lower bound.

These bounds apply **only at change indices**. They neither prove infinitely
many changes nor bound the length of a subsequent constant block. Consequently
they do not prove denominator divergence or irrationality. `Spec.lean` remains
unchanged with its original `sorry`; no proof has been submitted.
