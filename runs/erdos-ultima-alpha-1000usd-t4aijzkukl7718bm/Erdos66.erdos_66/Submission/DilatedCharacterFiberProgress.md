# Same-field dilation control

The original conjecture remains unresolved. `Spec.lean` is unchanged.

`DilatedCharacterFiberExplore.lean` compiles and its principal theorems were
audited in `DilatedCharacterFiberAxiomCheck.lean`. Only `propext`,
`Classical.choice`, and `Quot.sound` occur.

For a nonzero field scalar t, dilating both parameter sets and the target
leaves their signed quadratic-character fiber unchanged. Consequently the
signed self-energy is exactly dilation invariant.

For translated parameter intervals of lengths h,k with self-energies at
most C h^2 and C k^2, positive integer dilations r,s (nonzero in the field)
satisfy

    (sum_z |crossCharFiber(r U_h, s U_k; z)|)^2
       <= C h k (r h + s k).

The support cardinality contributes r h+s k; the energy constant itself
does not increase. One selected translate controls all these dilations
simultaneously, as expressed by `exists_dilated_interval_fiber_control`.

Scope: this is a signed character-fiber theorem in one field. The theorem's
admissibility clause is only for the undilated intervals. It does not assert
that all dilated pairs avoid opposite parameters, repair all dilated origin
counts, control integer carry fibers, or compare different moduli.

In particular, it is not an infinite compatible construction and is not a
proof or disproof of `erdos_66`.
