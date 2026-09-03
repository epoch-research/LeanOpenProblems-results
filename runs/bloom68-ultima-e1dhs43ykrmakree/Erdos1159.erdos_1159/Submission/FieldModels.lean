import FormalConjecturesUtil

/-!
# Finite-field models of projective planes

For each prime `p`, the points and dual lines of `PG(2, p)` are both
`Projectivization (ZMod p) (Fin 3 → ZMod p)`.  The incidence relation and
projective-plane instance are those supplied by `Configuration.ofField`.
We supply a noncomputable `Fintype` instance and identify the order as `p`
by counting the points in two ways.

This file imports neither `Submission.Spec` nor `Submission.Counting`.
It constructs models only and does not settle Erdős Problem 1159.
-/

open Configuration

namespace Erdos1159.FieldModels

/-- Points, and also dual lines, of the projective plane over `ZMod p`. -/
abbrev Plane (p : ℕ) [Fact p.Prime] :=
  Projectivization (ZMod p) (Fin 3 → ZMod p)

/-- A chosen finite enumeration of the projective points. -/
noncomputable instance planeFintype (p : ℕ) [Fact p.Prime] : Fintype (Plane p) :=
  Fintype.ofFinite (Plane p)

/-- The existing field-construction instance, named for convenient explicit use. -/
noncomputable def planeProjectivePlane (p : ℕ) [Fact p.Prime] :
    ProjectivePlane (Plane p) (Plane p) :=
  inferInstance

/-- The three-dimensional vector space gives `p² + p + 1` projective points. -/
@[simp] theorem nat_card_plane (p : ℕ) [Fact p.Prime] :
    Nat.card (Plane p) = p ^ 2 + p + 1 := by
  have h := Projectivization.card_of_finrank (ZMod p) (Fin 3 → ZMod p)
    (Module.finrank_fin_fun (ZMod p) (n := 3))
  simpa [Finset.sum_range_succ, Nat.card_zmod, add_comm, add_left_comm, add_assoc] using h

/-- The point count in `Fintype.card` notation. -/
@[simp] theorem card_plane (p : ℕ) [Fact p.Prime] :
    Fintype.card (Plane p) = p ^ 2 + p + 1 := by
  rw [← Nat.card_eq_fintype_card, nat_card_plane]

/-- The order of the projective plane over the prime field `ZMod p` is `p`. -/
@[simp] theorem order_plane (p : ℕ) [Fact p.Prime] :
    ProjectivePlane.order (Plane p) (Plane p) = p := by
  have h := ProjectivePlane.card_points (Plane p) (Plane p)
  rw [card_plane] at h
  nlinarith

end Erdos1159.FieldModels
