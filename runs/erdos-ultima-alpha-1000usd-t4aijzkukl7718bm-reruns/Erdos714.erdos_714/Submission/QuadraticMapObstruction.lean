import Submission.QuadraticSignedCount

/-!
Actual Mathlib quadratic maps over odd-characteristic fields satisfy the
signed-fiber obstruction. In particular the base field may remain F3 while
its vector-space dimensions grow. This does not treat arbitrary affine or
asymmetric restrictions and does not settle Erdős 714.
-/
noncomputable section
open Classical Finset SimpleGraph
set_option maxHeartbeats 2000000
namespace Erdos714QuadraticMapObstruction
open Erdos714Packing Erdos714SignedQuadratic
variable {F V W : Type*} [Field F] [AddCommGroup V] [AddCommGroup W]
variable [Module F V] [Module F W]

lemma double_injective (h2 : (2:F)≠0) : Function.Injective (fun x:V => x+x) := by
  intro x y h
  apply smul_right_injective V h2
  simpa only [two_smul F] using h

lemma parallelogram (Q : QuadraticMap F V W) (x y : V) :
    Q (x+y)+Q (x-y)=(Q x+Q y)+(Q x+Q y) := by
  have h := Q.map_add_add_add_map x y (-y)
  simp only [add_neg_cancel_right,add_neg_cancel,Q.map_zero,add_zero,Q.map_neg] at h
  rw [neg_add_eq_sub] at h
  convert h.symm using 1
  abel

variable [Fintype V] [Fintype W]

/-- A complete finite inequality for the actual quadratic-map translation graph. -/
theorem fiber_cubic_bound (Q : QuadraticMap F V W) (c : W) (h2 : (2:F)≠0)
    (C : ℕ) (hC : 1≤C)
    (hbal : ∀ w, Fintype.card {x : V // Q x=w}≤C*(level Q c).card)
    (hf : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (incidence (connectionRows Q c))) :
    (level Q c).card^3≤576*C*(Fintype.card V)^2 :=
  balanced_fiber_cubic_bound (double_injective h2) Q c Q.map_neg
    (double_injective h2) (parallelogram Q) C hC hbal hf

/-- A hypothetical critical-size family of these balanced quadratic fibers
has an explicitly bounded field-size parameter. -/
theorem critical_parameter_bound (Q : QuadraticMap F V W) (c : W) (h2 : (2:F)≠0)
    (C D q : ℕ) (hC : 1≤C) (hN : Fintype.card V≤q^4)
    (hs : q^3≤D*(level Q c).card)
    (hbal : ∀ w, Fintype.card {x : V // Q x=w}≤C*(level Q c).card)
    (hf : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (incidence (connectionRows Q c))) :
    q≤576*C*D^3 := by
  have hb := fiber_cubic_bound Q c h2 C hC hbal hf
  have h : q^9≤576*C*D^3*q^8 := by
    calc
      _ = (q^3)^3 := by ring
      _ ≤ (D*(level Q c).card)^3 := Nat.pow_le_pow_left hs 3
      _ = D^3*(level Q c).card^3 := by ring
      _ ≤ D^3*(576*C*(Fintype.card V)^2) := Nat.mul_le_mul_left _ hb
      _ ≤ D^3*(576*C*(q^4)^2) := by gcongr
      _ = _ := by ring
  by_cases hq : q=0
  · simp [hq]
  · apply Nat.le_of_mul_le_mul_right (c := q^8) _ (pow_pos (Nat.pos_of_ne_zero hq) 8)
    convert h using 1
    ring

/-- This covers growing-dimensional F3-quadratic maps, where the earlier
single affine-line obstruction yields only three vertices, not four. -/
theorem ternary_parameter_bound (m C D : ℕ)
    (Q : QuadraticMap (ZMod 3) (Fin (4*m) → ZMod 3) (Fin m → ZMod 3))
    (c : Fin m → ZMod 3) (hC : 1≤C)
    (hs : (3^m)^3≤D*(level Q c).card)
    (hbal : ∀ w, Fintype.card {x : Fin (4*m) → ZMod 3 // Q x=w}≤C*(level Q c).card)
    (hf : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (incidence (connectionRows Q c))) :
    3^m≤576*C*D^3 := by
  apply critical_parameter_bound Q c (by decide) C D (3^m) hC _ hs _ hf
  · simp only [Fintype.card_fun,Fintype.card_fin,ZMod.card,← pow_mul]
    rw [Nat.mul_comm 4 m]
  · intro w
    convert hbal w using 1
    congr 1
    exact Subsingleton.elim _ _


#print axioms fiber_cubic_bound
#print axioms critical_parameter_bound
#print axioms ternary_parameter_bound
end Erdos714QuadraticMapObstruction
