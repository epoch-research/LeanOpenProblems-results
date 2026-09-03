import FormalConjecturesUtil

/-!
An exact obstruction to an elliptic matrix-trace candidate for Erdős Problem 714.
This is not a proof or disproof of Erdős Problem 714 itself.
-/

open SimpleGraph

namespace Erdos714MatrixCandidate

instance : Fact (Nat.Prime 29) := ⟨by decide⟩

variable {F : Type*} [Field F]

/-- Entries are in row-major order in a two-by-two matrix. -/
def det (x : Fin 4 → F) : F := x 0 * x 3 - x 1 * x 2

def trace (x : Fin 4 → F) : F := x 0 + x 3

/-- This is `Tr(adj(x) * y)`, and hence `Tr(x⁻¹*y)` when `det x = 1`. -/
def polar (x y : Fin 4 → F) : F :=
  x 0 * y 3 + x 3 * y 0 - x 1 * y 2 - x 2 * y 1

lemma polar_symm (x y : Fin 4 → F) : polar x y = polar y x := by
  unfold polar
  ring

/-- Nonzero weight, determinant one, and elliptic characteristic polynomial. -/
def valid (v : (Fin 4 → F) × F) : Prop :=
  v.2 ≠ 0 ∧ det v.1 = 1 ∧ ¬ IsSquare (trace v.1 ^ 2 - 4)

/-- The weighted trace relation, restricted to elliptic vertices and relative matrices. -/
def graph : SimpleGraph (Bool × ((Fin 4 → F) × F)) where
  Adj u v := u.1 ≠ v.1 ∧ valid u.2 ∧ valid v.2 ∧
    polar u.2.1 v.2.1 = u.2.2 * v.2.2 ∧
    ¬ IsSquare ((u.2.2 * v.2.2) ^ 2 - 4)
  symm := by
    intro u v h
    exact ⟨h.1.symm, h.2.2.1, h.2.1,
      by simpa only [polar_symm v.2.1 u.2.1, mul_comm] using h.2.2.2.1,
      by simpa only [mul_comm] using h.2.2.2.2⟩
  loopless := by intro v h; exact h.1 rfl

private def L : Fin 4 → Bool × ((Fin 4 → ZMod 29) × ZMod 29) := fun i =>
  (false, (![![15,4,27,15], ![15,25,2,15], ![2,8,25,28], ![2,21,4,28]] i, 15))

private def R : Fin 4 → Bool × ((Fin 4 → ZMod 29) × ZMod 29) := fun i =>
  (true, (![![15,10,5,15], ![4,28,14,4], ![4,1,15,4], ![15,19,24,15]] i,
    ![1,8,8,1] i))

private lemma all_edges (i j : Fin 4) : graph.Adj (L i) (R j) := by
  dsimp only [graph, valid]
  fin_cases i <;> fin_cases j <;> decide

private lemma L_injective : Function.Injective L := by decide

private lemma R_injective : Function.Injective R := by decide

/-- The witnesses are distinct even after normalizing a matrix by its weight. -/
private lemma L_normalized_injective :
    Function.Injective (fun i : Fin 4 => fun j : Fin 4 => (L i).2.1 j / (L i).2.2) := by
  decide

private lemma R_normalized_injective :
    Function.Injective (fun i : Fin 4 => fun j : Fin 4 => (R i).2.1 j / (R i).2.2) := by
  decide

/-- Even the elliptic restrictions do not make this candidate `K_{4,4}`-free. -/
theorem not_free :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free
      (graph (F := ZMod 29)) := by
  intro hfree
  apply hfree
  refine ⟨⟨⟨Sum.elim L R, ?_⟩, ?_⟩⟩
  · intro a b hab
    cases a with
    | inl i =>
      cases b with
      | inl j => simp at hab
      | inr j => exact all_edges i j
    | inr i =>
      cases b with
      | inl j => exact (all_edges j i).symm
      | inr j => simp at hab
  · intro a b hab
    cases a with
    | inl i =>
      cases b with
      | inl j => exact congrArg Sum.inl (L_injective hab)
      | inr j => exact False.elim (Bool.false_ne_true (congrArg Prod.fst hab))
    | inr i =>
      cases b with
      | inl j => exact False.elim (Bool.false_ne_true (congrArg Prod.fst hab).symm)
      | inr j => exact congrArg Sum.inr (R_injective hab)

#print axioms not_free

end Erdos714MatrixCandidate
