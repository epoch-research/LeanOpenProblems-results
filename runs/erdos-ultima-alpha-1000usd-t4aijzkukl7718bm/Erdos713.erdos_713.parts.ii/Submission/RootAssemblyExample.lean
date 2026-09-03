import FormalConjecturesUtil
import Submission.RootAssembly

/-! Two non-complete seven-vertex three-side pieces, glued with roots in
opposite colour classes. This is a completed example, not a disproof. -/
open SimpleGraph
namespace Erdos713RootAssemblyExample
open Erdos713C6 Erdos713Gluing Erdos713Rate

def relation (i : Fin 3) (j : Fin 4) : Prop := i.val ≠ j.val
abbrev Piece := bipGraph relation

local instance : DecidableRel relation := fun i j => inferInstanceAs (Decidable (i.val ≠ j.val))

local instance : DecidableRel Erdos713C4.K22.Adj := by
  rintro (a | a) (b | b) <;> dsimp [Erdos713C4.K22,completeBipartiteGraph] <;> infer_instance

local instance : DecidableRel Piece.Adj := by
  rintro (a | a) (b | b) <;> dsimp [Piece,bipGraph,relation] <;> infer_instance

lemma piece_no_isolates : ∀ a, ∃ b, Piece.Adj a b := by decide
lemma piece_min_degree : ∀ a, 2 ≤ Piece.degree a := by decide

set_option synthInstance.maxSize 2048 in
noncomputable def rectangleCopy : Erdos713C4.K22.Copy Piece := by
  let f : Fin 2 ⊕ Fin 2 → Fin 3 ⊕ Fin 4 :=
    Sum.map (Fin.castLE (by decide : 2 ≤ 3)) (fun j => ![2,3] j)
  exact ⟨⟨f,by decide⟩,by decide⟩

lemma exceptional_card : Nat.card ({3} : Set (Fin 4)) ≤ 2 := by simp

lemma other_columns : ∀ b ∉ ({3} : Set (Fin 4)), Nat.card {a // relation a b} ≤ 2 := by
  have hh : ∀ b : Fin 4, b ≠ 3 → Fintype.card {a : Fin 3 // relation a b} ≤ 2 := by decide
  intro b hb
  simpa only [Nat.card_eq_fintype_card] using hh b hb

lemma piece_rate : HasRate Piece ((3 : ℝ)/2) :=
  two_exception_columns_rate relation {3} exceptional_card other_columns ⟨rectangleCopy⟩ (.refl _)

lemma piece_assembly : Erdos713RootAssembly.Assembly Piece := by
  have hc : Fintype.card {v : Fin 3 ⊕ Fin 4 // v.isLeft} ≤ 3 := by decide
  apply Erdos713RootAssembly.Assembly.side Piece {v | v.isLeft}
  · refine ⟨disjoint_compl_right,?_⟩
    rintro (a | a) (b | b) hab <;> simp_all [Piece,bipGraph]
  · simpa only [Nat.card_eq_fintype_card] using hc

def paired := wedge Piece (Sum.inl 0) Piece (Sum.inr 0)

lemma paired_assembly : Erdos713RootAssembly.Assembly paired :=
  .wedgeExceptional relation {3} exceptional_card other_columns
    Piece (Sum.inl 0) piece_no_isolates ⟨rectangleCopy⟩ (.refl _)
    Piece (Sum.inr 0) (piece_no_isolates _) piece_assembly

lemma paired_rate : HasRate paired ((3 : ℝ)/2) := by
  simpa only [max_self] using Erdos713RootPower.exceptional_columns_wedge_rate
    relation {3} exceptional_card other_columns Piece (Sum.inl 0) piece_no_isolates
    ⟨rectangleCopy⟩ (.refl _) Piece (Sum.inr 0) (piece_no_isolates _) piece_rate

lemma paired_card : Fintype.card (Erdos713Gluing.Vertex
    (Sum.inl 0 : Fin 3 ⊕ Fin 4) (Sum.inr 0 : Fin 3 ⊕ Fin 4)) = 13 := by decide

#print axioms paired_assembly
#print axioms paired_rate
end Erdos713RootAssemblyExample
