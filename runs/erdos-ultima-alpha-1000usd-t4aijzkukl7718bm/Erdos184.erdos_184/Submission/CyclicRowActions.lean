import Mathlib.Data.Fin.Basic
import Mathlib.Data.Sym.Sym2
import Mathlib.Logic.Equiv.Basic
import Mathlib.Algebra.BigOperators.Fin

/-! Reindexing cyclic rows with independent edge permutations.
This numerical interface makes no assertion that all graph layouts are covered. -/
namespace Erdos184Work.CyclicRowActions
set_option maxHeartbeats 500000
variable {I W : Type*} (length choices : I → ℕ) [∀ i, NeZero (length i)]

abbrev Rows := ∀ i, Fin (choices i)
abbrev Edges := Σ i, Fin (length i)

def source (word : ∀ i, Fin (choices i) → Fin (length i) → W)
    (q : Rows choices) (e : Edges length) : W := word e.1 (q e.1) e.2

def target (word : ∀ i, Fin (choices i) → Fin (length i) → W)
    (q : Rows choices) (e : Edges length) : W := word e.1 (q e.1) (e.2 + 1)

structure Action (word : ∀ i, Fin (choices i) → Fin (length i) → W) where
  color : I ≃ I
  vertex : W ↪ W
  row : ∀ i, Fin (choices i) → Fin (choices (color i))
  edge : ∀ i, Fin (choices i) → (Fin (length i) ≃ Fin (length (color i)))
  endpoints : ∀ i q j,
    s(vertex (word i q j),vertex (word i q (j + 1))) =
      s(word (color i) (row i q) (edge i q j),
        word (color i) (row i q) (edge i q j + 1))

namespace Action
variable {length choices} {word : ∀ i, Fin (choices i) → Fin (length i) → W}
    (a : Action length choices word)

def apply (q : Rows choices) : Rows choices :=
  Equiv.piCongrLeft (fun i => Fin (choices i)) a.color (fun i => a.row i (q i))

lemma apply_color (q : Rows choices) (i : I) :
    a.apply q (a.color i) = a.row i (q i) := by
  simp only [apply,Equiv.piCongrLeft_apply_apply]

def edgeEquiv (q : Rows choices) : Edges length ≃ Edges length :=
  Equiv.sigmaCongr a.color (fun i => a.edge i (q i))

lemma edge_color (q : Rows choices) (e : Edges length) :
    (a.edgeEquiv q e).1 = a.color e.1 := rfl

lemma endpoints_apply (q : Rows choices) (e : Edges length) :
    s(a.vertex (source length choices word q e),a.vertex (target length choices word q e)) =
      s(source length choices word (a.apply q) (a.edgeEquiv q e),
        target length choices word (a.apply q) (a.edgeEquiv q e)) := by
  rcases e with ⟨i,j⟩
  change s(a.vertex (word i (q i) j),a.vertex (word i (q i) (j+1))) =
    s(word (a.color i) (a.apply q (a.color i)) (a.edge i (q i) j),
      word (a.color i) (a.apply q (a.color i)) (a.edge i (q i) j + 1))
  rw [apply_color]
  exact a.endpoints i (q i) j

end Action
#print axioms Action.endpoints_apply
end Erdos184Work.CyclicRowActions
