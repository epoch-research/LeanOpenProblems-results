import FormalConjecturesUtil

/-!
A Sidon embedding of the vertices of a C4-free graph does not in general make
its edge-sum Cayley lift K44-free. The counterexample below even uses a matching.
This auxiliary obstruction does not settle Erdős Problem 714.
-/

open SimpleGraph

namespace Erdos714SidonLift

set_option maxHeartbeats 8000000
set_option maxRecDepth 20000

/-- The strong Sidon condition, including sums with repeated summands. -/
def Sidon {V A : Type*} [Add A] (a : V → A) : Prop :=
  ∀ i j k l, a i + a j = a k + a l → (i = k ∧ j = l) ∨ (i = l ∧ j = k)

/-- The bipartite Cayley lift whose connections are the sums along auxiliary edges. -/
def sumLift {V A : Type*} [Add A] (a : V → A) (H : SimpleGraph V) :
    SimpleGraph (A ⊕ A) where
  Adj x y := match x, y with
    | .inl u, .inr v => ∃ i j, H.Adj i j ∧ u + v = a i + a j
    | .inr v, .inl u => ∃ i j, H.Adj i j ∧ u + v = a i + a j
    | _, _ => False
  symm := by intro x y; cases x <;> cases y <;> simp_all
  loopless := by intro x; cases x <;> simp

/-- Seven disjoint pairs. -/
def matching : SimpleGraph (Fin 14) where
  Adj i j := i.val / 2 = j.val / 2 ∧ i ≠ j
  symm := by rintro i j ⟨h, hn⟩; exact ⟨h.symm, hn.symm⟩
  loopless := by intro i h; exact h.2 rfl

lemma matching_neighbor_unique : ∀ i j k : Fin 14,
    matching.Adj i j → matching.Adj i k → j = k := by
  dsimp only [matching]
  decide

/-- In particular, the auxiliary graph is C4-free. -/
theorem matching_free :
    (completeBipartiteGraph (Fin 2) (Fin 2)).Free matching := by
  rintro ⟨f⟩
  have h0 := f.toHom.map_adj (show
    (completeBipartiteGraph (Fin 2) (Fin 2)).Adj (.inl 0) (.inr 0) by simp)
  have h1 := f.toHom.map_adj (show
    (completeBipartiteGraph (Fin 2) (Fin 2)).Adj (.inl 0) (.inr 1) by simp)
  have h := f.injective (matching_neighbor_unique _ _ _ h0 h1)
  simp at h

/-- A small Sidon set in a finite cyclic group. Consecutive pairs sum to 1,...,7. -/
def labels : Fin 14 → ZMod 593 :=
  ![10, -9, 17, -15, 26, -23, 37, -33, 82, -77, 119, -113, 148, -141]

lemma labels_injective : Function.Injective labels := by decide

/-- Exhaustive finite arithmetic is checked by Lean's kernel, not native evaluation. -/
theorem labels_sidon : Sidon labels := by
  unfold Sidon
  decide

/-- Every integer in [1,7] is an auxiliary edge sum. -/
lemma grid_edges (i j : Fin 4) :
    (sumLift labels matching).Adj (.inl (i.val : ZMod 593))
      (.inr ((j.val : ZMod 593) + 1)) := by
  dsimp only [sumLift, matching]
  fin_cases i <;> fin_cases j <;> decide

/-- The four rows 0,1,2,3 and columns 1,2,3,4 form a biclique in the lift. -/
def gridCopy : Copy (completeBipartiteGraph (Fin 4) (Fin 4)) (sumLift labels matching) := by
  let L : Fin 4 ↪ ZMod 593 := ⟨fun i => (i.val : ZMod 593), by decide⟩
  let R : Fin 4 ↪ ZMod 593 := ⟨fun i => (i.val : ZMod 593) + 1, by decide⟩
  refine ⟨⟨L.sumMap R, ?_⟩, (L.sumMap R).injective⟩
  intro a b hab
  cases a with
  | inl i =>
    cases b with
    | inl j => simp at hab
    | inr j => exact grid_edges i j
  | inr j =>
    cases b with
    | inl i => exact grid_edges i j
    | inr i => simp at hab

theorem lift_not_free :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free (sumLift labels matching) :=
  fun h => h ⟨gridCopy⟩

/-- A precise counterexample to the proposed Sidon/C4-free lifting implication. -/
theorem lifting_implication_false :
    ¬ (∀ a : Fin 14 → ZMod 593, Sidon a → ∀ H : SimpleGraph (Fin 14),
      (completeBipartiteGraph (Fin 2) (Fin 2)).Free H →
        (completeBipartiteGraph (Fin 4) (Fin 4)).Free (sumLift a H)) := by
  intro h
  exact lift_not_free (h labels labels_sidon matching matching_free)

#print axioms labels_sidon
#print axioms matching_free
#print axioms gridCopy
#print axioms lifting_implication_false

end Erdos714SidonLift
