import Submission.GraphSubdivision

/-! Injective edge coordinates for a single-edge series subdivision. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.GraphSubdivision
open Erdos184Serial
set_option maxHeartbeats 1800000
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false
variable {V : Type*} [Fintype V] [DecidableEq V]

def edgeMap (a b : V) : Sym2 V ⊕ Unit → Sym2 (V ⊕ Unit)
  | .inl e => if e = s(a,b) then s(Sum.inl a,Sum.inr ()) else e.map Sum.inl
  | .inr _ => s(Sum.inl b,Sum.inr ())

lemma edgeMap_eq_old (a b x y : V) (e : Sym2 V ⊕ Unit) :
    edgeMap a b e = s(Sum.inl x,Sum.inl y) ↔ e = .inl s(x,y) ∧ s(x,y) ≠ s(a,b) := by
  cases e with
  | inl e =>
    by_cases he : e = s(a,b)
    · simp [edgeMap,he,Sym2.eq_iff]
      tauto
    · simp only [edgeMap,if_neg he,Sum.inl.injEq]
      have hm : e.map (Sum.inl : V → V ⊕ Unit) = s(Sum.inl x,Sum.inl y) ↔ e = s(x,y) := by
        rw [← Sym2.map_pair_eq]
        exact (Sym2.map.injective Sum.inl_injective).eq_iff
      rw [hm]
      constructor
      · intro h
        exact ⟨h,h ▸ he⟩
      · exact And.left
  | inr u => simp [edgeMap,Sym2.eq_iff]

lemma edgeMap_eq_cross (a b x : V) (e : Sym2 V ⊕ Unit) :
    edgeMap a b e = s(Sum.inl x,Sum.inr ()) ↔
      (e = .inl s(a,b) ∧ x = a) ∨ (e = .inr () ∧ x = b) := by
  cases e with
  | inl e =>
    by_cases he : e = s(a,b)
    · subst e
      simp [edgeMap,Sym2.eq_iff,eq_comm]
    · simp only [edgeMap,if_neg he,Sum.inl.injEq,he,false_and,Sum.inl_ne_inr,false_or,iff_false]
      induction e using Sym2.ind with | h u v =>
      simp [Sym2.map_pair_eq]
  | inr u => cases u; simp [edgeMap,Sym2.eq_iff,eq_comm]

lemma edgeMap_ne_new (a b : V) (e : Sym2 V ⊕ Unit) :
    edgeMap a b e ≠ s(Sum.inr (),Sum.inr ()) := by
  cases e with
  | inl e =>
    induction e using Sym2.ind with | h x y =>
    by_cases he : s(x,y) = s(a,b) <;> simp [edgeMap,he,Sym2.map_pair_eq,Sym2.eq_iff]
  | inr u => simp [edgeMap,Sym2.eq_iff]

lemma edgeMap_injective {a b : V} (hab : a ≠ b) : Function.Injective (edgeMap a b) := by
  intro e f hef
  cases f with
  | inl f =>
    by_cases hf : f = s(a,b)
    · subst f
      have hx : edgeMap a b e = s(Sum.inl a,Sum.inr ()) := by simpa [edgeMap] using hef
      rcases (edgeMap_eq_cross a b a e).mp hx with h | h
      · exact h.1
      · exact (hab h.2).elim
    · induction f using Sym2.ind with | h x y =>
      have hx : edgeMap a b e = s(Sum.inl x,Sum.inl y) := by
        simpa only [edgeMap,if_neg hf,Sym2.map_pair_eq] using hef
      exact ((edgeMap_eq_old a b x y e).mp hx).1
  | inr u =>
    cases u
    have hx : edgeMap a b e = s(Sum.inl b,Sum.inr ()) := hef
    rcases (edgeMap_eq_cross a b b e).mp hx with h | h
    · exact (hab h.2.symm).elim
    · exact h.1

def edgeEmbedding {a b : V} (hab : a ≠ b) : Sym2 V ⊕ Unit ↪ Sym2 (V ⊕ Unit) :=
  ⟨edgeMap a b,edgeMap_injective hab⟩

private lemma exists_mem_eq_and {α : Type*} (S : Finset α) (a : α) (P : Prop) :
    (∃ z, z ∈ S ∧ z = a ∧ P) ↔ a ∈ S ∧ P := by
  constructor
  · rintro ⟨z,hz,rfl,hP⟩
    exact ⟨hz,hP⟩
  · rintro ⟨ha,hP⟩
    exact ⟨a,ha,rfl,hP⟩

lemma edgeFinset_split (G : SimpleGraph V) (t : Finset Unit) {a b : V} (hab : a ≠ b) :
    (split G t a b).edgeFinset = (G.edgeFinset.disjSum t).map (edgeEmbedding hab) := by
  ext e
  induction e using Sym2.ind with | h x y =>
  simp only [SimpleGraph.mem_edgeFinset,Finset.mem_map]
  change (split G t a b).Adj x y ↔ ∃ z, z ∈ G.edgeFinset.disjSum t ∧ edgeMap a b z = s(x,y)
  cases x with
  | inl x =>
    cases y with
    | inl y =>
      simp only [edgeMap_eq_old,exists_mem_eq_and,Finset.inl_mem_disjSum,SimpleGraph.mem_edgeFinset]
      rfl
    | inr u =>
      cases u
      simp only [edgeMap_eq_cross,and_or_left,exists_or,exists_mem_eq_and,
        Finset.inl_mem_disjSum,Finset.inr_mem_disjSum,SimpleGraph.mem_edgeFinset]
      change ((x = a ∧ G.Adj a b) ∨ (x = b ∧ () ∈ t)) ↔ _
      tauto
  | inr u =>
    cases u
    cases y with
    | inl y =>
      rw [show s(Sum.inr (),Sum.inl y) = s(Sum.inl y,Sum.inr ()) from Sym2.eq_swap]
      simp only [edgeMap_eq_cross,and_or_left,exists_or,exists_mem_eq_and,
        Finset.inl_mem_disjSum,Finset.inr_mem_disjSum,SimpleGraph.mem_edgeFinset]
      change ((y = a ∧ G.Adj a b) ∨ (y = b ∧ () ∈ t)) ↔ _
      tauto
    | inr u =>
      cases u
      simp only [edgeMap_ne_new,and_false,exists_false]
      rfl

#print axioms edgeMap_injective
#print axioms edgeFinset_split
end Erdos184Work.GraphSubdivision
