import Submission.GraphSerial
import Submission.CircuitTransport

/-! Edge-coordinate realization of the two-edge serial switch. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.GraphSerial
open Erdos184Serial
set_option maxHeartbeats 1800000
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false
variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]

def edgeMap (a b : V) (c d : W) : Sym2 V ⊕ Sym2 W → Sym2 (V ⊕ W)
  | .inl e => if e = s(a,b) then s(Sum.inl a,Sum.inr c) else e.map Sum.inl
  | .inr e => if e = s(c,d) then s(Sum.inl b,Sum.inr d) else e.map Sum.inr

lemma edgeMap_eq_left (a b x y : V) (c d : W) (e : Sym2 V ⊕ Sym2 W) :
    edgeMap a b c d e = s(Sum.inl x,Sum.inl y) ↔ e = .inl s(x,y) ∧ s(x,y) ≠ s(a,b) := by
  cases e with
  | inl e =>
    by_cases he : e = s(a,b)
    · simp [edgeMap,he,Sym2.eq_iff]
      tauto
    · simp only [edgeMap,if_neg he,Sum.inl.injEq]
      have hm : e.map (Sum.inl : V → V ⊕ W) = s(Sum.inl x,Sum.inl y) ↔ e = s(x,y) := by
        rw [← Sym2.map_pair_eq]
        exact (Sym2.map.injective Sum.inl_injective).eq_iff
      rw [hm]
      constructor
      · intro h
        exact ⟨h,h ▸ he⟩
      · exact And.left
  | inr e =>
    induction e using Sym2.ind with | h u v =>
    by_cases he : s(u,v) = s(c,d) <;> simp [edgeMap,he,Sym2.map_pair_eq,Sym2.eq_iff]

lemma edgeMap_eq_right (a b : V) (c d x y : W) (e : Sym2 V ⊕ Sym2 W) :
    edgeMap a b c d e = s(Sum.inr x,Sum.inr y) ↔ e = .inr s(x,y) ∧ s(x,y) ≠ s(c,d) := by
  cases e with
  | inl e =>
    induction e using Sym2.ind with | h u v =>
    by_cases he : s(u,v) = s(a,b) <;> simp [edgeMap,he,Sym2.map_pair_eq,Sym2.eq_iff]
  | inr e =>
    by_cases he : e = s(c,d)
    · simp [edgeMap,he,Sym2.eq_iff]
      tauto
    · simp only [edgeMap,if_neg he,Sum.inr.injEq]
      have hm : e.map (Sum.inr : W → V ⊕ W) = s(Sum.inr x,Sum.inr y) ↔ e = s(x,y) := by
        rw [← Sym2.map_pair_eq]
        exact (Sym2.map.injective Sum.inr_injective).eq_iff
      rw [hm]
      constructor
      · intro h
        exact ⟨h,h ▸ he⟩
      · exact And.left

lemma edgeMap_eq_cross (a b x : V) (c d y : W) (e : Sym2 V ⊕ Sym2 W) :
    edgeMap a b c d e = s(Sum.inl x,Sum.inr y) ↔
      (e = .inl s(a,b) ∧ x = a ∧ y = c) ∨ (e = .inr s(c,d) ∧ x = b ∧ y = d) := by
  cases e with
  | inl e =>
    by_cases he : e = s(a,b)
    · subst e
      simp [edgeMap,Sym2.eq_iff,eq_comm]
    · simp only [edgeMap,if_neg he,Sum.inl.injEq,he,false_and,Sum.inl_ne_inr,false_or,iff_false]
      induction e using Sym2.ind with | h u v =>
      simp [Sym2.map_pair_eq]
  | inr e =>
    by_cases he : e = s(c,d)
    · subst e
      simp [edgeMap,Sym2.eq_iff,eq_comm]
    · simp only [edgeMap,if_neg he,Sum.inr.injEq,he,false_and,Sum.inr_ne_inl,false_or,iff_false]
      induction e using Sym2.ind with | h u v =>
      simp [Sym2.map_pair_eq]

lemma edgeMap_injective {a b : V} {c d : W} (hab : a ≠ b) :
    Function.Injective (edgeMap a b c d) := by
  intro e f hef
  cases f with
  | inl f =>
    by_cases hf : f = s(a,b)
    · subst f
      have hx : edgeMap a b c d e = s(Sum.inl a,Sum.inr c) := by simpa [edgeMap] using hef
      rcases (edgeMap_eq_cross a b a c d c e).mp hx with h | h
      · exact h.1
      · exact (hab h.2.1).elim
    · induction f using Sym2.ind with | h x y =>
      have hx : edgeMap a b c d e = s(Sum.inl x,Sum.inl y) := by
        simpa only [edgeMap,if_neg hf,Sym2.map_pair_eq] using hef
      exact ((edgeMap_eq_left a b x y c d e).mp hx).1
  | inr f =>
    by_cases hf : f = s(c,d)
    · subst f
      have hx : edgeMap a b c d e = s(Sum.inl b,Sum.inr d) := by simpa [edgeMap] using hef
      rcases (edgeMap_eq_cross a b b c d d e).mp hx with h | h
      · exact (hab h.2.1.symm).elim
      · exact h.1
    · induction f using Sym2.ind with | h x y =>
      have hx : edgeMap a b c d e = s(Sum.inr x,Sum.inr y) := by
        simpa only [edgeMap,if_neg hf,Sym2.map_pair_eq] using hef
      exact ((edgeMap_eq_right a b c d x y e).mp hx).1

def edgeEmbedding {a b : V} {c d : W} (hab : a ≠ b) :
    Sym2 V ⊕ Sym2 W ↪ Sym2 (V ⊕ W) := ⟨edgeMap a b c d,edgeMap_injective hab⟩

private lemma exists_mem_eq_and {α : Type*} (S : Finset α) (a : α) (P : Prop) :
    (∃ z, z ∈ S ∧ z = a ∧ P) ↔ a ∈ S ∧ P := by
  constructor
  · rintro ⟨z,hz,rfl,hP⟩
    exact ⟨hz,hP⟩
  · rintro ⟨ha,hP⟩
    exact ⟨a,ha,rfl,hP⟩

lemma edgeFinset_switch (G : SimpleGraph V) (H : SimpleGraph W) {a b : V} {c d : W}
    (hab : a ≠ b) :
    (switch G H a b c d).edgeFinset =
      (G.edgeFinset.disjSum H.edgeFinset).map (edgeEmbedding (c := c) (d := d) hab) := by
  ext e
  induction e using Sym2.ind with | h x y =>
  simp only [SimpleGraph.mem_edgeFinset,Finset.mem_map]
  change (switch G H a b c d).Adj x y ↔
    ∃ z, z ∈ G.edgeFinset.disjSum H.edgeFinset ∧ edgeMap a b c d z = s(x,y)
  cases x with
  | inl x =>
    cases y with
    | inl y =>
      simp only [edgeMap_eq_left,exists_mem_eq_and,Finset.inl_mem_disjSum,SimpleGraph.mem_edgeFinset]
      rfl
    | inr y =>
      simp only [edgeMap_eq_cross,and_or_left,exists_or,exists_mem_eq_and,
        Finset.inl_mem_disjSum,Finset.inr_mem_disjSum,SimpleGraph.mem_edgeFinset]
      change ((x = a ∧ y = c ∧ G.Adj a b) ∨ (x = b ∧ y = d ∧ H.Adj c d)) ↔ _
      tauto
  | inr x =>
    cases y with
    | inl y =>
      rw [show s(Sum.inr x,Sum.inl y) = s(Sum.inl y,Sum.inr x) from Sym2.eq_swap]
      simp only [edgeMap_eq_cross,and_or_left,exists_or,exists_mem_eq_and,
        Finset.inl_mem_disjSum,Finset.inr_mem_disjSum,SimpleGraph.mem_edgeFinset]
      change ((y = a ∧ x = c ∧ G.Adj a b) ∨ (y = b ∧ x = d ∧ H.Adj c d)) ↔ _
      tauto
    | inr y =>
      simp only [edgeMap_eq_right,exists_mem_eq_and,Finset.inr_mem_disjSum,SimpleGraph.mem_edgeFinset]
      rfl

#print axioms edgeMap_injective
#print axioms edgeFinset_switch
end Erdos184Work.GraphSerial
