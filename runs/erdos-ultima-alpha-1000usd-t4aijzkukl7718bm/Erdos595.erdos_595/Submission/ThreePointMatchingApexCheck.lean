import Submission.OneEdgeLocalDefinitions
import Submission.BipartiteNeighborhoodApexCover

/-! The complete second right adjoint is K4-free for independent apices whose
neighborhoods have at most three vertices and induce matchings. The one-edge
plus isolated point family is included. This does not establish non-coverability. -/
set_option autoImplicit false
open Set SimpleGraph
namespace Erdos595ThreePointMatchingApex
open Erdos595ArcAdjoint Erdos595BipartiteNeighborhoodApex
variable {V E : Type*} (B : SimpleGraph V) (N : E → Set V)

/-- Empty neighborhoods and fewer than three distinct points are allowed. -/
def ThreePoints : Prop := ∀ e, ∃ a b c : V, N e ⊆ {a,b,c}

def NeighborhoodMatching : Prop :=
  ∀ e a b c, a ∈ N e → b ∈ N e → c ∈ N e → B.Adj a b → B.Adj a c → b = c

private lemma four_of_three {a b c d u v w : V}
    (ha : a ∈ ({u,v,w} : Set V)) (hb : b ∈ ({u,v,w} : Set V))
    (hc : c ∈ ({u,v,w} : Set V)) (hd : d ∈ ({u,v,w} : Set V)) :
    a = b ∨ a = c ∨ a = d ∨ b = c ∨ b = d ∨ c = d := by
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at ha hb hc hd
  rcases ha with rfl | rfl | rfl <;>
    rcases hb with rfl | rfl | rfl <;>
    rcases hc with rfl | rfl | rfl <;>
    rcases hd with rfl | rfl | rfl <;> simp_all

variable (hB : B.CliqueFree 3) (h3 : ThreePoints N) (hM : NeighborhoodMatching B N)

include hB h3 hM in
theorem local_conditions : Erdos595OneEdgeLocal.LocalConditions (graph B N)
    (fun x => mark x = true) := by
  classical
  constructor
  · intro a b ha hb hab
    cases a <;> cases b <;> simp_all [mark,graph]
  · intro a b c hab hac hbc
    cases a <;> cases b <;> cases c <;> simp_all [mark,graph]
    exact (hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨hab,hac,hbc⟩)).elim
  · intro a ha b c d e hab hac had hae
    cases a with
    | inl a => cases ha
    | inr a =>
      cases b with
      | inr b => exact hab.elim
      | inl b =>
        cases c with
        | inr c => exact hac.elim
        | inl c =>
          cases d with
          | inr d => exact had.elim
          | inl d =>
            cases e with
            | inr e => exact hae.elim
            | inl e =>
              obtain ⟨u,v,w,hN⟩ := h3 a
              have h := four_of_three (hN hab) (hN hac) (hN had) (hN hae)
              simpa only [Sum.inl.injEq] using h
  · intro a ha b c d hab hac had hbc hbd
    cases a with
    | inl a => cases ha
    | inr a =>
      cases b with
      | inr b => exact hab.elim
      | inl b =>
        cases c with
        | inr c => exact hac.elim
        | inl c =>
          cases d with
          | inr d => exact had.elim
          | inl d => exact congrArg Sum.inl (hM a b c d hab hac had hbc hbd)

/-- One old edge with an isolated third point is a special case.
The displayed edge itself is allowed to be absent, and the three parameters
need not be distinct. -/
theorem matching_of_one_edge (l r d : E → V)
    (hN : ∀ e, N e ⊆ {l e,r e,d e})
    (hdl : ∀ e, ¬B.Adj (d e) (l e)) (hdr : ∀ e, ¬B.Adj (d e) (r e)) :
    NeighborhoodMatching B N := by
  intro e a b c ha hb hc hab hac
  have ha' := hN e ha
  have hb' := hN e hb
  have hc' := hN e hc
  have hld : ¬B.Adj (l e) (d e) := fun hh => hdl e hh.symm
  have hrd : ¬B.Adj (r e) (d e) := fun hh => hdr e hh.symm
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at ha' hb' hc'
  rcases ha' with rfl | rfl | rfl <;>
    rcases hb' with rfl | rfl | rfl <;>
    rcases hc' with rfl | rfl | rfl <;>
    first | rfl | exact (hab.ne rfl).elim | exact (hac.ne rfl).elim |
      exact (hdl e hab).elim | exact (hdl e hac).elim |
      exact (hdr e hab).elim | exact (hdr e hac).elim |
      exact (hld hab).elim | exact (hld hac).elim |
      exact (hrd hab).elim | exact (hrd hac).elim

#print axioms local_conditions
end Erdos595ThreePointMatchingApex
