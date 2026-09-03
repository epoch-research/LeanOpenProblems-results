import Submission.Work
import Submission.FinitePortLabels

/-! Oriented boundary edges and finite endpoint capacities. -/
namespace Erdos583BoundaryPortsDevelopment
open SimpleGraph Erdos583Work Erdos583Work.BridgeGlue
open scoped Classical
set_option maxHeartbeats 1800000
variable {V : Type*} (G : SimpleGraph V) (S : Set V)

abbrev Boundary := {p : S × (Sᶜ : Set V) // G.Adj p.1.val p.2.val}
def inner (b : Boundary G S) : V := b.val.1.val
def outer (b : Boundary G S) : V := b.val.2.val
def edge (b : Boundary G S) : Sym2 V := s(inner G S b,outer G S b)

lemma inner_mem (b : Boundary G S) : inner G S b ∈ S := b.val.1.property
lemma outer_not_mem (b : Boundary G S) : outer G S b ∉ S := b.val.2.property
lemma adj (b : Boundary G S) : G.Adj (inner G S b) (outer G S b) := b.property

lemma edge_injective : Function.Injective (edge G S) := by
  intro b c he
  rcases Sym2.eq_iff.mp he with h|h
  · apply Subtype.ext
    exact Prod.ext (Subtype.ext h.1) (Subtype.ext h.2)
  · exact (outer_not_mem G S c (h.1 ▸ inner_mem G S b)).elim

lemma edge_not_inside (b : Boundary G S) : edge G S b ∉ (within G S).edgeSet := by
  intro he
  exact outer_not_mem G S b he.2.2

lemma edge_not_outside (b : Boundary G S) : edge G S b ∉ (within G Sᶜ).edgeSet := by
  intro he
  exact he.2.1 (inner_mem G S b)

lemma inside_disjoint_outside : Disjoint (within G S).edgeSet (within G Sᶜ).edgeSet := by
  apply Set.disjoint_left.mpr
  intro e he hf
  induction e using Sym2.ind with
  | h x y => exact hf.2.1 he.2.1

lemma cover : (within G S).edgeSet ∪ (Set.range (edge G S) ∪ (within G Sᶜ).edgeSet)=G.edgeSet := by
  apply Set.Subset.antisymm
  · intro e he
    rcases he with he|⟨b,rfl⟩|he
    · exact edgeSet_mono (within_le G S) he
    · exact adj G S b
    · exact edgeSet_mono (within_le G Sᶜ) he
  · intro e he
    induction e using Sym2.ind with
    | h x y =>
      by_cases hx : x ∈ S <;> by_cases hy : y ∈ S
      · exact Or.inl ⟨he,hx,hy⟩
      · exact Or.inr (Or.inl ⟨⟨(⟨x,hx⟩,⟨y,hy⟩),he⟩,rfl⟩)
      · exact Or.inr (Or.inl ⟨⟨(⟨y,hy⟩,⟨x,hx⟩),he.symm⟩,Sym2.eq_swap⟩)
      · exact Or.inr (Or.inr ⟨he,hx,hy⟩)

lemma fiber_card [Fintype V] (v : V) (hv : v ∈ S) :
    Fintype.card {b : Boundary G S // inner G S b=v}=(G.neighborSet v ∩ Sᶜ).ncard := by
  let e : {b : Boundary G S // inner G S b=v} ≃ (G.neighborSet v ∩ Sᶜ : Set V) :=
    { toFun := fun b ↦ ⟨outer G S b.val,by
        refine ⟨?_,outer_not_mem G S b.val⟩
        exact Eq.mp (congrArg (fun x : V ↦ G.Adj x (outer G S b.val)) b.property) (adj G S b.val)⟩
      invFun := fun y ↦ ⟨⟨(⟨v,hv⟩,⟨y.val,y.property.2⟩),y.property.1⟩,rfl⟩
      left_inv := by
        intro b
        apply Subtype.ext
        apply Subtype.ext
        exact Prod.ext (Subtype.ext b.property.symm) rfl
      right_inv := by intro y; rfl }
  rw [←Nat.card_eq_fintype_card,Nat.card_congr e,Nat.card_coe_set_eq]

lemma split_degree [Fintype V] (v : V) :
    (G.neighborSet v ∩ S).ncard+(G.neighborSet v ∩ Sᶜ).ncard=Nat.card (G.neighborSet v) := by
  rw [←Set.ncard_union_eq]
  · rw [←Set.inter_union_distrib_left,Set.union_compl_self,Set.inter_univ,Nat.card_coe_set_eq]
  · exact Set.disjoint_left.mpr (fun x hx hy ↦ hy.2 hx.2)

lemma assign [Fintype V] {I : Type*} [Fintype I] (start : I → V)
    (hcap : ∀ v ∈ S, Nat.card (G.neighborSet v) ≤
      (G.neighborSet v ∩ S).ncard+Fintype.card {i : I // start i=v}) :
    ∃ slot : Boundary G S ↪ I, ∀ b, start (slot b)=inner G S b := by
  apply Erdos583FinitePortLabelsDevelopment.assign_slots
  intro v
  by_cases hv : v ∈ S
  · rw [fiber_card G S v hv]
    have hh := split_degree G S v
    have hb := hcap v hv
    omega
  · have hn : IsEmpty {b : Boundary G S // inner G S b=v} := by
      refine ⟨fun b ↦ hv ?_⟩
      exact b.property ▸ inner_mem G S b.val
    letI := hn
    simp

end Erdos583BoundaryPortsDevelopment
