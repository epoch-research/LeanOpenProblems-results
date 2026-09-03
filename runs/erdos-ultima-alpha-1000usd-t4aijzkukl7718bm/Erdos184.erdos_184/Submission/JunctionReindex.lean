import Submission.JunctionCounts

/-! Junctions and local junctions are unchanged by a bijection of colors. -/
open scoped Classical
namespace Erdos184Work.CycleSegments
set_option maxHeartbeats 500000
variable {V K L : Type*} [Fintype V] [Fintype K] [Fintype L]

noncomputable def junctionReindex (B : K → Set V) (e : L ≃ K) :
    Junction (B ∘ e) ≃ Junction B where
  toFun x := ⟨x.val,by
    obtain ⟨i,j,hij,hi,hj⟩ := x.property
    exact ⟨e i,e j,e.injective.ne hij,hi,hj⟩⟩
  invFun x := ⟨x.val,by
    obtain ⟨i,j,hij,hi,hj⟩ := x.property
    refine ⟨e.symm i,e.symm j,e.symm.injective.ne hij,?_,?_⟩
    · simpa using hi
    · simpa using hj⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def localJunctionReindex (B : K → Set V) (e : L ≃ K) (i : L) :
    LocalJunction (B ∘ e) i ≃ LocalJunction B (e i) where
  toFun x := ⟨junctionReindex B e x.val,x.property⟩
  invFun x := ⟨(junctionReindex B e).symm x.val,x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

lemma localJunction_card_reindex (B : K → Set V) (e : L ≃ K) (i : L) :
    Fintype.card (LocalJunction (B ∘ e) i) = Fintype.card (LocalJunction B (e i)) :=
  Fintype.card_congr (localJunctionReindex B e i)

lemma incidence_card_reindex (B : K → Set V) (e : L ≃ K) (x : V) :
    Fintype.card {i : L // x ∈ (B ∘ e) i} = Fintype.card {i : K // x ∈ B i} :=
  Fintype.card_congr (e.subtypeEquiv (fun _ => Iff.rfl))

lemma incidence_natCard_reindex (B : K → Set V) (e : L ≃ K) (x : V) :
    Nat.card {i : L // x ∈ (B ∘ e) i} = Nat.card {i : K // x ∈ B i} :=
  Nat.card_congr (e.subtypeEquiv (fun _ => Iff.rfl))

#print axioms incidence_card_reindex
end Erdos184Work.CycleSegments
