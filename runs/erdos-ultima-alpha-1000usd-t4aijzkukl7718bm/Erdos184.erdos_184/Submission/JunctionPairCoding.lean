import Submission.PairJunctionCoding

/-! Applying pair-slot coding to the actual junctions of a finite set family. -/
open scoped Classical
namespace Erdos184Work.JunctionPairCoding
open CycleSegments PairJunctionCoding
set_option maxHeartbeats 1500000
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] {l : ℕ} (B : Fin l → Set V)

noncomputable def incidence (w : Junction B) : Finset (Fin l) :=
  Finset.univ.filter fun i => w.val ∈ B i

lemma mem_incidence (w : Junction B) (i : Fin l) : i ∈ incidence B w ↔ w.val ∈ B i := by
  simp [incidence]

lemma incidence_card (w : Junction B) : (incidence B w).card =
    Fintype.card {i : Fin l // w.val ∈ B i} := by
  simp [incidence,Fintype.card_subtype]

noncomputable def pairContactEquiv (p : PairIndex l) :
    {w : Junction B // p.val.1 ∈ incidence B w ∧ p.val.2 ∈ incidence B w} ≃
      {x : V // x ∈ B p.val.1 ∩ B p.val.2} where
  toFun w := ⟨w.val.val,(mem_incidence B _ _).mp w.property.1,
    (mem_incidence B _ _).mp w.property.2⟩
  invFun x := ⟨⟨x.val,⟨p.val.1,p.val.2,ne_of_lt p.property,x.property.1,x.property.2⟩⟩,
    (mem_incidence B _ _).mpr x.property.1,(mem_incidence B _ _).mpr x.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

variable (htwo : ∀ w : Junction B, Nat.card {i : Fin l // w.val ∈ B i} = 2)

include htwo

lemma incidence_two (w : Junction B) : (incidence B w).card = 2 := by
  rw [incidence_card]
  simpa only [Nat.card_eq_fintype_card] using htwo w

lemma multiplicity_pair (p : PairIndex l) :
    multiplicity (incidence B) (incidence_two B htwo) p = (B p.val.1 ∩ B p.val.2).ncard := by
  rw [multiplicity_eq]
  have h := Fintype.card_congr (pairContactEquiv B p)
  simpa only [← Nat.card_eq_fintype_card,Nat.card_coe_set_eq] using h

variable (hbound : ∀ i j : Fin l, i ≠ j → (B i ∩ B j).ncard ≤ 2)

include hbound

lemma multiplicity_le (p : PairIndex l) :
    multiplicity (incidence B) (incidence_two B htwo) p ≤ 2 := by
  rw [multiplicity_pair B htwo]
  exact hbound _ _ (ne_of_lt p.property)

noncomputable def counts (p : PairIndex l) : Fin 3 :=
  ⟨multiplicity (incidence B) (incidence_two B htwo) p,by have := multiplicity_le B htwo hbound p; omega⟩

lemma counts_val (p : PairIndex l) : (counts B htwo hbound p).val =
    (B p.val.1 ∩ B p.val.2).ncard := multiplicity_pair B htwo p

noncomputable def codeVertex : Junction B ↪ Fin ((l*l)*2) :=
  coding (incidence B) (incidence_two B htwo) (multiplicity_le B htwo hbound)

lemma codeVertex_incidence (w : Junction B) (i : Fin l) : w.val ∈ B i ↔
    i = (decodedPair (codeVertex B htwo hbound w)).1 ∨
    i = (decodedPair (codeVertex B htwo hbound w)).2 := by
  rw [← mem_incidence]
  exact coding_incidence (incidence B) (incidence_two B htwo) (multiplicity_le B htwo hbound) w i

lemma slot_range (p : PairIndex l) (r : Fin 2) :
    slot (p,r) ∈ Set.range (codeVertex B htwo hbound) ↔ r.val < (counts B htwo hbound p).val :=
  slot_mem_range (incidence B) (incidence_two B htwo) (multiplicity_le B htwo hbound) p r

#print axioms counts_val
#print axioms codeVertex_incidence
end Erdos184Work.JunctionPairCoding
