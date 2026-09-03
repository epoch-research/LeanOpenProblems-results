import Submission.FourSubfamilyPatterns

/-! A row has at most two doubled contacts. Consequently any selected family
of k cycles in the hypothetical core has at most k+1 junction markers per row. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.AllowedFourCounts
set_option maxHeartbeats 3000000
variable {I : Type*} [Fintype I] [DecidableEq I] (a : I → I → ℕ)

def doubled (i : I) : Finset I := Finset.univ.filter (fun j => j ≠ i ∧ a i j = 2)

lemma doubled_card_le_two
    (hfour : ∀ T : Fin 4 → I, Function.Injective T → Pattern a T) (i : I) :
    (doubled a i).card ≤ 2 := by
  by_contra hn
  obtain ⟨j,k,l,hj,hk,hl,hjk,hjl,hkl⟩ := Finset.two_lt_card_iff.mp (show 2 < (doubled a i).card by omega)
  have hj' := (Finset.mem_filter.mp hj).2
  have hk' := (Finset.mem_filter.mp hk).2
  have hl' := (Finset.mem_filter.mp hl).2
  let T : Fin 4 → I := ![i,j,k,l]
  have hT : Function.Injective T := by
    intro u v huv
    fin_cases u <;> fin_cases v <;>
      simp_all [T,Matrix.cons_val_zero',Matrix.cons_val_succ']
  apply no_three_doubles a (hfour T hT)
  exact ⟨hj'.2,hk'.2,hl'.2⟩

#print axioms doubled_card_le_two
end Erdos184Work.AllowedFourCounts

namespace Erdos184Work.CycleSegments
set_option maxHeartbeats 3000000
variable {V K : Type*} [Fintype V] [Fintype K]

lemma localJunction_card_le_sum (B : K → Set V) (i : K) :
    Fintype.card (LocalJunction B i) ≤
      ∑ j ∈ Finset.univ.erase i, (B i ∩ B j).ncard := by
  rw [localJunction_card,Set.ncard_eq_toFinset_card']
  have he : {x | x ∈ B i ∧ ∃ j, j ≠ i ∧ x ∈ B j}.toFinset =
      (Finset.univ.erase i).biUnion (fun j => (B i ∩ B j).toFinset) := by
    ext x
    simp only [Set.mem_toFinset,Set.mem_setOf_eq,Finset.mem_biUnion,Finset.mem_erase,
      Finset.mem_univ,and_true,Set.mem_inter_iff]
    aesop
  rw [he]
  have hh := Finset.card_biUnion_le (s := Finset.univ.erase i) (t := fun j => (B i ∩ B j).toFinset)
  simpa only [Set.ncard_eq_toFinset_card'] using hh

lemma localJunction_card_le_of_few_doubles (B : K → Set V)
    (hpair : ∀ i j, i ≠ j → (B i ∩ B j).ncard ≤ 2)
    (hdouble : ∀ i, (AllowedFourCounts.doubled (fun i j => (B i ∩ B j).ncard) i).card ≤ 2)
    (i : K) : Fintype.card (LocalJunction B i) ≤ Fintype.card K + 1 := by
  let S : Finset K := Finset.univ.erase i
  let a : K → K → ℕ := fun i j => (B i ∩ B j).ncard
  have hf : S.filter (fun j => a i j = 2) = AllowedFourCounts.doubled a i := by
    ext j
    simp [S,AllowedFourCounts.doubled]
  have hn : 0 < Fintype.card K := Fintype.card_pos_iff.mpr ⟨i⟩
  calc
    Fintype.card (LocalJunction B i) ≤ ∑ j ∈ S, a i j := localJunction_card_le_sum B i
    _ ≤ ∑ j ∈ S, (1 + if a i j = 2 then 1 else 0) := by
      apply Finset.sum_le_sum
      intro j hj
      have hjne : i ≠ j := (Finset.mem_erase.mp hj).1.symm
      have hb := hpair i j hjne
      change a i j ≤ 2 at hb
      split_ifs <;> omega
    _ = S.card + (S.filter (fun j => a i j = 2)).card := by simp [Finset.sum_add_distrib]
    _ ≤ Fintype.card K + 1 := by
      rw [hf]
      have hd := hdouble i
      have hc : S.card = Fintype.card K - 1 := by simp [S]
      change (AllowedFourCounts.doubled a i).card ≤ 2 at hd
      omega

#print axioms localJunction_card_le_of_few_doubles
end Erdos184Work.CycleSegments

namespace Erdos184Work.FourSubfamilyPatterns
open Critical MaximumCycles MaximumCoreFamilies CycleSegments
set_option maxHeartbeats 3000000
variable {V K : Type*} [Fintype V] [Fintype K] {G : SimpleGraph V}

lemma core_selected_contacts_bound {D : Finset G.Subgraph} (hD : IsMaximum G D)
    (he : ∀ v, Even (G.degree v)) (hm : EvenCore.EvenMinimal G)
    (hn : number G = 3) (hr : ¬ Rigidity.CycleRigid G)
    (H : K → D) (hH : Function.Injective H) (i : K) :
    Fintype.card (LocalJunction (fun j => (H j).val.verts) i) ≤ Fintype.card K + 1 := by
  apply localJunction_card_le_of_few_doubles
  · intro i j hij
    exact maximum_decomposition_intersection_le_two D hD.1 hD.2.1 hD.2.2 _ _
      (H i).property (H j).property (fun hh => hij (hH (Subtype.ext hh)))
  · intro i
    apply AllowedFourCounts.doubled_card_le_two
    intro T hT
    exact core_pattern hD he hm hn hr (H ∘ T) (hH.comp hT)

#print axioms core_selected_contacts_bound
end Erdos184Work.FourSubfamilyPatterns
