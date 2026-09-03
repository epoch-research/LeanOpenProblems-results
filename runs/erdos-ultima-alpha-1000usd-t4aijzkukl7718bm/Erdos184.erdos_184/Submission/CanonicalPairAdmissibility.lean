import Submission.CanonicalThreeReduction
import Submission.MaximumTriplePatterns

/-! Numerical triple-contact restrictions retained in canonical pair coding. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.CanonicalThreeReduction
open Erdos184Serial Critical EvenCore Rigidity MaximumCycles MaximumCoreFamilies CycleSegments
open PairJunctionCoding JunctionPairCoding PairSlotMarkers CanonicalPairLayout CanonicalPairKernel
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
variable {l : ℕ}

def Numeric (b : PairIndex l → Fin 3) : Prop :=
  ∀ i j k (hij : i < j) (hjk : j < k),
    AdmissibleTriple (b ⟨(i,j),hij⟩).val (b ⟨(i,k),hij.trans hjk⟩).val (b ⟨(j,k),hjk⟩).val

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

lemma maximum_triple_of_core {D : Finset G.Subgraph} (hD : IsMaximum G D) (hcard : 3 < D.card)
    (he : ∀ x, Even (G.degree x)) (hm : EvenMinimal G) (hn : number G = 3) (hr : ¬ CycleRigid G)
    (T : Fin 3 → G.Subgraph) (hT : Function.Injective T) (hmem : ∀ i, T i ∈ D) :
    AdmissibleTriple ((T 0).verts ∩ (T 1).verts).ncard
      ((T 0).verts ∩ (T 2).verts).ncard ((T 1).verts ∩ (T 2).verts).ncard := by
  apply maximum_triple_admissible hD (degree_le_four_of_nonrigid_three he hm hn hr) T hT hmem
  have hsub : ({T 0,T 1,T 2} : Finset G.Subgraph) ⊆ D := by
    intro H hH
    simp only [Finset.mem_insert,Finset.mem_singleton] at hH
    rcases hH with rfl | rfl | rfl <;> exact hmem _
  have hc : ({T 0,T 1,T 2} : Finset G.Subgraph).card = 3 := by
    simp [hT.ne (by decide : (0 : Fin 3) ≠ 1),hT.ne (by decide : (0 : Fin 3) ≠ 2),
      hT.ne (by decide : (1 : Fin 3) ≠ 2)]
  have hp : ({T 0,T 1,T 2} : Finset G.Subgraph) ⊂ D :=
    Finset.ssubset_iff_subset_ne.mpr ⟨hsub,by intro hh; have := congrArg Finset.card hh; omega⟩
  have hsmall := proper_subfamily_number_lt hD.1 hD.2.1 hm _ hp
  omega

lemma counts_numeric (B : Fin l → Set V)
    (htwo : ∀ w : Junction B, Nat.card {i : Fin l // w.val ∈ B i} = 2)
    (hbound : ∀ i j : Fin l, i ≠ j → (B i ∩ B j).ncard ≤ 2)
    {D : Finset G.Subgraph} (hD : IsMaximum G D) (hcard : 3 < D.card)
    (he : ∀ x, Even (G.degree x)) (hm : EvenMinimal G) (hn : number G = 3) (hr : ¬ CycleRigid G)
    (H : Fin l → G.Subgraph) (hH : Function.Injective H) (hmem : ∀ i, H i ∈ D)
    (hB : ∀ i, B i = (H i).verts) : Numeric (counts B htwo hbound) := by
  intro i j k hij hjk
  let T : Fin 3 → G.Subgraph := ![H i,H j,H k]
  have hT : Function.Injective T := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp only [T,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_fin_one] at hab ⊢
    all_goals first | rfl | exact (hH.ne hij.ne hab).elim |
      exact (hH.ne (hij.trans hjk).ne hab).elim | exact (hH.ne hjk.ne hab).elim |
      exact (hH.ne hij.ne hab.symm).elim | exact (hH.ne (hij.trans hjk).ne hab.symm).elim |
      exact (hH.ne hjk.ne hab.symm).elim
  have hmemT (a : Fin 3) : T a ∈ D := by fin_cases a <;> exact hmem _
  have ht := maximum_triple_of_core hD hcard he hm hn hr T hT hmemT
  simp only [counts_val,hB]
  exact ht

#print axioms counts_numeric
end Erdos184Work.CanonicalThreeReduction
