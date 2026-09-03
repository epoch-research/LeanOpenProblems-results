import FormalConjecturesUtil
import Submission.SplitEdgePacking

/-! A demand-list version of edge packing. Root pairs may differ or repeat.
All requested split copies have pairwise disjoint EDGE sets. -/
open SimpleGraph Finset
open scoped Classical
namespace Erdos713SplitEdgePacking
variable {V W : Type*}
set_option maxHeartbeats 2000000

def SimultaneousPacking [Fintype W] (H : SimpleGraph W) (G : SimpleGraph V)
    {k : ℕ} (p : Fin k → V × V) : Prop :=
  ∃ f : (i : Fin k) → Witness H G (p i).1 (p i).2,
    ∀ i j, i ≠ j → Disjoint (f i).edges (f j).edges

lemma simultaneous_of_avoidance [Fintype W] (H : SimpleGraph W) (G : SimpleGraph V)
    (k : ℕ) (p : Fin k → V × V)
    (h : ∀ i : Fin k, ∀ T : Finset (Sym2 V), T.card ≤ k*(Fintype.card W+1).choose 2 →
      ∃ f : Witness H G (p i).1 (p i).2, Disjoint f.edges T) :
    SimultaneousPacking H G p := by
  induction k with
  | zero => exact ⟨fun i => Fin.elim0 i,fun i => Fin.elim0 i⟩
  | succ k ih =>
    obtain ⟨f,hf⟩ := ih (fun i => p i.succ) (fun i T hT => h i.succ T
      (hT.trans (Nat.mul_le_mul_right _ (Nat.le_succ k))))
    let T := univ.biUnion (fun i : Fin k => (f i).edges)
    have hT : T.card ≤ k*(Fintype.card W+1).choose 2 := by
      calc
        _ ≤ ∑ i : Fin k, (f i).edges.card := card_biUnion_le
        _ ≤ ∑ _i : Fin k, (Fintype.card W+1).choose 2 :=
          sum_le_sum (fun i _ => (f i).edge_card_le)
        _ = _ := by simp
    obtain ⟨g,hg⟩ := h 0 T (hT.trans (Nat.mul_le_mul_right _ (Nat.le_succ k)))
    have hgf (i : Fin k) : Disjoint g.edges (f i).edges :=
      hg.mono_right (by intro e he; exact mem_biUnion.mpr ⟨i,mem_univ _,he⟩)
    refine ⟨Fin.cases g f,?_⟩
    intro i j hij
    cases i using Fin.cases <;> cases j using Fin.cases
    · exact (hij rfl).elim
    · exact hgf _
    · exact (hgf _).symm
    · exact hf _ _ (fun he => hij (congrArg Fin.succ he))

lemma simultaneous_of_backward_gap [Fintype V] [Fintype W]
    (H : SimpleGraph W) (G : SimpleGraph V) (hf : H.Free G)
    (he : Nat.card G.edgeSet = extremalNumber (Fintype.card V) H)
    (k : ℕ) (p : Fin k → V × V)
    (hp : ∀ i, (p i).1 ≠ (p i).2 ∧ ¬ G.Adj (p i).1 (p i).2)
    (hsmall : ∀ i, (k*(Fintype.card W+1).choose 2 : ℕ)+
      (Nat.card (G.commonNeighbors (p i).1 (p i).2) : ℝ) <
      (extremalNumber (Fintype.card V) H : ℝ)-
        (extremalNumber (Fintype.card V-1) H : ℝ)) : SimultaneousPacking H G p := by
  apply simultaneous_of_avoidance H G k p
  intro i T hT
  apply witness_avoiding H G hf he (hp i).1 (hp i).2 T
  have hTR : (T.card : ℝ) ≤ (k*(Fintype.card W+1).choose 2 : ℕ) := by exact_mod_cast hT
  linarith [hsmall i]

#print axioms simultaneous_of_avoidance
#print axioms simultaneous_of_backward_gap
end Erdos713SplitEdgePacking
