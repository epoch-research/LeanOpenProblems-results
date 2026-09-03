import FormalConjecturesUtil
import Submission.RobustMergeWitnesses

/-! Edge-disjoint nontrivial split witnesses rooted at ONE fixed pair.
The interiors need not be vertex-disjoint and the split types may differ. -/
open SimpleGraph Finset
open scoped Classical
namespace Erdos713SplitEdgePacking
open Erdos713VertexSplitWitnesses Erdos713RobustMergeWitnesses
variable {V W : Type*}
set_option maxHeartbeats 2000000

structure Witness (H : SimpleGraph W) (G : SimpleGraph V) (u v : V) where
  root : W
  side : Set W
  copy : (split H root side).Copy G
  left_eq : copy (some root) = u
  right_eq : copy none = v
  left_nonempty : ∃ x, H.Adj root x ∧ x ∈ side
  right_nonempty : ∃ y, H.Adj root y ∧ y ∉ side

noncomputable def Witness.edges [Fintype W] {H : SimpleGraph W} {G : SimpleGraph V}
    {u v : V} (f : Witness H G u v) : Finset (Sym2 V) :=
  (split H f.root f.side).edgeFinset.image (Sym2.map f.copy)

lemma Witness.edge_card_le [Fintype W] {H : SimpleGraph W} {G : SimpleGraph V}
    {u v : V} (f : Witness H G u v) : f.edges.card ≤ (Fintype.card W+1).choose 2 := by
  exact Finset.card_image_le.trans (by
    simpa only [Fintype.card_option] using
      (split H f.root f.side).card_edgeFinset_le_card_choose_two)

lemma witness_avoiding [Fintype V] [Fintype W] (H : SimpleGraph W) (G : SimpleGraph V)
    (hf : H.Free G) (he : Nat.card G.edgeSet = extremalNumber (Fintype.card V) H)
    {u v : V} (huv : u ≠ v) (hn : ¬ G.Adj u v) (T : Finset (Sym2 V))
    (hsmall : (T.card : ℝ)+(Nat.card (G.commonNeighbors u v) : ℝ) <
      (extremalNumber (Fintype.card V) H : ℝ)-
        (extremalNumber (Fintype.card V-1) H : ℝ)) :
    ∃ f : Witness H G u v, Disjoint f.edges T := by
  obtain ⟨w,S,f,hu,hv,hL,hR⟩ := split_after_deleting H G hf he huv hn T hsmall
  let g := (Copy.ofLE _ _ (G.deleteEdges_le (T : Set (Sym2 V)))).comp f
  let F : Witness H G u v := ⟨w,S,g,hu,hv,hL,hR⟩
  refine ⟨F,Finset.disjoint_left.mpr ?_⟩
  intro e he hT
  obtain ⟨e0,he0,rfl⟩ := Finset.mem_image.mp he
  induction e0 using Sym2.ind with | _ x y =>
  have ha := f.toHom.map_adj (mem_edgeFinset.mp he0)
  exact (deleteEdges_adj.mp ha).2 hT

/-- Different witnesses in a packing have disjoint EDGE sets. They still
share the two prescribed roots, and may also share internal vertices. -/
def EdgePacking [Fintype W] (H : SimpleGraph W) (G : SimpleGraph V)
    (u v : V) (k : ℕ) : Prop :=
  ∃ f : Fin k → Witness H G u v, ∀ i j, i ≠ j → Disjoint (f i).edges (f j).edges

lemma packing_of_avoidance [Fintype W] (H : SimpleGraph W) (G : SimpleGraph V)
    (u v : V) (k : ℕ)
    (h : ∀ T : Finset (Sym2 V), T.card ≤ k*(Fintype.card W+1).choose 2 →
      ∃ f : Witness H G u v, Disjoint f.edges T) : EdgePacking H G u v k := by
  induction k with
  | zero => exact ⟨Fin.elim0,fun i => Fin.elim0 i⟩
  | succ k ih =>
    obtain ⟨f,hf⟩ := ih (fun T hT => h T
      (hT.trans (Nat.mul_le_mul_right _ (Nat.le_succ k))))
    let T := univ.biUnion (fun i : Fin k => (f i).edges)
    have hT : T.card ≤ k*(Fintype.card W+1).choose 2 := by
      calc
        _ ≤ ∑ i : Fin k, (f i).edges.card := card_biUnion_le
        _ ≤ ∑ _i : Fin k, (Fintype.card W+1).choose 2 :=
          sum_le_sum (fun i _ => (f i).edge_card_le)
        _ = _ := by simp
    obtain ⟨g,hg⟩ := h T (hT.trans (Nat.mul_le_mul_right _ (Nat.le_succ k)))
    have hgf (i : Fin k) : Disjoint g.edges (f i).edges :=
      hg.mono_right (by intro e he; exact mem_biUnion.mpr ⟨i,mem_univ _,he⟩)
    refine ⟨Fin.cases g f,?_⟩
    intro i j hij
    cases i using Fin.cases <;> cases j using Fin.cases
    · exact (hij rfl).elim
    · exact hgf _
    · exact (hgf _).symm
    · exact hf _ _ (fun he => hij (congrArg Fin.succ he))

/-- A backward gap buys a linear-size EDGE packing for each low-overlap
nonadjacent pair, without a strict rate gap for any split pattern. -/
theorem packing_of_backward_gap [Fintype V] [Fintype W]
    (H : SimpleGraph W) (G : SimpleGraph V) (hf : H.Free G)
    (he : Nat.card G.edgeSet = extremalNumber (Fintype.card V) H)
    {u v : V} (huv : u ≠ v) (hn : ¬ G.Adj u v) (k : ℕ)
    (hsmall : (k*(Fintype.card W+1).choose 2 : ℕ)+(Nat.card (G.commonNeighbors u v) : ℝ) <
      (extremalNumber (Fintype.card V) H : ℝ)-
        (extremalNumber (Fintype.card V-1) H : ℝ)) : EdgePacking H G u v k := by
  apply packing_of_avoidance H G u v k
  intro T hT
  apply witness_avoiding H G hf he huv hn T
  have hTR : (T.card : ℝ) ≤ (k*(Fintype.card W+1).choose 2 : ℕ) := by exact_mod_cast hT
  linarith

#print axioms witness_avoiding
#print axioms packing_of_avoidance
#print axioms packing_of_backward_gap
end Erdos713SplitEdgePacking
