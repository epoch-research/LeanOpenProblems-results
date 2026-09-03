import Submission.SquarePieces
import Submission.MinimalBridgeRestoration

/-! A quantitative square-family estimate allowing an optimality defect.
The discarded-subgraph cost is explicit and is not bounded uniformly here. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.SquareDiscardBudget
open Critical Rigidity SquarePieces Subfamilies
set_option maxHeartbeats 1400000
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

lemma square_union_number_le (A : Finset G.Subgraph)
    (hA : ∀ H ∈ A, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hp : Set.PairwiseDisjoint (A : Set G.Subgraph) (fun H => H.edgeSet)) :
    number (subfamilyGraph A) ≤ A.card := by
  have hc := (subfamilyGraph_edges A).symm
  have hn := number_le (lowerFamily A hc)
    (lowerFamily_property IsCycleOrEdge A hc (by
      intro H hH
      apply Or.inl
      simpa only [SimpleGraph.IsRegularOfDegree,
        ← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] using hA H hH))
    (lowerFamily_decomposition A hc hp)
  simpa only [lowerFamily_card] using hn

/-- The family need not be minimum; its defect is paid explicitly. -/
lemma squares_le_order_add_defect (A : Finset G.Subgraph)
    (hA : ∀ H ∈ A, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hp : Set.PairwiseDisjoint (A : Set G.Subgraph) (fun H => H.edgeSet))
    (hsq : ∀ H ∈ A, H.coe.edgeFinset.card = 4) :
    A.card ≤ 9 * Fintype.card V + 5 * (A.card - number (subfamilyGraph A)) := by
  have he := cycle_subfamily_even A hA hp
  have hb := five_mul_number_le_edges_add_nine_card (G := subfamilyGraph A) (by
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] using he)
  have hc : (subfamilyGraph A).edgeFinset.card = 4 * A.card := by
    rw [subfamilyGraph_card_edges A hp]
    calc
      _ = ∑ _H ∈ A, 4 := Finset.sum_congr rfl hsq
      _ = _ := by simp [Nat.mul_comm]
  have hn := square_union_number_le A hA hp
  rw [hc] at hb
  omega

/-- Subadditivity for an edge-disjoint spanning union. -/
lemma number_union_le (S T : SimpleGraph V) (hd : Disjoint S.edgeSet T.edgeSet) :
    number (S ⊔ T) ≤ number S + number T := by
  have he : (S ⊔ T) \ S = T := by
    ext x y
    change ((S.Adj x y ∨ T.Adj x y) ∧ ¬ S.Adj x y) ↔ T.Adj x y
    have hh : ¬ (S.Adj x y ∧ T.Adj x y) := by
      rintro ⟨hS,hT⟩
      exact Set.disjoint_left.mp hd (show s(x,y) ∈ S.edgeSet from hS) hT
    tauto
  have hn := number_sdiff_add_le (S ⊔ T) S le_sup_left
  rw [he] at hn
  omega

/-- Abstract endpoint of a square-deletion/core-extraction chain. The
identity on `number G` encodes the unit decrements; the term `number J`
accounts for the discarded even graph and cannot be silently omitted. -/
lemma square_discard_bound (A : Finset G.Subgraph) (J R : SimpleGraph V)
    (hA : ∀ H ∈ A, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hp : Set.PairwiseDisjoint (A : Set G.Subgraph) (fun H => H.edgeSet))
    (hsq : ∀ H ∈ A, H.coe.edgeFinset.card = 4)
    (hSJ : Disjoint (subfamilyGraph A).edgeSet J.edgeSet)
    (hSR : Disjoint (subfamilyGraph A ⊔ J).edgeSet R.edgeSet)
    (hcover : (subfamilyGraph A ⊔ J) ⊔ R = G)
    (hcount : number G = A.card + number R) :
    A.card ≤ 9 * Fintype.card V + 5 * number J := by
  have h₁ := number_union_le (subfamilyGraph A) J hSJ
  have h₂ := number_union_le (subfamilyGraph A ⊔ J) R hSR
  rw [hcover] at h₂
  have hdef : A.card - number (subfamilyGraph A) ≤ number J := by omega
  have hb := squares_le_order_add_defect A hA hp hsq
  omega

lemma total_discard_bound (A : Finset G.Subgraph) (J R : SimpleGraph V)
    (hA : ∀ H ∈ A, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hp : Set.PairwiseDisjoint (A : Set G.Subgraph) (fun H => H.edgeSet))
    (hsq : ∀ H ∈ A, H.coe.edgeFinset.card = 4)
    (hSJ : Disjoint (subfamilyGraph A).edgeSet J.edgeSet)
    (hSR : Disjoint (subfamilyGraph A ⊔ J).edgeSet R.edgeSet)
    (hcover : (subfamilyGraph A ⊔ J) ⊔ R = G)
    (hcount : number G = A.card + number R)
    (hR : number R ≤ 6 * Fintype.card V) :
    number G ≤ 15 * Fintype.card V + 5 * number J := by
  have h := square_discard_bound A J R hA hp hsq hSJ hSR hcover hcount
  omega

end Erdos184Work.SquareDiscardBudget
#print axioms Erdos184Work.SquareDiscardBudget.squares_le_order_add_defect
#print axioms Erdos184Work.SquareDiscardBudget.square_discard_bound
#print axioms Erdos184Work.SquareDiscardBudget.total_discard_bound
