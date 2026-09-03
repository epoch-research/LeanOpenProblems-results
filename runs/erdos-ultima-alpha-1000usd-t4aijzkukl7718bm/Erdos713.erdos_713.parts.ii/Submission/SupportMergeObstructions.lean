import FormalConjecturesUtil
import Submission.VertexMerging
import Submission.QuadraticSupportCenters

/-! A quadratic support obstructs every identification losing fewer edges
than its backward support slope. -/
open SimpleGraph Finset Filter Asymptotics
namespace Erdos713SupportMergeObstructions
open Erdos713VertexMerging Erdos713ExactCloneSaturation Erdos713QuadraticSupports
open Erdos713QuadraticSupportTangents Erdos713QuadraticSupportCenters Erdos713CloneSymm
variable {V W : Type*}
set_option maxHeartbeats 2000000

lemma record_safe_merge [Fintype V] (H : SimpleGraph W) (G : SimpleGraph V)
    (he : Nat.card G.edgeSet = extremalNumber (Fintype.card V) H) {ε : ℝ}
    (hrec : QuadSupport (fun n => extremalNumber n H) ε (Fintype.card V))
    {u v : V} (huv : u ≠ v) (hn : ¬ G.Adj u v) (hsafe : H.Free (merge G u v hn)) :
    ε*(2*(Fintype.card V : ℝ)-1) ≤ (Nat.card (G.commonNeighbors u v) : ℝ) := by
  classical
  have hc : Fintype.card {x : V // x ≠ v} = Fintype.card V-1 := by
    rw [Fintype.card_subtype_compl]
    simp
  have hbound : Nat.card (merge G u v hn).edgeSet ≤ extremalNumber (Fintype.card V-1) H := by
    have hh := card_edgeFinset_le_extremalNumber hsafe
    rw [hc] at hh
    simpa only [edgeFinset_card,Nat.card_eq_fintype_card] using hh
  have hedge := merge_edge_count G huv hn
  have hNat : extremalNumber (Fintype.card V) H ≤
      extremalNumber (Fintype.card V-1) H + Nat.card (G.commonNeighbors u v) := by omega
  have hReal : (extremalNumber (Fintype.card V) H : ℝ) ≤
      (extremalNumber (Fintype.card V-1) H : ℝ)+(Nat.card (G.commonNeighbors u v) : ℝ) := by
    exact_mod_cast hNat
  have hcard : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨v⟩
  have hh := hrec (Fintype.card V-1)
  have hnm : ((Fintype.card V-1 : ℕ) : ℝ) = (Fintype.card V : ℝ)-1 := by
    rw [Nat.cast_sub (by omega)]; norm_num
  rw [hnm] at hh
  nlinarith only [hReal,hh]

lemma merge_contains_of_small_overlap [Fintype V] (H : SimpleGraph W) (G : SimpleGraph V)
    (he : Nat.card G.edgeSet = extremalNumber (Fintype.card V) H) {ε : ℝ}
    (hrec : QuadSupport (fun n => extremalNumber n H) ε (Fintype.card V))
    {u v : V} (huv : u ≠ v) (hn : ¬ G.Adj u v)
    (hsmall : (Nat.card (G.commonNeighbors u v) : ℝ) < ε*(2*(Fintype.card V : ℝ)-1)) :
    H ⊑ merge G u v hn := by
  by_contra hh
  exact (not_le_of_gt hsmall) (record_safe_merge H G he hrec huv hn hh)

/-- Uniformly at every sufficiently large support order, the small-overlap
threshold may have any fixed coefficient below c*alpha. -/
theorem eventually_support_mergers (H : SimpleGraph W) {α c a : ℝ}
    (h : (fun n : ℕ => (extremalNumber n H : ℝ)) ~[atTop]
      (fun n => c*(n : ℝ)^α)) (hac : a < c*α) :
    ∀ᶠ n : ℕ in atTop, ∀ (G : SimpleGraph (Fin n)),
      Nat.card G.edgeSet = extremalNumber n H → ∀ ε : ℝ,
      QuadSupport (fun n => extremalNumber n H) ε n →
      ∀ u v : Fin n, u ≠ v → ∀ hn : ¬ G.Adj u v,
      (Nat.card (G.commonNeighbors u v) : ℝ) ≤ a*(n : ℝ)^(α-1) →
      H ⊑ merge G u v hn := by
  filter_upwards [eventually_support_lower h hac] with n hs
  intro G he ε hrec u v huv hn hsmall
  apply merge_contains_of_small_overlap H G (by simpa only [Fintype.card_fin] using he)
    (by simpa only [Fintype.card_fin] using hrec) huv hn
  simpa only [Fintype.card_fin] using hsmall.trans_lt (hs ε hrec)

/-- Such exact hosts occur in every fixed relative window of sufficiently
large orders. No identification is claimed to preserve forbiddenness. -/
theorem nearby_merge_obstructed (H : SimpleGraph W) (hEdge : ∃ x y, H.Adj x y)
    {α c a δ : ℝ} (ha : 1 < α) (ha2 : α < 2) (hc : 0 < c) (hac : a < c*α)
    (hd : 0 < δ)
    (h : (fun n : ℕ => (extremalNumber n H : ℝ)) ~[atTop]
      (fun n => c*(n : ℝ)^α)) (N D : ℕ) :
    ∀ᶠ k : ℕ in atTop, ∃ (n : ℕ) (G : SimpleGraph (Fin n)),
      N ≤ n ∧ (1-δ)*(k : ℝ) < n ∧ (n : ℝ) < (1+δ)*k ∧
      H.Free G ∧ Nat.card G.edgeSet = extremalNumber n H ∧
      (∀ v, D ≤ Nat.card (G.neighborSet v)) ∧
      (∀ v, a*(n : ℝ)^(α-1) ≤ (Nat.card (G.neighborSet v) : ℝ)) ∧
      ∀ u v : Fin n, u ≠ v → ∀ hn : ¬ G.Adj u v,
        (Nat.card (G.commonNeighbors u v) : ℝ) ≤ a*(n : ℝ)^(α-1) →
        H ⊑ merge G u v hn := by
  obtain ⟨M,hM⟩ := eventually_atTop.mp
    ((eventually_support_mergers H h hac).and (eventually_support_lower h hac))
  filter_upwards [nearby_supports ha ha2 hc h (max N M) D hd (by norm_num : (0 : ℝ) < 1)] with k hk
  obtain ⟨n,ε,hnNM,hn,hε,_,hrec,hD,hnlo,hnhi⟩ := hk
  obtain ⟨hMerge,hSlope⟩ := hM n ((le_max_right N M).trans hnNM)
  obtain ⟨G,hopt,he⟩ := exists_ordinary_optimal H hEdge n
  refine ⟨n,G,(le_max_left N M).trans hnNM,hnlo,hnhi,hopt.free,he,?_,?_,
    hMerge G he ε hrec⟩
  · intro v
    exact_mod_cast hD.trans (record_degree H hn G hopt.free he hrec v)
  · intro v
    exact (hSlope ε hrec).le.trans (record_degree H hn G hopt.free he hrec v)

#print axioms record_safe_merge
#print axioms eventually_support_mergers
#print axioms nearby_merge_obstructed
end Erdos713SupportMergeObstructions
