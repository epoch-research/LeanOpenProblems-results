import FormalConjecturesUtil
import Submission.SupportMergeObstructions
import Submission.VertexSplitWitnesses
import Submission.UniformOverlap

/-! At selected exact orders, all but o(n^2) ordered root pairs support a
nontrivial vertex split of the forbidden graph. This is not rationality. -/
open SimpleGraph Finset Filter Asymptotics
open scoped Topology
namespace Erdos713DenseSplitWitnesses
open Erdos713VertexMerging Erdos713VertexSplitWitnesses
open Erdos713SupportMergeObstructions Erdos713UniformOverlap
variable {V W : Type*}
set_option maxHeartbeats 2000000

def SplitRoots (H : SimpleGraph W) (G : SimpleGraph V) (u v : V) : Prop :=
  ∃ (w : W) (S : Set W) (f : (Erdos713VertexSplitWitnesses.split H w S).Copy G),
    f (some w) = u ∧ f none = v ∧
    (∃ x, H.Adj w x ∧ x ∈ S) ∧ (∃ y, H.Adj w y ∧ y ∉ S)

open scoped Classical in
noncomputable def missingPairs [Fintype V] (H : SimpleGraph W) (G : SimpleGraph V) : Finset (V × V) :=
  univ.filter (fun p => ¬ SplitRoots H G p.1 p.2)

open scoped Classical in
noncomputable def adjPairs [Fintype V] (G : SimpleGraph V) : Finset (V × V) :=
  univ.filter (fun p => G.Adj p.1 p.2)

lemma adjPairs_card [Fintype V] (G : SimpleGraph V) :
    (adjPairs G).card = 2*Nat.card G.edgeSet := by
  classical
  let e : {p : V × V // G.Adj p.1 p.2} ≃ G.Dart :=
    { toFun := fun p => ⟨p.val,p.property⟩
      invFun := fun p => ⟨p.toProd,p.adj⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hh := Fintype.card_congr e
  simpa only [Fintype.card_subtype,adjPairs,G.dart_card_eq_twice_card_edges,
    edgeFinset_card,Nat.card_eq_fintype_card] using hh

lemma missingPairs_bound [Fintype V] (H : SimpleGraph W) (G : SimpleGraph V)
    (hf : H.Free G) (t : ℝ)
    (hMerge : ∀ u v, u ≠ v → ∀ hn : ¬ G.Adj u v,
      (Nat.card (G.commonNeighbors u v) : ℝ) ≤ t → H ⊑ merge G u v hn) :
    (missingPairs H G).card ≤ Fintype.card V+2*Nat.card G.edgeSet+(highOverlap G t).card := by
  classical
  have hsub : missingPairs H G ⊆ (univ : Finset V).diag ∪ adjPairs G ∪ highOverlap G t := by
    rintro ⟨u,v⟩ hp
    have hno := (mem_filter.mp hp).2
    by_cases huv : u = v
    · apply mem_union_left
      apply mem_union_left
      simp [huv]
    · by_cases hn : G.Adj u v
      · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨mem_univ _,hn⟩))
      · by_cases ht : t < (Nat.card (G.commonNeighbors u v) : ℝ)
        · exact mem_union_right _ (mem_filter.mpr ⟨mem_univ _,ht⟩)
        · exact (hno (split_copy_of_merge hf hn (hMerge u v huv hn (le_of_not_gt ht)))).elim
  have hh := (card_le_card hsub).trans (card_union_le _ _)
  have h2 := card_union_le (univ : Finset V).diag (adjPairs G)
  rw [diag_card,card_univ,adjPairs_card] at h2
  omega

/-- This conclusion concerns every H-free host satisfying the displayed
merger obstruction, without a maximum-degree or exactness assumption. -/
theorem eventually_few_missing_of_mergers (H : SimpleGraph W) {α c a ε : ℝ}
    (ha : 1 < α) (ha2 : α < 2) (hc : 0 < c) (ha0 : 0 < a)
    (h : (fun n : ℕ => (extremalNumber n H : ℝ)) ~[atTop]
      (fun n => c*(n : ℝ)^α)) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      Fintype.card V = n → H.Free G →
      (∀ u v, u ≠ v → ∀ hn : ¬ G.Adj u v,
        (Nat.card (G.commonNeighbors u v) : ℝ) ≤ a*(n : ℝ)^(α-1) → H ⊑ merge G u v hn) →
      (missingPairs H G).card ≤ ε*(n : ℝ)^2 := by
  classical
  have hUpper : ∀ᶠ n : ℕ in atTop, (extremalNumber n H : ℝ) ≤ (ε/6)*(n : ℝ)^2 := by
    filter_upwards [(Erdos713FutureRecords.higher_ratio_zero ha2 h).eventually_lt_const
      (show 0 < ε/6 by positivity),eventually_gt_atTop (0 : ℕ)] with n hn hnp
    have hnR : (0 : ℝ) < n := by exact_mod_cast hnp
    have hpow : (n : ℝ)^(2 : ℝ) = (n : ℝ)^2 := Real.rpow_two _
    rw [hpow] at hn
    exact ((div_lt_iff₀ (sq_pos_of_pos hnR)).mp hn).le
  have hLarge : ∀ᶠ n : ℕ in atTop, 3 ≤ ε*(n : ℝ) :=
    (tendsto_natCast_atTop_atTop.const_mul_atTop hε).eventually_ge_atTop _
  filter_upwards [few_high_overlaps H ha ha2 hc ha0 h (by positivity : 0 < ε/3),
    hUpper,hLarge] with n hHigh hU hL
  intro V instV G hcard hf hMerge
  have hhigh := hHigh V G hcard hf
  have hbound := missingPairs_bound H G hf (a*(n : ℝ)^(α-1)) hMerge
  have hBR : ((missingPairs H G).card : ℝ) ≤
      (n : ℝ)+2*(Nat.card G.edgeSet : ℝ)+(highOverlap G (a*(n : ℝ)^(α-1))).card := by
    exact_mod_cast (by simpa only [hcard] using hbound)
  have hEdge : (Nat.card G.edgeSet : ℝ) ≤ (ε/6)*(n : ℝ)^2 := by
    have hh : Nat.card G.edgeSet ≤ extremalNumber n H := by
      simpa only [hcard,edgeFinset_card,Nat.card_eq_fintype_card] using card_edgeFinset_le_extremalNumber hf
    exact (show (Nat.card G.edgeSet : ℝ) ≤ (extremalNumber n H : ℝ) by exact_mod_cast hh).trans hU
  have hn0 := Nat.cast_nonneg (α := ℝ) n
  have hnBound := mul_le_mul_of_nonneg_right hL hn0
  nlinarith only [hBR,hEdge,hhigh,hnBound]

/-- Exact hosts with sharp minimum degree and split witnesses at almost
all ordered root pairs exist near every sufficiently large order. The
split pattern may depend on the pair. No disjointness is asserted. -/
theorem nearby_dense_split_witnesses (H : SimpleGraph W) (hEdge : ∃ x y, H.Adj x y)
    {α c a δ ε : ℝ} (ha : 1 < α) (ha2 : α < 2) (hc : 0 < c) (hac : a < c*α)
    (hd : 0 < δ) (hε : 0 < ε)
    (h : (fun n : ℕ => (extremalNumber n H : ℝ)) ~[atTop]
      (fun n => c*(n : ℝ)^α)) (N D : ℕ) :
    ∀ᶠ k : ℕ in atTop, ∃ (n : ℕ) (G : SimpleGraph (Fin n)),
      N ≤ n ∧ (1-δ)*(k : ℝ) < n ∧ (n : ℝ) < (1+δ)*k ∧
      H.Free G ∧ Nat.card G.edgeSet = extremalNumber n H ∧
      (∀ v, D ≤ Nat.card (G.neighborSet v)) ∧
      (∀ v, a*(n : ℝ)^(α-1) ≤ (Nat.card (G.neighborSet v) : ℝ)) ∧
      (missingPairs H G).card ≤ ε*(n : ℝ)^2 := by
  let b := max a c
  have hb0 : 0 < b := hc.trans_le (le_max_right _ _)
  have hbc : b < c*α := max_lt hac (by nlinarith)
  obtain ⟨M,hM⟩ := eventually_atTop.mp (eventually_few_missing_of_mergers H ha ha2 hc hb0 h hε)
  filter_upwards [nearby_merge_obstructed H hEdge ha ha2 hc hbc hd h (max N M) D] with k hk
  obtain ⟨n,G,hnNM,hnlo,hnhi,hf,he,hD,hMin,hMerge⟩ := hk
  refine ⟨n,G,(le_max_left N M).trans hnNM,hnlo,hnhi,hf,he,hD,?_,
    hM n ((le_max_right N M).trans hnNM) (Fin n) G (Fintype.card_fin n) hf hMerge⟩
  intro v
  exact (mul_le_mul_of_nonneg_right (le_max_left a c)
    (Real.rpow_nonneg (Nat.cast_nonneg n) _)).trans (hMin v)

#print axioms missingPairs_bound
#print axioms eventually_few_missing_of_mergers
#print axioms nearby_dense_split_witnesses
end Erdos713DenseSplitWitnesses
