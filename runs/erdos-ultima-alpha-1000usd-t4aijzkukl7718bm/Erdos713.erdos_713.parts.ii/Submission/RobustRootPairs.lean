import FormalConjecturesUtil
import Submission.DenseSplitWitnesses
import Submission.SplitEdgePacking

/-! Uniformly few exceptional root pairs, and robust split witnesses
outside that set in an exact host with a backward extremal gap. -/
open SimpleGraph Finset Filter Asymptotics
namespace Erdos713RobustRootPairs
open Erdos713DenseSplitWitnesses Erdos713UniformOverlap
open Erdos713SplitEdgePacking Erdos713RobustMergeWitnesses
variable {V W : Type*}
set_option maxHeartbeats 2000000

open scoped Classical in
noncomputable def badRoots [Fintype V] (G : SimpleGraph V) (t : ℝ) : Finset (V × V) :=
  (univ : Finset V).diag ∪ adjPairs G ∪ highOverlap G t

lemma outside_badRoots [Fintype V] (G : SimpleGraph V) (t : ℝ) {u v : V}
    (hp : (u,v) ∉ badRoots G t) :
    u ≠ v ∧ ¬ G.Adj u v ∧ (Nat.card (G.commonNeighbors u v) : ℝ) ≤ t := by
  classical
  simpa only [badRoots,mem_union,mem_diag,mem_univ,true_and,adjPairs,highOverlap,
    mem_filter,not_or,not_lt,Prod.fst,Prod.snd,and_assoc] using hp

lemma badRoots_bound [Fintype V] (G : SimpleGraph V) (t : ℝ) :
    (badRoots G t).card ≤ Fintype.card V+2*Nat.card G.edgeSet+(highOverlap G t).card := by
  classical
  have h1 := card_union_le ((univ : Finset V).diag ∪ adjPairs G) (highOverlap G t)
  have h2 := card_union_le (univ : Finset V).diag (adjPairs G)
  rw [diag_card,card_univ,adjPairs_card] at h2
  change ((univ : Finset V).diag ∪ adjPairs G ∪ highOverlap G t).card ≤ _
  omega

/-- The exceptional set is small uniformly over ALL H-free hosts; exact
extremality is only needed later to supply witnesses outside it. -/
theorem eventually_few_badRoots (H : SimpleGraph W) {α c a ε : ℝ}
    (ha : 1 < α) (ha2 : α < 2) (hc : 0 < c) (ha0 : 0 < a)
    (h : (fun n : ℕ => (extremalNumber n H : ℝ)) ~[atTop]
      (fun n => c*(n : ℝ)^α)) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      Fintype.card V = n → H.Free G →
      (badRoots G (a*(n : ℝ)^(α-1))).card ≤ ε*(n : ℝ)^2 := by
  classical
  have hUpper : ∀ᶠ n : ℕ in atTop, (extremalNumber n H : ℝ) ≤ (ε/6)*(n : ℝ)^2 := by
    filter_upwards [(Erdos713FutureRecords.higher_ratio_zero ha2 h).eventually_lt_const
      (show 0 < ε/6 by positivity),eventually_gt_atTop (0 : ℕ)] with n hn hnp
    have hnR : (0 : ℝ) < n := by exact_mod_cast hnp
    rw [Real.rpow_two] at hn
    exact ((div_lt_iff₀ (sq_pos_of_pos hnR)).mp hn).le
  have hLarge : ∀ᶠ n : ℕ in atTop, 3 ≤ ε*(n : ℝ) :=
    (tendsto_natCast_atTop_atTop.const_mul_atTop hε).eventually_ge_atTop _
  filter_upwards [few_high_overlaps H ha ha2 hc ha0 h (by positivity : 0 < ε/3),
    hUpper,hLarge] with n hHigh hU hL
  intro V instV G hcard hf
  have hhigh := hHigh V G hcard hf
  have hbound := badRoots_bound G (a*(n : ℝ)^(α-1))
  have hBR : ((badRoots G (a*(n : ℝ)^(α-1))).card : ℝ) ≤
      (n : ℝ)+2*(Nat.card G.edgeSet : ℝ)+(highOverlap G (a*(n : ℝ)^(α-1))).card := by
    exact_mod_cast (by simpa only [hcard] using hbound)
  have hEdge : (Nat.card G.edgeSet : ℝ) ≤ (ε/6)*(n : ℝ)^2 := by
    have hh : Nat.card G.edgeSet ≤ extremalNumber n H := by
      simpa only [hcard,edgeFinset_card,Nat.card_eq_fintype_card] using card_edgeFinset_le_extremalNumber hf
    exact (show (Nat.card G.edgeSet : ℝ) ≤ (extremalNumber n H : ℝ) by exact_mod_cast hh).trans hU
  have hnBound := mul_le_mul_of_nonneg_right hL (Nat.cast_nonneg (α := ℝ) n)
  nlinarith only [hBR,hEdge,hhigh,hnBound]

/-- The deleted set may consist of arbitrary unordered vertex pairs, not
only edges; its cardinality still bounds the actual edge loss. -/
def RobustRoots (H : SimpleGraph W) (G : SimpleGraph V) (u v : V) (r : ℝ) : Prop :=
  ∀ T : Finset (Sym2 V), (T.card : ℝ) ≤ r →
    Nonempty (Witness H (G.deleteEdges (T : Set (Sym2 V))) u v)

lemma robust_outside [Fintype V] (H : SimpleGraph W) (G : SimpleGraph V)
    (hf : H.Free G) (he : Nat.card G.edgeSet = extremalNumber (Fintype.card V) H)
    {r t : ℝ}
    (hgap : r+t < (extremalNumber (Fintype.card V) H : ℝ)-
      (extremalNumber (Fintype.card V-1) H : ℝ))
    {u v : V} (hp : (u,v) ∉ badRoots G t) : RobustRoots H G u v r := by
  obtain ⟨hne,hn,hcom⟩ := outside_badRoots G t hp
  intro T hT
  obtain ⟨w,S,f,hu,hv,hL,hR⟩ := split_after_deleting H G hf he hne hn T
    ((add_le_add hT hcom).trans_lt hgap)
  exact ⟨⟨w,S,f,hu,hv,hL,hR⟩⟩

lemma floor_cost_le {r : ℝ} (hr : 0 ≤ r) {C : ℕ} (hC : 0 < C) :
    (⌊r/(C : ℝ)⌋₊ * C : ℕ) ≤ r := by
  have hc : (0 : ℝ) < C := by exact_mod_cast hC
  have hh := (le_div_iff₀ hc).mp (Nat.floor_le (div_nonneg hr hc.le))
  exact_mod_cast hh

lemma packing_outside [Fintype V] [Fintype W] (H : SimpleGraph W) (G : SimpleGraph V)
    (hf : H.Free G) (he : Nat.card G.edgeSet = extremalNumber (Fintype.card V) H)
    (hEdge : ∃ x y, H.Adj x y) {r t : ℝ} (hr : 0 ≤ r)
    (hgap : r+t < (extremalNumber (Fintype.card V) H : ℝ)-
      (extremalNumber (Fintype.card V-1) H : ℝ))
    {u v : V} (hp : (u,v) ∉ badRoots G t) :
    EdgePacking H G u v ⌊r/((Fintype.card W+1).choose 2 : ℝ)⌋₊ := by
  obtain ⟨hne,hn,hcom⟩ := outside_badRoots G t hp
  have hq : 2 ≤ Fintype.card W := by
    obtain ⟨x,y,hxy⟩ := hEdge
    exact Fintype.one_lt_card_iff.mpr ⟨x,y,hxy.ne⟩
  have hC : 0 < (Fintype.card W+1).choose 2 := Nat.choose_pos (by omega)
  apply packing_of_backward_gap H G hf he hne hn
  exact (add_le_add (floor_cost_le hr hC) hcom).trans_lt hgap

#print axioms eventually_few_badRoots
#print axioms robust_outside
#print axioms packing_outside
end Erdos713RobustRootPairs
