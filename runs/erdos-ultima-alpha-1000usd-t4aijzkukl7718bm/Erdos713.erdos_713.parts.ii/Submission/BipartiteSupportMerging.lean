import FormalConjecturesUtil
import Submission.SplitRootParity
import Submission.SupportMergeObstructions

/-! Exact supported hosts for a nonseparable bipartite pattern cannot be
assumed bipartite. Opposite-color mergers expose that distinction. -/
open SimpleGraph Finset
namespace Erdos713BipartiteSupportMerging
open Erdos713SplitRootParity Erdos713SupportMergeObstructions
open Erdos713VertexMerging Erdos713ExactCloneSaturation Erdos713CloneSymm
variable {V W : Type*}
set_option maxHeartbeats 2000000

lemma complete_at_support [Fintype V] {H : SimpleGraph W} (hH : H.IsBipartite)
    (hRest : ∀ w, (H.induce {w}ᶜ).Preconnected) {G : SimpleGraph V}
    (χ : G.Coloring (Fin 2)) (hf : H.Free G)
    (he : Nat.card G.edgeSet = extremalNumber (Fintype.card V) H) {ε : ℝ}
    (hrec : QuadSupport (fun n => extremalNumber n H) ε (Fintype.card V))
    (hSlope : 0 < ε*(2*(Fintype.card V : ℝ)-1)) :
    ∀ u v, χ u ≠ χ v → G.Adj u v := by
  intro u v hχ
  by_contra hn
  have huv : u ≠ v := fun hh => hχ (congrArg χ hh)
  have hsafe := free_merge_opposite hH hRest χ hf hχ hn
  have hs := record_safe_merge H G he hrec huv hn hsafe
  letI := commonNeighbors_empty_of_opposite χ hχ
  simp only [Nat.card_of_isEmpty,Nat.cast_zero] at hs
  exact (not_le_of_gt hSlope) hs

lemma small_degree_of_complete_coloring [Fintype V] [Nonempty V] [Fintype W]
    {H : SimpleGraph W} (hH : H.IsBipartite) {G : SimpleGraph V}
    (χ : G.Coloring (Fin 2)) (hf : H.Free G)
    (hComplete : ∀ u v, χ u ≠ χ v → G.Adj u v) :
    ∃ v : V, Nat.card (G.neighborSet v) ≤ Fintype.card W := by
  classical
  by_contra hh
  push_neg at hh
  obtain ⟨v⟩ := (inferInstance : Nonempty V)
  have hvpos : 0 < G.degree v := by
    simpa only [Nat.card_eq_fintype_card,card_neighborSet_eq_degree] using
      (lt_of_le_of_lt (Nat.zero_le (Fintype.card W)) (hh v))
  obtain ⟨w,hw⟩ := (G.degree_pos_iff_exists_adj v).mp hvpos
  let S := G.neighborFinset v
  have hTw : ∀ u ∈ S, G.neighborSet u = G.neighborSet w := by
    intro u hu
    have hu' : G.Adj v u := by simpa only [S,mem_neighborFinset] using hu
    have hcolor : χ u = χ w := two_ne_same _ _ _ (χ.valid hu').symm (χ.valid hw).symm
    ext z
    change G.Adj u z ↔ G.Adj w z
    constructor
    · intro huz
      exact hComplete w z (hcolor ▸ χ.valid huz)
    · intro hwz
      exact hComplete u z (hcolor.symm ▸ χ.valid hwz)
  have hS : Fintype.card W ≤ S.card := by
    simpa only [S,card_neighborFinset_eq_degree,Nat.card_eq_fintype_card,card_neighborSet_eq_degree]
      using (hh v).le
  rcases twins_card_or_degree hH hf S hTw with hsmall | hsmall
  · omega
  · have := hh w
    omega

/-- This prevents identifying the exact support witness with a bipartite
almost-regular restriction used in separate extremal estimates. -/
theorem no_bipartite_large_support [Fintype W] {H : SimpleGraph W}
    (hH : H.IsBipartite) (hRest : ∀ w, (H.induce {w}ᶜ).Preconnected)
    {n : ℕ} (hn : 0 < n) (G : SimpleGraph (Fin n)) (hf : H.Free G)
    (he : Nat.card G.edgeSet = extremalNumber n H) {ε : ℝ}
    (hrec : QuadSupport (fun n => extremalNumber n H) ε n)
    (hSlope : (Fintype.card W : ℝ) < ε*(2*(n : ℝ)-1)) : ¬ G.IsBipartite := by
  rintro ⟨χ⟩
  haveI : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  have hpos : 0 < ε*(2*(n : ℝ)-1) := (Nat.cast_nonneg _).trans_lt hSlope
  have hComplete := complete_at_support hH hRest χ hf
    (by simpa only [Fintype.card_fin] using he)
    (by simpa only [Fintype.card_fin] using hrec)
    (by simpa only [Fintype.card_fin] using hpos)
  obtain ⟨v,hv⟩ := small_degree_of_complete_coloring hH χ hf hComplete
  have hdeg := record_degree H hn G hf he hrec v
  have hvR : (Nat.card (G.neighborSet v) : ℝ) ≤ Fintype.card W := by exact_mod_cast hv
  linarith

#print axioms complete_at_support
#print axioms no_bipartite_large_support
end Erdos713BipartiteSupportMerging
