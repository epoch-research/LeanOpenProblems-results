import FormalConjecturesUtil
import Submission.UpToCubicNorm

/-! A lexicographically minimal tight-rate core; every proper contained graph is subdominant. -/

open Filter SimpleGraph Asymptotics

namespace Erdos713Critical
open Erdos713Rate Erdos713Tight
universe u

lemma card_le_of_contained {U W : Type*} [Fintype U] [Fintype W]
    {J : SimpleGraph U} {H : SimpleGraph W} (h : J ⊑ H) : Fintype.card U ≤ Fintype.card W := by
  obtain ⟨f⟩ := h
  exact Fintype.card_le_of_injective f f.injective

lemma edges_le_of_contained {U W : Type*} [Fintype U] [Fintype W]
    {J : SimpleGraph U} {H : SimpleGraph W} (h : J ⊑ H) : Nat.card J.edgeSet ≤ Nat.card H.edgeSet := by
  classical
  obtain ⟨f⟩ := h
  simpa only [Fintype.card_eq_nat_card] using Fintype.card_le_of_embedding f.mapEdgeSet

lemma iso_of_contained_card_eq {U W : Type*} [Fintype U] [Fintype W]
    {J : SimpleGraph U} {H : SimpleGraph W} (h : J ⊑ H)
    (hV : Fintype.card U = Fintype.card W) (hE : Nat.card H.edgeSet ≤ Nat.card J.edgeSet) :
    Nonempty (J ≃g H) := by
  classical
  obtain ⟨f⟩ := h
  let e : U ≃ W := Equiv.ofBijective f ((Fintype.bijective_iff_injective_and_card f).mpr ⟨f.injective,hV⟩)
  have hle : J.map e.toEmbedding ≤ H :=
    (map_le_iff_le_comap e.toEmbedding J H).mpr (fun _ _ h => f.toHom.map_adj h)
  have hcards : H.edgeFinset.card ≤ (J.map e.toEmbedding).edgeFinset.card := by
    rw [← (Iso.map e J).card_edgeFinset_eq]
    simpa only [edgeFinset_card, Fintype.card_eq_nat_card] using hE
  have heq : J.map e.toEmbedding = H :=
    edgeFinset_inj.mp (Finset.eq_of_subset_of_card_le (edgeFinset_mono hle) hcards)
  exact ⟨heq ▸ Iso.map e J⟩

open scoped Classical in
lemma exists_critical_connected_core {W : Type u} [Fintype W] (G : SimpleGraph W)
    {r : ℝ} (hr : 1 < r) (h : HasTightRate G r) :
    ∃ (U : Type u) (_ : Fintype U) (H : SimpleGraph U), H ⊑ G ∧ H.Connected ∧
      (∀ v, 2 ≤ Nat.card (H.neighborSet v)) ∧ HasTightRate H r ∧ Fintype.card U ≤ Fintype.card W ∧
      (∀ (T : Type u) [Fintype T] (J : SimpleGraph T), J ⊑ H → HasTightRate J r →
        Fintype.card U ≤ Fintype.card T) ∧
      (∀ (T : Type u) [Fintype T] (J : SimpleGraph T), J ⊑ H → ¬ Nonempty (J ≃g H) →
        (fun n : ℕ => (extremalNumber n J : ℝ)) =o[atTop] (fun n : ℕ => (n : ℝ)^r)) := by
  classical
  let P : ℕ → Prop := fun n => ∃ (U : Type u) (_ : Fintype U) (H : SimpleGraph U),
    H ⊑ G ∧ HasTightRate H r ∧ Fintype.card U = n
  have hP : ∃ n, P n := ⟨Fintype.card W, W, inferInstance, G, .refl _, h, rfl⟩
  obtain ⟨U₀, inst₀, H₀, hH₀G, hH₀R, hc₀⟩ := Nat.find_spec hP
  let Q : ℕ → Prop := fun m => ∃ (U : Type u) (_ : Fintype U) (H : SimpleGraph U),
    H ⊑ G ∧ HasTightRate H r ∧ Fintype.card U = Nat.find hP ∧ Nat.card H.edgeSet = m
  have hQ : ∃ m, Q m := ⟨Nat.card H₀.edgeSet, U₀, inst₀, H₀, hH₀G, hH₀R, hc₀, rfl⟩
  obtain ⟨U, instU, H, hHG, hHR, hcard, hecard⟩ := Nat.find_spec hQ
  have hMin (T : Type u) [Fintype T] (J : SimpleGraph T) (hJG : J ⊑ G) (hJR : HasTightRate J r) :
      Fintype.card U ≤ Fintype.card T := by
    rw [hcard]
    exact Nat.find_min' hP ⟨T, inferInstance, J, hJG, hJR, rfl⟩
  have hEdgeMin (T : Type u) [Fintype T] (J : SimpleGraph T) (hJH : J ⊑ H) (hJR : HasTightRate J r) :
      Nat.card H.edgeSet ≤ Nat.card J.edgeSet := by
    have hJcard : Fintype.card T = Nat.find hP := by
      exact (le_antisymm (card_le_of_contained hJH) (hMin T J (hJH.trans hHG) hJR)).trans hcard
    rw [hecard]
    exact Nat.find_min' hQ ⟨T, inferInstance, J, hJH.trans hHG, hJR, hJcard, rfl⟩
  have hSmaller (S : Set U) (hS : Nat.card S < Fintype.card U)
      (hR : HasTightRate (H.induce S) r) : False := by
    have hh := hMin S (H.induce S) ((show H.induce S ⊑ H from ⟨Copy.induce H S⟩).trans hHG) hR
    simp only [Fintype.card_eq_nat_card] at hh hS
    omega
  have hDegree : ∀ v, 2 ≤ Nat.card (H.neighborSet v) := by
    intro x
    by_contra hx
    have hx' : H.degree x < 2 := by
      simpa only [Nat.card_eq_fintype_card, card_neighborSet_eq_degree, not_le] using hx
    apply hSmaller {x}ᶜ (by
      simpa only [Fintype.card_eq_nat_card] using
        Fintype.card_subtype_lt (p := fun v => v ∈ ({x}ᶜ : Set U)) (x := x) (by simp))
    have hx01 : H.degree x = 0 ∨ H.degree x = 1 := by omega
    rcases hx01 with hx0 | hx1
    · exact isolated_converse H hx0 hHR
    · obtain ⟨y, hxy, _⟩ := degree_eq_one_iff_existsUnique_adj.mp hx1
      exact leaf_converse H hx1 hxy hr hHR
  letI : Nonempty U := nonempty_of_superlinear_rate hr hHR.toHasRate
  have hConnected : H.Connected := by
    by_contra hC
    let w : U := Classical.arbitrary U
    have hw : ∃ v, ¬H.Reachable w v := by
      by_contra hhh
      push_neg at hhh
      exact hC ((H.connected_iff_exists_forall_reachable).mpr ⟨w, hhh⟩)
    obtain ⟨v, hv⟩ := hw
    let S : Set U := (H.connectedComponentMk w).supp
    have hwS : w ∈ S := rfl
    have hvS : v ∉ S := by
      intro hh
      exact hv (ConnectedComponent.exact hh.symm)
    have hs : Nat.card S < Fintype.card U := by
      simpa only [Fintype.card_eq_nat_card] using Fintype.card_subtype_lt hvS
    have hsc : Nat.card ↥(Sᶜ) < Fintype.card U := by
      simpa only [Fintype.card_eq_nat_card] using
        Fintype.card_subtype_lt (x := w) (by simpa only [Set.mem_compl_iff, not_not] using hwS)
    have hSplit := iso (Erdos713Components.splitIso H S (fun u v huv =>
      ConnectedComponent.mem_supp_congr_adj (H.connectedComponentMk w) huv)) hHR
    rcases sum_or (H.induce S) (H.induce Sᶜ) hr hSplit with hRS | hRSc
    · exact hSmaller S hs hRS
    · exact hSmaller Sᶜ hsc hRSc

  refine ⟨U, instU, H, hHG, hConnected, hDegree, hHR, hMin W G (.refl _) h, ?_, ?_⟩
  · intro T _ J hJH hJR
    exact hMin T J (hJH.trans hHG) hJR
  · intro T _ J hJH hNoIso
    by_contra hNoLittleO
    have hJR : HasTightRate J r := of_upper_notLittleO hHR.one_le
      ((extremal_mono_bigO hJH).trans hHR.upper) hNoLittleO
    exact hNoIso (iso_of_contained_card_eq hJH
      (le_antisymm (card_le_of_contained hJH) (hMin T J (hJH.trans hHG) hJR))
      (hEdgeMin T J hJH hJR))

lemma proper_subgraph_littleO {W : Type u} [Fintype W] (H : SimpleGraph W) {r : ℝ}
    (hCritical : ∀ (T : Type u) [Fintype T] (J : SimpleGraph T), J ⊑ H → ¬ Nonempty (J ≃g H) →
      (fun n : ℕ => (extremalNumber n J : ℝ)) =o[atTop] (fun n : ℕ => (n : ℝ)^r))
    {J : SimpleGraph W} (hJ : J < H) :
    (fun n : ℕ => (extremalNumber n J : ℝ)) =o[atTop] (fun n : ℕ => (n : ℝ)^r) := by
  classical
  apply hCritical W J ⟨Copy.ofLE _ _ hJ.le⟩
  rintro ⟨e⟩
  have hE := e.card_edgeFinset_eq
  exact hJ.ne (edgeFinset_inj.mp (Finset.eq_of_subset_of_card_le (edgeFinset_mono hJ.le) hE.ge))

#print axioms exists_critical_connected_core
#print axioms proper_subgraph_littleO
end Erdos713Critical
