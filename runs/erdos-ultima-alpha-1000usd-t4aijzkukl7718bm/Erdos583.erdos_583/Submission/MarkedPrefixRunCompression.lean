import Submission.MarkedPrivateTail
import Submission.TailPrefixRunFreshness
import Submission.TwoRunCompression

/-! Compression of complete prefix excursions followed by a private final
suffix. Marking is obtained only under a strict half-order bound. -/
namespace Erdos583MarkedPrefixRunCompressionDevelopment
open SimpleGraph Erdos583Work Erdos583Work.BridgeGlue
open Erdos583CycleRunIntervalsDevelopment Erdos583PrivatePathExpansionDevelopment
open Erdos583RunCompressionDataDevelopment Erdos583TwoRunCompressionDevelopment
open Erdos583MarkedPrivateTailDevelopment Erdos583TailPrefixRunFreshnessDevelopment
open scoped Classical
set_option maxHeartbeats 3000000
set_option Elab.async false
variable {V : Type*} [Fintype V] {G : SimpleGraph V} {a w b : V}

lemma prefix_run_partition_of_marked
    (W : G.Walk a w) (Q : G.Walk w b) (hp : (W.append Q).IsPath)
    (S : Set V) (hw : w ∉ S) (hb : b ∈ S)
    (hQ : ∀ z ∈ Q.support, z ≠ w → z ∈ S)
    (H : SimpleGraph V) (hH : H.support ⊆ Sᶜ)
    (hf : ∀ p ∈ runs W S, ¬H.Adj (runStart W p) (runFinish W p))
    (D : Finset (H ⊔ chords (runs W S) (runStart W) (runFinish W)).Subgraph)
    (hD : GoodDecomposition _ D) (hm : MarkedDouble.MarkedAt D w) :
    ∃ E : Finset ((H ⊔ arcs (runs W S) (runPath W)) ⊔ Q.toSubgraph.spanningCoe).Subgraph,
      GoodDecomposition _ E ∧ E.card ≤ D.card := by
  let X := chords (runs W S) (runStart W) (runFinish W)
  let B := Q.toSubgraph.spanningCoe
  have hJ : (H ⊔ X).support ⊆ Sᶜ := by
    rintro z ⟨v,hz|hz⟩
    · exact hH ⟨v,hz⟩
    · exact run_chords_outside W S ⟨v,hz⟩
  have hwb : w ≠ b := fun he ↦ hw (he ▸ hb)
  obtain ⟨E,hE,hEc⟩ := extend_marked_private_tail (H ⊔ X) Q hp.of_append_right hwb
    (fun z hz hzw hzJ ↦ hJ hzJ (hQ z hz hzw)) D hD hm
  have hHB : (H ⊔ B).support ⊆ (W.toSubgraph.verts ∩ S)ᶜ := by
    rintro z ⟨v,hz|hz⟩ hzS
    · exact hH ⟨v,hz⟩ hzS.2
    · have hzQ := Walk.mem_support_of_adj_toSubgraph hz
      have he := path_append_support_inter W Q hp (W.mem_verts_toSubgraph.mp hzS.1) hzQ
      exact hw (he ▸ hzS.2)
  have hfHB (p : RunIndex W) (hpr : p ∈ runs W S) :
      ¬(H ⊔ B).Adj (runStart W p) (runFinish W p) := by
    rintro (hh|hh)
    · exact hf p hpr hh
    · exact prefix_run_shortcut_not_tail W Q hp S p hpr (by
        rw [Walk.edges_append]
        exact List.mem_append_right _ (Q.mem_edges_toSubgraph.mp hh))
  have he : (H ⊔ X) ⊔ B=(H ⊔ B) ⊔ X := by ac_rfl
  obtain ⟨E',hE',hE'c⟩ := partition_transport he ⟨E,hE,hEc⟩
  obtain ⟨F,hF,hFc⟩ := (path_run_conditions W hp.of_append_left S).expand W S
    (H ⊔ B) hHB hfHB E' hE'
  apply partition_transport (show (H ⊔ B) ⊔ arcs (runs W S) (runPath W)=
    (H ⊔ arcs (runs W S) (runPath W)) ⊔ B by ac_rfl)
  refine ⟨F,hF,?_⟩
  exact hFc.trans hE'c

lemma marked_prefix_run_partition {n : ℕ} (hsmall : VertexCritical.SmallerOrders n)
    (W : G.Walk a w) (Q : G.Walk w b) (hp : (W.append Q).IsPath)
    (S : Set V) (hw : w ∉ S) (hb : b ∈ S)
    (hQ : ∀ z ∈ Q.support, z ≠ w → z ∈ S)
    (H : SimpleGraph V) (hH : H.support ⊆ Sᶜ)
    (hf : ∀ p ∈ runs W S, ¬H.Adj (runStart W p) (runFinish W p))
    (hc : SupportConnected (H ⊔ chords (runs W S) (runStart W) (runFinish W)))
    (hwJ : w ∈ (H ⊔ chords (runs W S) (runStart W) (runFinish W)).support)
    (hsize : 2*Sᶜ.ncard < n) :
    ∃ D : Finset ((H ⊔ arcs (runs W S) (runPath W)) ⊔ Q.toSubgraph.spanningCoe).Subgraph,
      GoodDecomposition _ D ∧ D.card ≤ ⌈(Sᶜ.ncard : ℚ)/2⌉₊ := by
  have hJ : (H ⊔ chords (runs W S) (runStart W) (runFinish W)).support ⊆ Sᶜ := by
    rintro z ⟨v,hz|hz⟩
    · exact hH ⟨v,hz⟩
    · exact run_chords_outside W S ⟨v,hz⟩
  have hJcard := Set.ncard_le_ncard hJ
  obtain ⟨D,hD,hDc,hm⟩ := marked_on_support_of_twice_lt hsmall _ hc w hwJ (by omega)
  obtain ⟨E,hE,hEc⟩ := prefix_run_partition_of_marked W Q hp S hw hb hQ H hH hf D hD hm
  refine ⟨E,hE,?_⟩
  rw [ceil_half] at hDc ⊢
  omega

end Erdos583MarkedPrefixRunCompressionDevelopment
