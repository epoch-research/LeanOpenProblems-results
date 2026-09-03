import Submission.FractionalEnvelope

/-! The two fractional envelope values associated with a marked edge.
No integral comparison or two-edge-sum theorem is assumed or proved here. -/
open SimpleGraph
open scoped Classical
namespace Erdos184.RootedEnvelopeProfiles
open FractionalEnvelope
variable {V : Type*} [Fintype V]

/-- Maximum fractional optimum over even subgraphs using the marked edge,
with a zero default when that family is empty. -/
noncomputable def through (G : SimpleGraph V) (e : Sym2 V) : ℝ :=
  (CycleEnvelope.evenSubgraphs G).sup' (evenSubgraphs_nonempty G)
    (fun H => if e ∈ H.edgeSet then optimum H else 0)

lemma through_nonneg (G : SimpleGraph V) (e : Sym2 V) : 0 ≤ through G e := by
  have hb : (⊥ : SimpleGraph V) ∈ CycleEnvelope.evenSubgraphs G :=
    CycleEnvelope.mem_evenSubgraphs.mpr ⟨bot_le, by
      intro v
      simp only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      simp⟩
  have hh := Finset.le_sup' (fun H : SimpleGraph V => if e ∈ H.edgeSet then optimum H else 0) hb
  simpa [through] using hh

lemma optimum_le_through {G H : SimpleGraph V} {e : Sym2 V}
    (hle : H ≤ G) (he : ∀ v, Even (H.degree v)) (hm : e ∈ H.edgeSet) :
    optimum H ≤ through G e := by
  have hh := Finset.le_sup' (fun A : SimpleGraph V => if e ∈ A.edgeSet then optimum A else 0)
    (CycleEnvelope.mem_evenSubgraphs.mpr ⟨hle,he⟩)
  simpa only [if_pos hm] using hh

lemma through_le_envelope (G : SimpleGraph V) (e : Sym2 V) : through G e ≤ envelope G := by
  apply Finset.sup'_le
  intro H hH
  obtain ⟨hle,he⟩ := CycleEnvelope.mem_evenSubgraphs.mp hH
  split_ifs
  · exact optimum_le_envelope hle he
  · exact envelope_nonneg G

/-- The unrooted envelope is the maximum of the avoiding and using profiles. -/
lemma envelope_eq_max (G : SimpleGraph V) (e : Sym2 V) :
    envelope G = max (envelope (G.deleteEdges {e})) (through G e) := by
  apply le_antisymm
  · apply envelope_le
    intro H hHG heH
    by_cases hm : e ∈ H.edgeSet
    · exact (optimum_le_through hHG heH hm).trans (le_max_right _ _)
    · have hle : H ≤ G.deleteEdges {e} := by
        apply edgeSet_subset_edgeSet.mp
        rw [edgeSet_deleteEdges]
        intro f hf
        refine ⟨edgeSet_mono hHG hf, ?_⟩
        intro hfe
        exact hm ((Set.mem_singleton_iff.mp hfe) ▸ hf)
      exact (optimum_le_envelope hle heH).trans (le_max_left _ _)
  · exact max_le (envelope_mono (G.deleteEdges_le {e})) (through_le_envelope G e)

lemma through_le_avoiding_add_one (G : SimpleGraph V) (e : Sym2 V) :
    through G e ≤ envelope (G.deleteEdges {e}) + 1 :=
  (through_le_envelope G e).trans (delete_edge_lipschitz G e)

/-- An arithmetic sufficient condition for a factor-two estimate for a
repeated-block profile. The hypotheses do not assert that arbitrary graph
profiles satisfy the rooted comparison. -/
lemma repeated_profile_bound (k b c r : ℝ) (hr : 0 ≤ r)
    (hroot : k ≤ b + c) :
    r * (k - 1) + 1 ≤ 2 * max (r * b) (r * (c - 1) + 1) := by
  have hh := mul_le_mul_of_nonneg_left hroot hr
  have h₀ := le_max_left (r*b) (r*(c-1)+1)
  have h₁ := le_max_right (r*b) (r*(c-1)+1)
  nlinarith

/-- Unrooted and edge-deleted factor-two estimates alone do not entail the
repeated-profile estimate by arithmetic. This is a numerical profile, NOT
an example of a graph realizing it. -/
lemma unrooted_conditions_arithmetically_insufficient :
    let k : ℝ := 4
    let b : ℝ := 3/2
    let c : ℝ := 2
    k ≤ 2 * max b c ∧ k-1 ≤ 2*b ∧ c ≤ b+1 ∧
      2 * max (2*b) (2*(c-1)+1) < 2*(k-1)+1 := by
  norm_num

end Erdos184.RootedEnvelopeProfiles
