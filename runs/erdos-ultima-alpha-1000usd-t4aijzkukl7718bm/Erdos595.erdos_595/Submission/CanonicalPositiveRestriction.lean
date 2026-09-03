import Submission.EdgeVertexFilterMarginal

/-!
Exact positivity for the canonical countable-cover filter. Unlike positivity
for an arbitrary avoiding filter, a positive edge subgraph for this canonical
filter is precisely a non-coverable subgraph. This supplies no K4-free example
of positivity and does not settle Erdős 595.
-/
set_option autoImplicit false
open Set Filter SimpleGraph
namespace Erdos595CanonicalPositive
open Erdos595Work Erdos595CountableBadEdge

variable {V : Type*} (G : SimpleGraph V)
abbrev Edge := Erdos595ArcAdjoint.Arc G

/-- Symmetrize a subset of the directed edge carrier, retaining the old edges. -/
def span (S : Set (Edge G)) : SimpleGraph V where
  Adj a b := ∃ h : G.Adj a b, (⟨(a,b),h⟩ : Edge G) ∈ S ∨
    (⟨(b,a),h.symm⟩ : Edge G) ∈ S
  symm := by
    rintro a b ⟨h,hs⟩
    exact ⟨h.symm,hs.symm⟩
  loopless := fun a ⟨h,_⟩ => h.ne rfl

lemma span_le (S : Set (Edge G)) : span G S ≤ G := fun _ _ ⟨h,_⟩ => h

/-- The canonical filter is the dual ideal of coverable edge subsets,
including directed subsets after symmetrization. -/
theorem compl_mem_iff (S : Set (Edge G)) :
    Sᶜ ∈ coveringFilter G ↔ IsCountableUnionOfTriangleFree (span G S) := by
  classical
  constructor
  · intro hS
    obtain ⟨T,hT,hTc,hsub⟩ := Filter.mem_countableGenerate_iff.mp hS
    letI : Countable T := hTc.to_subtype
    choose H hH hEq using fun t : T => hT t.property
    apply cover_of_countable_family (span G S) H hH
    intro a b hab
    by_contra hn
    push_neg at hn
    have hnot (e : Edge G) (he : e.val = (a,b) ∨ e.val = (b,a)) : e ∉ S := by
      apply hsub
      intro s hs
      have heq := hEq ⟨s,hs⟩
      change s = _ at heq
      rw [heq]
      rcases he with he | he
      · change ¬(H ⟨s,hs⟩).Adj e.val.1 e.val.2
        rw [he]
        exact hn ⟨s,hs⟩
      · change ¬(H ⟨s,hs⟩).Adj e.val.1 e.val.2
        rw [he]
        exact fun h => hn ⟨s,hs⟩ h.symm
    obtain ⟨h,hs | hs⟩ := hab
    · exact hnot ⟨(a,b),h⟩ (Or.inl rfl) hs
    · exact hnot ⟨(b,a),h.symm⟩ (Or.inr rfl) hs
  · intro hS
    have h := avoids_coverable G (coveringFilter G) (coveringFilter_avoids G) (span G S) hS
    exact h.mono fun e he hs => he ⟨e.property,Or.inl hs⟩

/-- No assumed properness is needed; when G is covered both sides are false. -/
theorem positive_iff (S : Set (Edge G)) :
    (coveringFilter G ⊓ Filter.principal S).NeBot ↔
      ¬IsCountableUnionOfTriangleFree (span G S) := by
  rw [Filter.neBot_iff,Ne,Filter.inf_principal_eq_bot,compl_mem_iff]

/-- Directed edges of an arbitrary graph, restricted to the original carrier. -/
def edges (H : SimpleGraph V) : Set (Edge G) := {e | H.Adj e.val.1 e.val.2}

lemma span_edges (H : SimpleGraph V) : span G (edges G H) = G ⊓ H := by
  ext a b
  constructor
  · rintro ⟨h,hs | hs⟩
    · exact ⟨h,hs⟩
    · exact ⟨h,hs.symm⟩
  · intro h
    exact ⟨h.1,Or.inl h.2⟩

theorem positive_edges_iff (H : SimpleGraph V) :
    (coveringFilter G ⊓ Filter.principal (edges G H)).NeBot ↔
      ¬IsCountableUnionOfTriangleFree (G ⊓ H) := by
  rw [positive_iff,span_edges]

theorem positive_subgraph_iff (H : SimpleGraph V) (hHG : H ≤ G) :
    (coveringFilter G ⊓ Filter.principal (edges G H)).NeBot ↔
      ¬IsCountableUnionOfTriangleFree H := by
  rw [positive_edges_iff,inf_eq_right.mpr hHG]

/-- Inclusion of directed edges for a spanning subgraph. -/
def inclusion (H : SimpleGraph V) (hHG : H ≤ G) : Edge H → Edge G :=
  fun e => ⟨e.val,hHG e.property⟩

/-- The canonical filter restricts exactly, not merely to an arbitrary
avoiding filter on the smaller graph. -/
theorem comap_inclusion (H : SimpleGraph V) (hHG : H ≤ G) :
    Filter.comap (inclusion G H hHG) (coveringFilter G) = coveringFilter H := by
  apply le_antisymm
  · apply le_coveringFilter H
    intro K hK
    exact Filter.preimage_mem_comap (coveringFilter_avoids G K hK)
  · apply Filter.map_le_iff_le_comap.mp
    apply le_coveringFilter G
    intro K hK
    exact coveringFilter_avoids H K hK

lemma range_inclusion (H : SimpleGraph V) (hHG : H ≤ G) :
    Set.range (inclusion G H hHG) = edges G H := by
  ext e
  constructor
  · rintro ⟨d,rfl⟩
    exact d.property
  · intro he
    exact ⟨⟨e.val,he⟩,rfl⟩

theorem map_inclusion (H : SimpleGraph V) (hHG : H ≤ G) :
    Filter.map (inclusion G H hHG) (coveringFilter H) =
      coveringFilter G ⊓ Filter.principal (edges G H) := by
  rw [← comap_inclusion G H hHG,Filter.map_comap,range_inclusion]

/-- Removing a coverable edge graph does not change whether a subgraph has
positive canonical mass. No additivity or ultrafilter assertion is used. -/
theorem positive_diff_iff (S : Set (Edge G)) (H : SimpleGraph V)
    (hH : IsCountableUnionOfTriangleFree H) :
    (coveringFilter G ⊓ Filter.principal (S \ edges G H)).NeBot ↔
      (coveringFilter G ⊓ Filter.principal S).NeBot := by
  have hc : (edges G H)ᶜ ∈ coveringFilter G :=
    avoids_coverable G (coveringFilter G) (coveringFilter_avoids G) H hH
  have he : coveringFilter G ⊓ Filter.principal (S \ edges G H) =
      coveringFilter G ⊓ Filter.principal S := by
    rw [Set.diff_eq,← Filter.inf_principal,← inf_assoc]
    calc
      coveringFilter G ⊓ Filter.principal S ⊓ Filter.principal (edges G H)ᶜ =
          coveringFilter G ⊓ Filter.principal (edges G H)ᶜ ⊓ Filter.principal S := inf_right_comm _ _ _
      _ = coveringFilter G ⊓ Filter.principal S := by
        rw [inf_eq_left.mpr (Filter.le_principal_iff.mpr hc)]
  rw [he]

#print axioms compl_mem_iff
#print axioms positive_subgraph_iff
#print axioms map_inclusion
#print axioms positive_diff_iff
end Erdos595CanonicalPositive
