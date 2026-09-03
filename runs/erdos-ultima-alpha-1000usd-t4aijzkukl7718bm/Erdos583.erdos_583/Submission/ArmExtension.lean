import Submission.StarPathPieces

/-! Extend a rooted path family across an injection by adding empty paths. -/
namespace Erdos583ArmExtensionDevelopment
open SimpleGraph Erdos583Work Erdos583StarPathPiecesDevelopment
open scoped Classical
set_option maxHeartbeats 1600000
variable {V A B : Type*} {G : SimpleGraph V}
  (rootA : A → V) (rootB : B → V) (f : A ↪ B) (hf : ∀ a, rootA a=rootB (f a))
  (P : ∀ a, Arm G (rootA a))

noncomputable def extend (b : B) : Arm G (rootB b) :=
  if hb : ∃ a, f a=b then
    let a := Classical.choose hb
    let he : rootA a=rootB b := (hf a).trans (congrArg rootB (Classical.choose_spec hb))
    ⟨(P a).finish,(P a).walk.copy he rfl,by simpa only [Walk.isPath_copy] using (P a).isPath⟩
  else ⟨rootB b,.nil,by simp⟩

lemma extend_image_edges (a : A) :
    (extend rootA rootB f hf P (f a)).walk.toSubgraph.edgeSet=(P a).walk.toSubgraph.edgeSet := by
  have hex : ∃ c, f c=f a := ⟨a,rfl⟩
  have he : Classical.choose hex=a := f.injective (Classical.choose_spec hex)
  unfold extend
  rw [dif_pos hex]
  ext e
  simp only [Walk.mem_edges_toSubgraph,Walk.edges_copy]
  rw [he]

lemma extend_image_support (a : A) :
    (extend rootA rootB f hf P (f a)).walk.support=(P a).walk.support := by
  have hex : ∃ c, f c=f a := ⟨a,rfl⟩
  have he : Classical.choose hex=a := f.injective (Classical.choose_spec hex)
  unfold extend
  rw [dif_pos hex]
  simp only [Walk.support_copy]
  change (P (Classical.choose hex)).walk.support=(P a).walk.support
  rw [he]

lemma extend_other_edges (b : B) (hb : ¬∃ a, f a=b) :
    (extend rootA rootB f hf P b).walk.toSubgraph.edgeSet=∅ := by
  unfold extend
  rw [dif_neg hb]
  simp

lemma extend_support (S : Set V) (hb : ∀ b, rootB b ∈ S)
    (hp : ∀ a, ∀ x ∈ (P a).walk.support, x ∈ S) (b : B) :
    ∀ x ∈ (extend rootA rootB f hf P b).walk.support, x ∈ S := by
  by_cases h : ∃ a, f a=b
  · obtain ⟨a,rfl⟩ := h
    rw [extend_image_support]
    exact hp a
  · unfold extend
    rw [dif_neg h]
    intro x hx
    have he : x=rootB b := by simpa only [Walk.support_nil,List.mem_singleton] using hx
    exact he ▸ hb b

lemma extend_disjoint (hp : Pairwise (fun a c ↦ Disjoint (P a).walk.toSubgraph.edgeSet (P c).walk.toSubgraph.edgeSet)) :
    Pairwise (fun b c ↦ Disjoint (extend rootA rootB f hf P b).walk.toSubgraph.edgeSet
      (extend rootA rootB f hf P c).walk.toSubgraph.edgeSet) := by
  intro b c hbc
  by_cases hb : ∃ a, f a=b
  · obtain ⟨a,rfl⟩ := hb
    rw [extend_image_edges]
    by_cases hc : ∃ d, f d=c
    · obtain ⟨d,rfl⟩ := hc
      rw [extend_image_edges]
      exact hp (fun he ↦ hbc (congrArg f he))
    · rw [extend_other_edges rootA rootB f hf P c hc]
      exact Set.disjoint_empty _
  · rw [extend_other_edges rootA rootB f hf P b hb]
    exact Set.empty_disjoint _

lemma extend_union : (⋃ b, (extend rootA rootB f hf P b).walk.toSubgraph.edgeSet)=
    ⋃ a, (P a).walk.toSubgraph.edgeSet := by
  apply Set.Subset.antisymm
  · apply Set.iUnion_subset
    intro b
    by_cases hb : ∃ a, f a=b
    · obtain ⟨a,rfl⟩ := hb
      rw [extend_image_edges]
      exact fun e he ↦ Set.mem_iUnion.mpr ⟨a,he⟩
    · rw [extend_other_edges rootA rootB f hf P b hb]
      exact Set.empty_subset _
  · apply Set.iUnion_subset
    intro a
    rw [←extend_image_edges rootA rootB f hf P a]
    exact fun e he ↦ Set.mem_iUnion.mpr ⟨f a,he⟩

lemma extend_disjoint_left (K : G.Subgraph) (hK : ∀ a, Disjoint K.edgeSet (P a).walk.toSubgraph.edgeSet)
    (b : B) : Disjoint K.edgeSet (extend rootA rootB f hf P b).walk.toSubgraph.edgeSet := by
  by_cases hb : ∃ a, f a=b
  · obtain ⟨a,rfl⟩ := hb
    rw [extend_image_edges]
    exact hK a
  · rw [extend_other_edges rootA rootB f hf P b hb]
    exact Set.disjoint_empty _

end Erdos583ArmExtensionDevelopment
