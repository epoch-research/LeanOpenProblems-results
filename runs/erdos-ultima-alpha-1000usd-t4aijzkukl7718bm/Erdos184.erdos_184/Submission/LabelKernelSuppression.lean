import Submission.LabelKernelSubdivision

/-! Suppressing a private degree-two junction in a labelled kernel, with exact
transport for every support. The other endpoints must be distinct: suppressing
a whole two-edge cycle into a loop is deliberately excluded. -/
open scoped Classical
namespace Erdos184Work.LabelKernel
open Erdos184Serial
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
variable {J W : Type*} [DecidableEq J] [DecidableEq W]

structure Suppression (src dst : J → W) where
  left : J
  right : J
  middle : W
  distinct : left ≠ right
  left_src : src left ≠ middle
  left_dst : dst left = middle
  right_src : src right = middle
  right_dst : dst right ≠ middle
  outside : src left ≠ dst right
  private_incidence : ∀ j, src j = middle ∨ dst j = middle → j = left ∨ j = right

namespace Suppression
variable {src dst : J → W} (S : Suppression src dst)

abbrev Edge := {j : J // j ≠ S.right}
abbrev Vertex := {w : W // w ≠ S.middle}

def port : S.Edge := ⟨S.left,S.distinct⟩

lemma source_ne (j : S.Edge) : src j.val ≠ S.middle := by
  intro h
  rcases S.private_incidence j.val (Or.inl h) with hj | hj
  · exact S.left_src (hj ▸ h)
  · exact j.property hj

lemma target_ne (j : S.Edge) (hj : j.val ≠ S.left) : dst j.val ≠ S.middle := by
  intro h
  rcases S.private_incidence j.val (Or.inr h) with hleft | hright
  · exact hj hleft
  · exact j.property hright

def source (j : S.Edge) : S.Vertex := ⟨src j.val,S.source_ne j⟩

def target (j : S.Edge) : S.Vertex :=
  if h : j.val = S.left then ⟨dst S.right,S.right_dst⟩ else ⟨dst j.val,S.target_ne j h⟩

@[simp] lemma source_val (j : S.Edge) : (S.source j).val = src j.val := rfl
@[simp] lemma port_val : S.port.val = S.left := rfl
@[simp] lemma target_port : (S.target S.port).val = dst S.right := by simp [target,port]

lemma port_loopless : S.source S.port ≠ S.target S.port := by
  intro h
  have hh := congrArg Subtype.val h
  exact S.outside (by simpa using hh)

def edgeEmbedding : S.Edge ⊕ Unit ↪ J where
  toFun
    | .inl j => j.val
    | .inr _ => S.right
  inj' := by
    intro i j h
    cases i with
    | inl i =>
      cases j with
      | inl j => exact congrArg Sum.inl (Subtype.ext h)
      | inr u => exact (i.property h).elim
    | inr u =>
      cases j with
      | inl j => exact (j.property h.symm).elim
      | inr v => cases u; cases v; rfl

def vertexEmbedding : S.Vertex ⊕ Unit ↪ W where
  toFun
    | .inl w => w.val
    | .inr _ => S.middle
  inj' := by
    intro i j h
    cases i with
    | inl i =>
      cases j with
      | inl j => exact congrArg Sum.inl (Subtype.ext h)
      | inr u => exact (i.property h).elim
    | inr u =>
      cases j with
      | inl j => exact (j.property h.symm).elim
      | inr v => cases u; cases v; rfl

def embedding : Embedding (Subdivision.source S.source) (Subdivision.target S.target S.port) src dst where
  edge := S.edgeEmbedding
  vertex := S.vertexEmbedding
  endpoints j := by
    cases j with
    | inl j =>
      by_cases hj : j.val = S.left
      · have hport : j = S.port := Subtype.ext hj
        subst j
        simp [Subdivision.source,Subdivision.target,edgeEmbedding,vertexEmbedding,
          source,port,S.left_dst]
      · have hport : j ≠ S.port := fun h => hj (congrArg Subtype.val h)
        simp [Subdivision.source,Subdivision.target,edgeEmbedding,vertexEmbedding,
          source,target,hj,hport]
    | inr u =>
      cases u
      simp [Subdivision.source,Subdivision.target,edgeEmbedding,vertexEmbedding,
        S.right_src]

noncomputable def transport : SupportTransport (code S.source S.target) (code src dst) :=
  (Subdivision.transport S.source S.target S.port S.port_loopless).trans
    (SupportTransport.ofEmbedding S.embedding.edge S.embedding.valid_map)

lemma expand_eq (s : Finset S.Edge) :
    S.transport.expand s = (Series.expand S.port s).map S.edgeEmbedding := rfl

lemma mem_expand (s : Finset S.Edge) (j : J) :
    j ∈ S.transport.expand s ↔
      (∃ i ∈ s, i.val = j) ∨ (S.port ∈ s ∧ j = S.right) := by
  rw [S.expand_eq,Finset.mem_map]
  constructor
  · rintro ⟨i,hi,rfl⟩
    cases i with
    | inl i => exact Or.inl ⟨i,(Series.mem_expand_left S.port s i).mp hi,rfl⟩
    | inr u => exact Or.inr ⟨(Series.mem_expand_right S.port s u).mp hi,rfl⟩
  · rintro (⟨i,hi,rfl⟩ | ⟨hi,rfl⟩)
    · exact ⟨.inl i,(Series.mem_expand_left S.port s i).mpr hi,rfl⟩
    · exact ⟨.inr (),(Series.mem_expand_right S.port s ()).mpr hi,rfl⟩

lemma expand_univ [Fintype J] : S.transport.expand Finset.univ = Finset.univ := by
  ext j
  simp only [S.mem_expand,Finset.mem_univ,true_and,iff_true]
  by_cases hj : j = S.right
  · exact Or.inr hj
  · exact Or.inl ⟨⟨j,hj⟩,rfl⟩

lemma partition_spectrum_univ_iff [Fintype J] (P : ℕ → Prop) :
    (∃ D, Partition (code src dst) Finset.univ D ∧ P D.card) ↔
      (∃ D, Partition (code S.source S.target) Finset.univ D ∧ P D.card) := by
  have h := S.transport.exists_partition_card_iff Finset.univ P
  rwa [S.expand_univ] at h

lemma minimalCore_univ_iff [Fintype J] (k : ℕ) :
    MinimalCore (code src dst) Finset.univ k ↔
      MinimalCore (code S.source S.target) Finset.univ k := by
  have h := S.transport.minimalCore_iff Finset.univ k
  rwa [S.expand_univ] at h

lemma rigid_univ_iff [Fintype J] (k : ℕ) :
    Rigid (code src dst) Finset.univ k ↔
      Rigid (code S.source S.target) Finset.univ k := by
  have h := S.transport.rigid_iff Finset.univ k
  rwa [S.expand_univ] at h

lemma expand_colors [Fintype J] {K : Type*} [DecidableEq K]
    (color : J → K) (hc : color S.left = color S.right) (A : Finset K) :
    S.transport.expand (Finset.univ.filter (fun j : S.Edge => color j.val ∈ A)) =
      Finset.univ.filter (fun j => color j ∈ A) := by
  ext j
  simp only [S.mem_expand,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · rintro (⟨i,hi,rfl⟩ | ⟨hi,rfl⟩)
    · exact hi
    · simpa only [S.port_val,hc] using hi
  · intro hj
    by_cases he : j = S.right
    · right
      exact ⟨by simpa only [S.port_val,hc,he] using hj,he⟩
    · exact Or.inl ⟨⟨j,he⟩,hj,rfl⟩

lemma partition_spectrum_colors_iff [Fintype J] {K : Type*} [DecidableEq K]
    (color : J → K) (hc : color S.left = color S.right) (A : Finset K) (P : ℕ → Prop) :
    (∃ D, Partition (code src dst) (Finset.univ.filter (fun j => color j ∈ A)) D ∧ P D.card) ↔
      (∃ D, Partition (code S.source S.target)
        (Finset.univ.filter (fun j : S.Edge => color j.val ∈ A)) D ∧ P D.card) := by
  have h := S.transport.exists_partition_card_iff
    (Finset.univ.filter (fun j : S.Edge => color j.val ∈ A)) P
  rwa [S.expand_colors color hc A] at h

#print axioms transport
#print axioms partition_spectrum_colors_iff
#print axioms minimalCore_univ_iff
end Suppression
end Erdos184Work.LabelKernel
