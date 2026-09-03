import Submission.LabelKernelEmbedding

/-! Color-local bounds and their transport under relabellings of labelled kernels.
This interface makes no assertion that arbitrary minimal cores satisfy a uniform bound. -/
open scoped Classical
namespace Erdos184Work.LabelKernel
open Erdos184Serial
set_option maxHeartbeats 1000000

variable {E F W Z I J : Type*} [Fintype E] [Fintype F]
  [DecidableEq E] [DecidableEq F] [DecidableEq W] [DecidableEq Z]
  [DecidableEq I] [DecidableEq J]

def colorSet (color : E → I) (A : Finset I) : Finset E :=
  Finset.univ.filter fun e => color e ∈ A

@[simp] lemma mem_colorSet (color : E → I) (A : Finset I) (e : E) :
    e ∈ colorSet color A ↔ color e ∈ A := by simp [colorSet]

/-- Every color subfamily is maximum in its displayed number of colors;
every three-color subfamily has a decomposition of size at most two. -/
def ColorLocalBounds (src dst : E → W) (color : E → I) : Prop :=
  (∀ A : Finset I, ∀ P, Partition (code src dst) (colorSet color A) P →
    P.card ≤ A.card) ∧
  (∀ A : Finset I, A.card = 3 → ∃ P,
    Partition (code src dst) (colorSet color A) P ∧ P.card ≤ 2)

lemma map_colorSet (e : E ≃ F) (c : I ≃ J) (color : E → I) (color' : F → J)
    (hcolor : ∀ a, color' (e a) = c (color a)) (A : Finset I) :
    (colorSet color A).map e.toEmbedding = colorSet color' (A.map c.toEmbedding) := by
  ext b
  simp only [Finset.mem_map, mem_colorSet]
  constructor
  · rintro ⟨a,ha,rfl⟩
    exact ⟨color a,ha,(hcolor a).symm⟩
  · rintro ⟨i,hi,hb⟩
    refine ⟨e.symm b,?_,e.apply_symm_apply b⟩
    have he : color (e.symm b) = i := by
      apply c.injective
      rw [← hcolor,e.apply_symm_apply]
      exact hb.symm
    rwa [he]

lemma ColorLocalBounds.transport {src dst : E → W} {src' dst' : F → Z}
    {color : E → I} {color' : F → J}
    (h : ColorLocalBounds src dst color)
    (e : E ≃ F) (c : I ≃ J)
    (M : Embedding src dst src' dst') (he : M.edge = e.toEmbedding)
    (hcolor : ∀ a, color' (e a) = c (color a)) :
    ColorLocalBounds src' dst' color' := by
  have hm (A : Finset I) : (colorSet color A).map M.edge =
      colorSet color' (A.map c.toEmbedding) := by
    rw [he]
    exact map_colorSet e c color color' hcolor A
  have hall (B : Finset J) :
      (B.map c.symm.toEmbedding).map c.toEmbedding = B := by
    ext j
    simp
  constructor
  · intro B P hP
    have hP' : Partition (code src' dst')
        ((colorSet color (B.map c.symm.toEmbedding)).map M.edge) P := by
      rw [hm,hall]
      exact hP
    obtain ⟨Q,hQ,hcard⟩ := unmap_partition_exists M.edge M.valid_map hP'
    have hu := h.1 (B.map c.symm.toEmbedding) Q hQ
    rw [Finset.card_map] at hu
    omega
  · intro B hB
    obtain ⟨Q,hQ,hcard⟩ := h.2 (B.map c.symm.toEmbedding) (by simpa using hB)
    obtain ⟨P,hP,hPQ⟩ := map_partition_exists M.edge M.valid_map hQ
    rw [hm,hall] at hP
    exact ⟨P,hP,by omega⟩

lemma ColorLocalBounds.pullback {src dst : E → W} {src' dst' : F → Z}
    {color : E → I} {color' : F → J}
    (h : ColorLocalBounds src' dst' color')
    (e : E ≃ F) (c : I ≃ J)
    (M : Embedding src dst src' dst') (he : M.edge = e.toEmbedding)
    (hcolor : ∀ a, color' (e a) = c (color a)) :
    ColorLocalBounds src dst color := by
  have hm (A : Finset I) : (colorSet color A).map M.edge =
      colorSet color' (A.map c.toEmbedding) := by
    rw [he]
    exact map_colorSet e c color color' hcolor A
  constructor
  · intro A P hP
    obtain ⟨Q,hQ,hcard⟩ := map_partition_exists M.edge M.valid_map hP
    rw [hm] at hQ
    have hu := h.1 (A.map c.toEmbedding) Q hQ
    rw [Finset.card_map] at hu
    omega
  · intro A hA
    obtain ⟨Q,hQ,hcard⟩ := h.2 (A.map c.toEmbedding) (by simpa using hA)
    rw [← hm] at hQ
    obtain ⟨P,hP,hPQ⟩ := unmap_partition_exists M.edge M.valid_map hQ
    exact ⟨P,hP,by omega⟩

#print axioms ColorLocalBounds.transport
#print axioms ColorLocalBounds.pullback
end Erdos184Work.LabelKernel
