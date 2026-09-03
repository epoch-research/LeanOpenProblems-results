import Submission.FiveWordOrbits1Check00
import Submission.FiveWordOrbits1Check01
import Submission.FiveWordOrbits1Check02
import Submission.FiveWordOrbits1Check03
import Submission.FiveWordOrbits1Check04
import Submission.FiveWordOrbits1Check05
import Submission.FiveWordOrbits1Check06
import Submission.FiveWordOrbits1Check07
import Submission.FiveWordOrbits1Check08
import Submission.FiveWordOrbits1Check09
import Submission.FiveWordOrbits1Check10
import Submission.FiveWordOrbits1Check11
import Submission.FiveWordOrbits1Check12
import Submission.FiveWordOrbits1Check13
import Submission.FiveWordOrbits1Check14
import Submission.FiveWordOrbits1Check15
import Submission.FiveWordOrbits1Check16
import Submission.FiveWordOrbits1Check17
import Submission.FiveWordOrbits1Check18
import Submission.FiveWordOrbits1Check19
import Submission.FiveWordOrbits1Check20

/-! Assembly of the five-color word-orbit certificates. -/
open scoped Classical
namespace Erdos184Work.FiveWordOrbits1
open LabelKernel Erdos184Serial CanonicalThreeReduction FiveRows1
set_option maxHeartbeats 50000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma edge_left (i : Cases) : EdgeLeftProp i := by
  have hc : FiniteIntervals.Covers (CaseProperty EdgeLeftProp) 0 396 := (FiniteIntervals.merge (FiniteIntervals.merge (coverBlock0 EdgeLeftProp edge_left_block0) (coverBlock1 EdgeLeftProp edge_left_block1)) (FiniteIntervals.merge (coverBlock2 EdgeLeftProp edge_left_block2) (coverBlock3 EdgeLeftProp edge_left_block3)))
  exact hc i.val (Nat.zero_le _) i.isLt i.isLt
lemma edge_right (i : Cases) : EdgeRightProp i := by
  have hc : FiniteIntervals.Covers (CaseProperty EdgeRightProp) 0 396 := (FiniteIntervals.merge (FiniteIntervals.merge (coverBlock0 EdgeRightProp edge_right_block0) (coverBlock1 EdgeRightProp edge_right_block1)) (FiniteIntervals.merge (coverBlock2 EdgeRightProp edge_right_block2) (coverBlock3 EdgeRightProp edge_right_block3)))
  exact hc i.val (Nat.zero_le _) i.isLt i.isLt
lemma vertex_left (i : Cases) : VertexLeftProp i := by
  have hc : FiniteIntervals.Covers (CaseProperty VertexLeftProp) 0 396 := (FiniteIntervals.merge (FiniteIntervals.merge (coverBlock0 VertexLeftProp vertex_left_block0) (coverBlock1 VertexLeftProp vertex_left_block1)) (FiniteIntervals.merge (coverBlock2 VertexLeftProp vertex_left_block2) (coverBlock3 VertexLeftProp vertex_left_block3)))
  exact hc i.val (Nat.zero_le _) i.isLt i.isLt
lemma endpoints_valid (i : Cases) : EndpointsProp i := by
  have hc : FiniteIntervals.Covers (CaseProperty EndpointsProp) 0 396 := (FiniteIntervals.merge (FiniteIntervals.merge (coverBlock0 EndpointsProp endpoints_valid_block0) (coverBlock1 EndpointsProp endpoints_valid_block1)) (FiniteIntervals.merge (coverBlock2 EndpointsProp endpoints_valid_block2) (coverBlock3 EndpointsProp endpoints_valid_block3)))
  exact hc i.val (Nat.zero_le _) i.isLt i.isLt
lemma color_map (i : Cases) : ColorMapProp i := by
  have hc : FiniteIntervals.Covers (CaseProperty ColorMapProp) 0 396 := (FiniteIntervals.merge (FiniteIntervals.merge (coverBlock0 ColorMapProp color_map_block0) (coverBlock1 ColorMapProp color_map_block1)) (FiniteIntervals.merge (coverBlock2 ColorMapProp color_map_block2) (coverBlock3 ColorMapProp color_map_block3)))
  exact hc i.val (Nat.zero_le _) i.isLt i.isLt
lemma representative_src_row : ∀ (r : Representatives) (e : E),
    representativeSource r e = srcAt (digit0 (repKey r).val) (digit1 (repKey r).val) (digit2 (repKey r).val) (digit3 (repKey r).val) (digit4 (repKey r).val) e := by decide +kernel
lemma representative_dst_row : ∀ (r : Representatives) (e : E),
    representativeTarget r e = dstAt (digit0 (repKey r).val) (digit1 (repKey r).val) (digit2 (repKey r).val) (digit3 (repKey r).val) (digit4 (repKey r).val) e := by decide +kernel

def edgeEquiv (i : Cases) : E ≃ E where
  toFun := edgeMap i
  invFun := edgeInverse i
  left_inv := edge_left i
  right_inv := edge_right i

def caseEmbedding (i : Cases) : Embedding (inputSource i) (inputTarget i)
    (representativeSource (orbit i)) (representativeTarget (orbit i)) where
  edge := (edgeEquiv i).toEmbedding
  vertex := ⟨vertexMap i,Function.LeftInverse.injective (vertex_left i)⟩
  endpoints := endpoints_valid i

lemma exists_case (o : Orders) (h : LocalBounds b hb o) :
    ∃ i : Cases, caseKey i = ⟨key o,key_lt o⟩ := by
  have hg := FiveRows1.catalogue o h
  rw [good_eq] at hg
  obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hg
  exact ⟨i,hi⟩
noncomputable def index (o : Orders) (h : LocalBounds b hb o) : Cases := (exists_case o h).choose
lemma index_key (o : Orders) (h : LocalBounds b hb o) :
    caseKey (index o h) = ⟨key o,key_lt o⟩ := (exists_case o h).choose_spec
lemma inputSource_eq (o : Orders) (h : LocalBounds b hb o) :
    inputSource (index o h) = FlatCanonicalKernel.src b hb o := by
  funext e
  unfold inputSource
  rw [index_key]
  simp only [digit_key0,digit_key1,digit_key2,digit_key3,digit_key4]
  exact (flat_src o h e).symm
lemma inputTarget_eq (o : Orders) (h : LocalBounds b hb o) :
    inputTarget (index o h) = FlatCanonicalKernel.dst b hb o := by
  funext e
  unfold inputTarget
  rw [index_key]
  simp only [digit_key0,digit_key1,digit_key2,digit_key3,digit_key4]
  exact (flat_dst o h e).symm

noncomputable def embedding (o : Orders) (h : LocalBounds b hb o) :
    Embedding (FlatCanonicalKernel.src b hb o) (FlatCanonicalKernel.dst b hb o)
      (representativeSource (orbit (index o h))) (representativeTarget (orbit (index o h))) where
  edge := (edgeEquiv (index o h)).toEmbedding
  vertex := ⟨vertexMap (index o h),Function.LeftInverse.injective (vertex_left (index o h))⟩
  endpoints e := by
    rw [← inputSource_eq o h,← inputTarget_eq o h]
    exact endpoints_valid (index o h) e
lemma map_univ (o : Orders) (h : LocalBounds b hb o) :
    (Finset.univ : Finset E).map (embedding o h).edge = Finset.univ :=
  Finset.map_univ_equiv (edgeEquiv (index o h))
lemma embedding_colors (o : Orders) (h : LocalBounds b hb o) (e : E) :
    FlatCanonicalKernel.color b ((embedding o h).edge e) =
      colorMap (index o h) (FlatCanonicalKernel.color b e) := color_map (index o h) e
lemma exists_representative (o : Orders) (h : LocalBounds b hb o) :
    ∃ r : Representatives, Nonempty (Embedding (FlatCanonicalKernel.src b hb o)
      (FlatCanonicalKernel.dst b hb o) (representativeSource r) (representativeTarget r)) :=
  ⟨orbit (index o h),⟨embedding o h⟩⟩

#print axioms good_eq
#print axioms endpoints_valid
#print axioms exists_representative
#print axioms map_univ
#print axioms embedding_colors
end Erdos184Work.FiveWordOrbits1
