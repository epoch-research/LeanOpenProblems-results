import Submission.CanonicalThreeReduction
import Submission.FourKernelCertificates

/-! The four-color canonical kernel with every pair meeting exactly once has
a two-circuit partition, regardless of its recursively encoded cyclic orders. -/
namespace Erdos184Work.FourSingleContactKernel
open PairJunctionCoding PairSlotMarkers CanonicalPairLayout CanonicalPairKernel CycleSegments
open LabelKernel Erdos184Serial
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

def counts : PairIndex 4 → Fin 3 := fun _ => 1

lemma marker_bound : ∀ i, 2 ≤ (markers counts i).card := by decide +kernel
lemma arity_one : ∀ i, arity counts i = 1 := by decide +kernel

noncomputable local instance : DecidableEq (Σ i, Fin (arity counts i+2)) := Classical.decEq _

def edge (j : Fin 12) : Σ i : Fin 4, Fin (arity counts i+2) :=
  ⟨⟨j.val / 3,by omega⟩,⟨j.val % 3,by
    have h := arity_one ⟨j.val / 3,by omega⟩
    omega⟩⟩

lemma edge_injective : Function.Injective edge := by
  intro i j h
  have hq : i.val / 3 = j.val / 3 := congrArg (fun e => e.1.val) h
  have hr : i.val % 3 = j.val % 3 := congrArg (fun e => e.2.val) h
  apply Fin.ext
  omega

lemma edge_surjective : Function.Surjective edge := by
  rintro ⟨i,j⟩
  have hj : j.val < 3 := by have := arity_one i; omega
  let k : Fin 12 := ⟨3*i.val+j.val,by omega⟩
  refine ⟨k,?_⟩
  have hq : (3*i.val+j.val) / 3 = i.val := by omega
  have hr : (3*i.val+j.val) % 3 = j.val := by omega
  dsimp [edge,k]
  apply Sigma.ext
  · exact Fin.ext hq
  · exact (Fin.heq_ext_iff (by rw [arity_one,arity_one])).mpr hr

def vertex : Fin 6 ↪ Fin 32 where
  toFun := ![2,4,6,12,14,22]
  inj' := by decide

def placeTable : Fin 4 → Fin 3 → Fin 32 :=
  ![![2,4,6],![2,12,14],![4,12,22],![6,14,22]]

def placement (i : Fin 4) (j : Fin (arity counts i+2)) : Fin 32 :=
  placeTable i ⟨j.val,by have := arity_one i; omega⟩

lemma placement_mem : ∀ i j, placement i j ∈ markers counts i := by decide +kernel
lemma placement_strictMono : ∀ i, StrictMono (placement i) := by
  unfold StrictMono
  decide +kernel

lemma place_eq : place counts marker_bound = placement := by
  funext i
  exact (Finset.orderEmbOfFin_unique (Nat.sub_add_cancel (marker_bound i)).symm
    (placement_mem i) (placement_strictMono i)).symm

lemma endpoints : ∀ o : ∀ i : Fin 4, Marked.Order (arity counts i), ∀ j : Fin 12,
    s(vertex (FourKernelCertificates.Layout2.src j),vertex (FourKernelCertificates.Layout2.dst j)) =
      s(source counts marker_bound o (edge j),target counts marker_bound o (edge j)) := by
  unfold source target NormalizedKernel.src NormalizedKernel.dst NormalizedKernel.word
  rw [place_eq]
  decide +kernel

noncomputable def embedding (o : ∀ i : Fin 4, Marked.Order (arity counts i)) :
    Embedding FourKernelCertificates.Layout2.src FourKernelCertificates.Layout2.dst
      (source counts marker_bound o) (target counts marker_bound o) where
  edge := ⟨edge,edge_injective⟩
  vertex := vertex
  endpoints := endpoints o

lemma full_map (o : ∀ i : Fin 4, Marked.Order (arity counts i)) :
    (Finset.univ : Finset (Fin 12)).map (embedding o).edge = Finset.univ := by
  ext e
  simp only [Finset.mem_map,Finset.mem_univ,true_and,iff_true]
  exact edge_surjective e

lemma exists_two (o : ∀ i : Fin 4, Marked.Order (arity counts i)) :
    ∃ P, Partition (code (source counts marker_bound o) (target counts marker_bound o))
      Finset.univ P ∧ P.card = 2 := by
  obtain ⟨P,hP,hcard⟩ := FourKernelCertificates.Layout2.partition_count
  obtain ⟨Q,hQ,hcQ⟩ := map_partition_exists (embedding o).edge (embedding o).valid_map hP
  rw [full_map] at hQ
  exact ⟨Q,hQ,hcQ.trans hcard⟩

lemma not_restrictions (o : ∀ i : Fin 4, Marked.Order (arity counts i)) :
    ¬ CanonicalThreeReduction.Restrictions counts marker_bound o := by
  intro h
  obtain ⟨P,hP,hcard⟩ := exists_two o
  have hb := h.1.1.2 P hP
  omega

#print axioms exists_two
#print axioms not_restrictions
end Erdos184Work.FourSingleContactKernel
