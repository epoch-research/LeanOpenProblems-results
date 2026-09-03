import Submission.PathKernelTransport

/-! Polynomial-size witnesses for circuits in a labelled (possibly parallel)
edge kernel. A witness lists its distinct junctions and distinct edge labels. -/
namespace Erdos184Work.LabelKernel
open Erdos184Serial
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
variable {J W : Type*} [DecidableEq J] [DecidableEq W]

structure Cycle (src dst : J → W) (n : ℕ) where
  edge : Fin (n+2) → J
  vertex : Fin (n+2) → W
  edge_injective : Function.Injective edge
  vertex_injective : Function.Injective vertex
  endpoints : ∀ i,
    (src (edge i) = vertex i ∧ dst (edge i) = vertex (i+1)) ∨
    (dst (edge i) = vertex i ∧ src (edge i) = vertex (i+1))

namespace Cycle
variable {src dst : J → W} {n : ℕ} (C : Cycle src dst n)

def support : Finset J := Finset.univ.image C.edge

lemma edge_mem (i : Fin (n+2)) : C.edge i ∈ C.support :=
  Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩

lemma next_ne (i : Fin (n+2)) : i+1 ≠ i := by
  intro h
  have he := congrArg Fin.val h
  simp only [Fin.val_add_eq_ite,Fin.val_one] at he
  split_ifs at he <;> omega

lemma edge_next_ne (i : Fin (n+2)) : C.edge i ≠ C.edge (i+1) :=
  fun h => next_ne i (C.edge_injective h).symm

lemma incident (i j : Fin (n+2)) :
    (src (C.edge j) = C.vertex i ∨ dst (C.edge j) = C.vertex i) ↔ j = i ∨ j+1 = i := by
  rcases C.endpoints j with ⟨hsrc,hdst⟩ | ⟨hdst,hsrc⟩
  · rw [hsrc,hdst,C.vertex_injective.eq_iff,C.vertex_injective.eq_iff]
  · rw [hsrc,hdst,C.vertex_injective.eq_iff,C.vertex_injective.eq_iff]
    exact or_comm

lemma incident_next (i j : Fin (n+2)) :
    (src (C.edge j) = C.vertex (i+1) ∨ dst (C.edge j) = C.vertex (i+1)) ↔
      j = i ∨ j = i+1 := by
  rw [C.incident]
  simp only [add_right_cancel_iff,or_comm]

lemma incident_filter {t : Finset J} (ht : t ⊆ C.support) (i : Fin (n+2)) :
    t.filter (fun j => src j = C.vertex (i+1) ∨ dst j = C.vertex (i+1)) =
      ({C.edge i,C.edge (i+1)} : Finset J).filter (fun j => j ∈ t) := by
  ext e
  simp only [Finset.mem_filter,Finset.mem_insert,Finset.mem_singleton]
  constructor
  · rintro ⟨het,hei⟩
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp (ht het)
    refine ⟨?_,het⟩
    exact ((C.incident_next i j).mp hei).imp (congrArg C.edge) (congrArg C.edge)
  · rintro ⟨hei,het⟩
    refine ⟨het,?_⟩
    rcases hei with rfl | rfl
    · exact (C.incident_next i i).mpr (Or.inl rfl)
    · exact (C.incident_next i (i+1)).mpr (Or.inr rfl)

lemma valid : (code src dst).valid C.support := by
  intro w
  by_cases hw : ∃ i, C.vertex i = w
  · obtain ⟨i,rfl⟩ := hw
    have he : i-1+1 = i := sub_add_cancel i 1
    rw [← he]
    rw [C.incident_filter (Finset.Subset.refl _)]
    have h0 := C.edge_mem (i-1)
    have h1 := C.edge_mem (i-1+1)
    simp only [Finset.filter_insert,Finset.filter_singleton,h0,h1,if_true]
    rw [Finset.card_pair (C.edge_next_ne (i-1))]
    decide
  · have hf : C.support.filter (fun j => src j = w ∨ dst j = w) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro e he
      obtain ⟨hes,hew⟩ := Finset.mem_filter.mp he
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hes
      rcases C.endpoints i with ⟨hs,hd⟩ | ⟨hd,hs⟩
      · rw [hs,hd] at hew
        rcases hew with h | h
        · exact hw ⟨i,h⟩
        · exact hw ⟨i+1,h⟩
      · rw [hs,hd] at hew
        rcases hew with h | h
        · exact hw ⟨i+1,h⟩
        · exact hw ⟨i,h⟩
    rw [hf]
    simp

lemma valid_subset_step {t : Finset J} (ht : t ⊆ C.support)
    (hv : (code src dst).valid t) (i : Fin (n+2)) :
    C.edge i ∈ t ↔ C.edge (i+1) ∈ t := by
  have he := hv (C.vertex (i+1))
  rw [C.incident_filter ht i] at he
  by_cases h0 : C.edge i ∈ t <;> by_cases h1 : C.edge (i+1) ∈ t <;>
    simp [Finset.filter_insert,Finset.filter_singleton,h0,h1] at he ⊢

lemma castSucc_next (i : Fin (n+1)) : (i.castSucc : Fin (n+2))+1 = i.succ := by
  apply Fin.ext
  change (i.val+1) % (n+2) = i.val+1
  exact Nat.mod_eq_of_lt (by omega)

lemma valid_subset_all_or_none {t : Finset J} (ht : t ⊆ C.support)
    (hv : (code src dst).valid t) : t = ∅ ∨ t = C.support := by
  by_cases hn : t.Nonempty
  · right
    have hall (j : Fin (n+2)) : C.edge j ∈ t ↔ C.edge 0 ∈ t := by
      induction j using Fin.induction with
      | zero => rfl
      | succ j ih =>
        have hh := C.valid_subset_step ht hv j.castSucc
        rw [castSucc_next] at hh
        exact hh.symm.trans ih
    obtain ⟨e,he⟩ := hn
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp (ht he)
    have hzero := (hall i).mp he
    apply Finset.Subset.antisymm ht
    intro e he
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp he
    exact (hall j).mpr hzero
  · exact Or.inl (Finset.not_nonempty_iff_eq_empty.mp hn)

lemma circuit : Circuit (code src dst) C.support := by
  refine ⟨C.valid,⟨C.edge 0,C.edge_mem 0⟩,?_⟩
  intro t ht hv hn
  rcases C.valid_subset_all_or_none ht hv with h | h
  · exact False.elim ((Finset.nonempty_iff_ne_empty.mp hn) h)
  · exact h

lemma support_card : C.support.card = n+2 := by
  rw [support,Finset.card_image_of_injective _ C.edge_injective,Finset.card_univ,Fintype.card_fin]

#print axioms circuit
end Cycle
end Erdos184Work.LabelKernel
