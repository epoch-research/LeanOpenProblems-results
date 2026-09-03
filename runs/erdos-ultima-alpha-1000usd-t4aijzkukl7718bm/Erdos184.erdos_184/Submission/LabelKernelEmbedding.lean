import Submission.PathKernelTransport
import Submission.CircuitTransport

/-! Relabelling labelled kernels, allowing extra isolated junctions and
independent reversals of the orientations used to name their edges. -/
namespace Erdos184Work.LabelKernel
open Erdos184Serial
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
variable {J W J' W' : Type*} [DecidableEq J] [DecidableEq W]
    [DecidableEq J'] [DecidableEq W']

structure Embedding (src dst : J → W) (src' dst' : J' → W') where
  edge : J ↪ J'
  vertex : W ↪ W'
  endpoints : ∀ j, s(vertex (src j),vertex (dst j)) = s(src' (edge j),dst' (edge j))

namespace Embedding
variable {src dst : J → W} {src' dst' : J' → W'} (M : Embedding src dst src' dst')

lemma incident (j : J) (w : W) :
    (src' (M.edge j) = M.vertex w ∨ dst' (M.edge j) = M.vertex w) ↔
      src j = w ∨ dst j = w := by
  have hm : M.vertex w ∈ s(src' (M.edge j),dst' (M.edge j)) ↔
      M.vertex w ∈ s(M.vertex (src j),M.vertex (dst j)) := by rw [M.endpoints]
  simpa only [Sym2.mem_iff,M.vertex.injective.eq_iff,eq_comm] using hm

lemma incident_range (j : J) (w : W')
    (hw : src' (M.edge j) = w ∨ dst' (M.edge j) = w) : ∃ v, M.vertex v = w := by
  have hm : w ∈ s(src' (M.edge j),dst' (M.edge j)) := by simpa only [Sym2.mem_iff,eq_comm] using hw
  rw [← M.endpoints] at hm
  rcases Sym2.mem_iff.mp hm with h | h
  · exact ⟨src j,h.symm⟩
  · exact ⟨dst j,h.symm⟩

lemma filter_map (s : Finset J) (w : W) :
    (s.map M.edge).filter (fun j => src' j = M.vertex w ∨ dst' j = M.vertex w) =
      (s.filter (fun j => src j = w ∨ dst j = w)).map M.edge := by
  rw [Finset.filter_map]
  apply congrArg (Finset.map M.edge)
  apply Finset.filter_congr
  intro j _
  exact M.incident j w

lemma valid_map (s : Finset J) : (code src dst).valid s ↔
    (code src' dst').valid (s.map M.edge) := by
  constructor
  · intro hs w
    by_cases hw : ∃ v, M.vertex v = w
    · obtain ⟨v,rfl⟩ := hw
      rw [M.filter_map,Finset.card_map]
      exact hs v
    · have hf : (s.map M.edge).filter (fun j => src' j = w ∨ dst' j = w) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro e he
        obtain ⟨hem,hei⟩ := Finset.mem_filter.mp he
        obtain ⟨j,_,rfl⟩ := Finset.mem_map.mp hem
        exact hw (M.incident_range j w hei)
      rw [hf]
      simp
  · intro hs w
    have hh := hs (M.vertex w)
    rw [M.filter_map,Finset.card_map] at hh
    exact hh

lemma circuit_map_iff (s : Finset J) : Circuit (code src' dst') (s.map M.edge) ↔
    Circuit (code src dst) s := Erdos184Serial.circuit_map_iff M.edge M.valid_map s

lemma hasNumber_map_iff (s : Finset J) (k : ℕ) :
    HasNumber (code src' dst') (s.map M.edge) k ↔ HasNumber (code src dst) s k :=
  Erdos184Serial.hasNumber_map_iff M.edge M.valid_map s k

lemma minimalCore_map_iff (s : Finset J) (k : ℕ) :
    MinimalCore (code src' dst') (s.map M.edge) k ↔ MinimalCore (code src dst) s k :=
  Erdos184Serial.minimalCore_map_iff M.edge M.valid_map s k

lemma rigid_map_iff (s : Finset J) (k : ℕ) :
    Rigid (code src' dst') (s.map M.edge) k ↔ Rigid (code src dst) s k :=
  Erdos184Serial.rigid_map_iff M.edge M.valid_map s k

lemma upper_bound_map_iff (s : Finset J) (k : ℕ) :
    (∀ P, Partition (code src' dst') (s.map M.edge) P → P.card ≤ k) ↔
    (∀ P, Partition (code src dst) s P → P.card ≤ k) := by
  constructor
  · intro hb P hP
    obtain ⟨Q,hQ,hcQ⟩ := map_partition_exists M.edge M.valid_map hP
    rw [← hcQ]
    exact hb Q hQ
  · intro hb P hP
    obtain ⟨Q,hQ,hcQ⟩ := unmap_partition_exists M.edge M.valid_map hP
    rw [← hcQ]
    exact hb Q hQ

#print axioms upper_bound_map_iff
#print axioms minimalCore_map_iff
end Embedding
end Erdos184Work.LabelKernel
