import Submission.SerialMinimum

/-! The one-coordinate circuit system used for series extensions. -/
open scoped Classical
namespace Erdos184Serial
set_option maxHeartbeats 1000000

def pointCode : Code Unit where
  valid _ := True
  empty := trivial
  diff := by intros; trivial

lemma point_circuit_iff (s : Finset Unit) : Circuit pointCode s ↔ s = {()} := by
  constructor
  · intro h
    obtain ⟨x,hx⟩ := h.2.1
    cases x
    apply Finset.Subset.antisymm
    · intro y hy
      cases y
      simp
    · exact Finset.singleton_subset_iff.mpr hx
  · rintro rfl
    refine ⟨trivial,Finset.singleton_nonempty _,?_⟩
    intro t ht _ hne
    obtain ⟨x,hx⟩ := hne
    cases x
    exact Finset.Subset.antisymm ht (Finset.singleton_subset_iff.mpr hx)

lemma point_partition_eq {D : Finset (Finset Unit)}
    (hD : Partition pointCode {()} D) : D = {{()}} := by
  have hsub : D ⊆ {{()}} := by
    intro s hs
    exact Finset.mem_singleton.mpr ((point_circuit_iff s).mp (hD.1 s hs))
  have hm : () ∈ D.biUnion id := by rw [hD.2.2]; simp
  obtain ⟨s,hs,_⟩ := Finset.mem_biUnion.mp hm
  have he := (point_circuit_iff s).mp (hD.1 s hs)
  subst s
  exact Finset.Subset.antisymm hsub (Finset.singleton_subset_iff.mpr hs)

lemma point_rigid : Rigid pointCode {()} 1 := by
  intro D hD
  rw [point_partition_eq hD]
  simp

lemma point_hasNumber : HasNumber pointCode {()} 1 := by
  refine ⟨⟨{{()}},partition_singleton ((point_circuit_iff _).mpr rfl),by simp⟩,?_⟩
  intro D hD
  exact (point_rigid D hD).ge

lemma point_minimalCore : MinimalCore pointCode {()} 1 :=
  minimalCore_of_rigid trivial point_rigid

#print axioms point_minimalCore
end Erdos184Serial
