import Submission.DoublePetersenCertificates

/-! The doubled Petersen kernel is cycle-critical but not a minimal core.
This does not disprove the original decomposition conjecture. -/
namespace Erdos184Work.DoublePetersen
open Erdos184Serial LabelKernel
set_option maxHeartbeats 3000000

lemma full_valid : code.valid Finset.univ := by
  change LabelKernel.valid src dst Finset.univ
  unfold LabelKernel.valid
  decide +kernel

lemma cofactor_number (s : Finset Edge) (hs : Circuit code s) :
    HasNumber code (Finset.univ \ s) 4 := by
  refine ⟨cofactor_upper s hs,?_⟩
  intro D hD
  have hd : ∀ a ∈ D, Disjoint s a := by
    intro a ha
    apply Finset.disjoint_left.mpr
    intro e hes hea
    exact (Finset.mem_sdiff.mp (hD.piece_subset ha hea)).2 hes
  have hp : Partition code Finset.univ (insert s D) := by
    refine ⟨?_,?_,?_⟩
    · intro a ha
      rcases Finset.mem_insert.mp ha with rfl | ha
      · exact hs
      · exact hD.1 a ha
    · rw [Finset.coe_insert]
      exact hD.2.1.insert (fun a ha _ => hd a ha)
    · rw [Finset.biUnion_insert,hD.2.2]
      exact Finset.union_sdiff_of_subset (Finset.subset_univ s)
  have hb := lower (insert s D) hp
  have hc := Finset.card_insert_le s D
  omega

def matchingBase : Finset (Fin 15) := {2,4,6,8,9}
def matching : Finset Edge := Finset.univ.filter (fun e => e.1 ∈ matchingBase)

lemma matching_valid : code.valid matching := by
  change LabelKernel.valid src dst matching
  unfold LabelKernel.valid
  decide +kernel
lemma matching_card : matching.card = 10 := by decide +kernel
lemma matching_proper : matching ⊂ Finset.univ := by decide +kernel
lemma no_base_cycle : ∀ i : Fin 57, ¬ PetersenBase.edges i ⊆ matchingBase := by decide +kernel

lemma matching_circuit_card (a : Finset Edge) (ha : Circuit code a) (hm : a ⊆ matching) : a.card = 2 := by
  rcases Parallel.circuit_cases PetersenBase.src PetersenBase.dst ha with ⟨e,rfl⟩ | ⟨t,b,ht,he⟩
  · simp [Parallel.pair]
  · obtain ⟨i,rfl⟩ := PetersenBase.catalogue t ht
    apply False.elim
    apply no_base_cycle i
    intro e hee
    have hp : (e,b e) ∈ a := by
      rw [he]
      exact Finset.mem_map.mpr ⟨e,hee,rfl⟩
    exact (Finset.mem_filter.mp (hm hp)).2

lemma matching_rigid : Rigid code matching 5 := by
  intro D hD
  have h := Finset.card_biUnion hD.2.1
  change (D.biUnion id).card = ∑ a ∈ D, a.card at h
  rw [hD.2.2,matching_card] at h
  have he : (∑ a ∈ D, a.card) = D.card * 2 :=
    Finset.sum_const_nat (fun a ha => matching_circuit_card a (hD.1 a ha) (hD.piece_subset ha))
  omega

lemma matching_number : HasNumber code matching 5 := by
  obtain ⟨D,hD⟩ := exists_partition code matching_valid
  exact ⟨⟨D,hD,matching_rigid D hD⟩,fun A hA => (matching_rigid A hA).symm.le⟩

lemma not_minimal : ¬ MinimalCore code Finset.univ 5 := by
  intro h
  obtain ⟨D,hD,hcD⟩ := h.2 matching matching_proper matching_valid
  have hn := matching_number.2 D hD
  omega

#print axioms cofactor_number
#print axioms matching_number
#print axioms not_minimal
end Erdos184Work.DoublePetersen
