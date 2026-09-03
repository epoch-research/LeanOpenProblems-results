import Submission.PathKernelTransport

/-! Finite marker certificates for exact kernel circuit counts. -/
namespace Erdos184Serial
variable {E : Type*} [DecidableEq E]

lemma Partition.marker_count {C : Code E} {s : Finset E} {D : Finset (Finset E)}
    (hD : Partition C s D) (M : Finset E) (d : ℕ)
    (hc : ∀ a, Circuit C a → (a ∩ M).card = d) :
    D.card * d = (s ∩ M).card := by
  have hdis : Set.PairwiseDisjoint (D : Set (Finset E)) (fun a => a ∩ M) := by
    intro a ha b hb hne
    exact (hD.2.1 ha hb hne).mono Finset.inter_subset_left Finset.inter_subset_left
  have he := Finset.card_biUnion hdis
  rw [← Finset.biUnion_inter] at he
  change (D.biUnion id ∩ M).card = _ at he
  rw [hD.2.2] at he
  calc
    D.card * d = ∑ _a ∈ D, d := by simp
    _ = ∑ a ∈ D, (a ∩ M).card := Finset.sum_congr rfl (fun a ha => (hc a (hD.1 a ha)).symm)
    _ = (s ∩ M).card := he.symm

lemma rigid_of_marker (C : Code E) (s M : Finset E) (d k : ℕ) (hd : d ≠ 0)
    (hc : ∀ a, Circuit C a → (a ∩ M).card = d) (hs : (s ∩ M).card = k * d) :
    Rigid C s k := by
  intro D hD
  have hh := hD.marker_count M d hc
  rw [hs] at hh
  exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hd) hh

lemma hasNumber_of_rigid (C : Code E) (s : Finset E) (k : ℕ)
    (hv : C.valid s) (hr : Rigid C s k) : HasNumber C s k := by
  obtain ⟨D,hD⟩ := exists_partition C hv
  exact ⟨⟨D,hD,hr D hD⟩,fun A hA => Nat.le_of_eq (hr A hA).symm⟩
end Erdos184Serial

namespace Erdos184Work.NonAlternate220
open Erdos184Serial
set_option maxHeartbeats 50000000
set_option maxRecDepth 100000

def src : Fin 8 → Fin 4 := ![0,1,2,3,0,1,2,3]
def dst : Fin 8 → Fin 4 := ![1,2,3,0,1,0,3,2]
def code : Code (Fin 8) := LabelKernel.code src dst
def markers : Finset (Fin 8) := {0,2,4,5,6,7}
instance valid_decidable (s : Finset (Fin 8)) : Decidable (code.valid s) := by
  unfold code LabelKernel.code LabelKernel.valid
  infer_instance
instance circuit_decidable (s : Finset (Fin 8)) : Decidable (Circuit code s) := by
  unfold Circuit
  infer_instance
lemma full_valid : code.valid Finset.univ := by decide
lemma circuit_marker : ∀ a, Circuit code a → (a ∩ markers).card = 2 := by decide
lemma full_rigid : Rigid code Finset.univ 3 :=
  rigid_of_marker code Finset.univ markers 2 3 (by decide) circuit_marker (by decide)
lemma full_number : HasNumber code Finset.univ 3 :=
  hasNumber_of_rigid code Finset.univ 3 full_valid full_rigid

#print axioms full_number
#print axioms full_rigid
end Erdos184Work.NonAlternate220
