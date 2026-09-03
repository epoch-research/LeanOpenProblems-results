import Submission.PetersenBase
import Submission.PetersenWeights
import Submission.ParallelLabels

/-! A four-circuit partition of the doubled Petersen kernel is impossible. -/
namespace Erdos184Work.DoublePetersen
open Erdos184Serial LabelKernel
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
set_option Elab.async false
abbrev Edge := Fin 15 × Bool
abbrev Vertex := Fin 10

def src : Edge → Vertex := Parallel.source PetersenBase.src
def dst : Edge → Vertex := Parallel.target PetersenBase.dst
def code : Code Edge := LabelKernel.code src dst

def weight (s : Finset Edge) : ℕ := ∑ p ∈ s, 5^p.1.val

def pairIndex (e : Fin 15) : Fin 73 := ⟨e.val+1,by omega⟩
def cycleIndex (i : Fin 57) : Fin 73 := ⟨i.val+16,by omega⟩

lemma pair_weight : ∀ e : Fin 15,
    weight (Parallel.pair e) = PetersenWeights.weight (pairIndex e) := by decide +kernel

lemma cycle_weight : ∀ i : Fin 57,
    (∑ e ∈ PetersenBase.edges i, 5^e.val) = PetersenWeights.weight (cycleIndex i) := by decide +kernel

lemma full_weight : weight Finset.univ = PetersenWeights.target := by decide +kernel

lemma circuit_weight (s : Finset Edge) (hs : Circuit code s) :
    ∃ i : Fin 73, weight s = PetersenWeights.weight i := by
  rcases Parallel.circuit_cases PetersenBase.src PetersenBase.dst hs with ⟨e,rfl⟩ | ⟨t,b,ht,he⟩
  · exact ⟨pairIndex e,pair_weight e⟩
  · obtain ⟨i,rfl⟩ := PetersenBase.catalogue t ht
    refine ⟨cycleIndex i,?_⟩
    rw [he,weight]
    exact (Parallel.sum_choice PetersenBase.src PetersenBase.dst
      (fun e : Fin 15 => 5^e.val) (PetersenBase.edges i) b).trans (cycle_weight i)

lemma partition_weight {s : Finset Edge} {D : Finset (Finset Edge)} (hD : Partition code s D) :
    (∑ a ∈ D, weight a) = weight s := by
  have hh := Finset.sum_biUnion (f := fun p : Edge => 5^p.1.val) hD.2.1
  change weight (D.biUnion id) = ∑ a ∈ D, weight a at hh
  rw [hD.2.2] at hh
  exact hh.symm

lemma four_padding (n : ℕ) (hn : n ≤ 4) (f : Fin n → Fin 73) :
    ∃ a b c d : Fin 73,
      (∑ i, PetersenWeights.weight (f i)) =
        PetersenWeights.weight a + PetersenWeights.weight b +
          PetersenWeights.weight c + PetersenWeights.weight d := by
  interval_cases n
  · exact ⟨0,0,0,0,by simp [PetersenWeights.weight_zero]⟩
  · exact ⟨f 0,0,0,0,by simp [PetersenWeights.weight_zero]⟩
  · exact ⟨f 0,f 1,0,0,by simp [PetersenWeights.weight_zero,Fin.sum_univ_two]⟩
  · exact ⟨f 0,f 1,f 2,0,by simp [PetersenWeights.weight_zero,Fin.sum_univ_three,add_assoc]⟩
  · exact ⟨f 0,f 1,f 2,f 3,by simp [Fin.sum_univ_four,add_assoc]⟩

lemma lower (D : Finset (Finset Edge)) (hD : Partition code Finset.univ D) : 5 ≤ D.card := by
  classical
  by_contra hn
  have hfour : D.card ≤ 4 := by omega
  have hw (a : D) : ∃ i : Fin 73, weight a.val = PetersenWeights.weight i :=
    circuit_weight a.val (hD.1 a.val a.property)
  choose f hf using hw
  let e : Fin D.card ≃ D := (Fintype.equivFinOfCardEq (by simp)).symm
  have hs : (∑ i : Fin D.card, PetersenWeights.weight (f (e i))) = PetersenWeights.target := by
    calc
      _ = ∑ i : Fin D.card, weight (e i).val := Finset.sum_congr rfl (fun i _ => (hf (e i)).symm)
      _ = ∑ a : D, weight a.val := Equiv.sum_comp e (fun a : D => weight a.val)
      _ = ∑ a ∈ D, weight a := Finset.sum_coe_sort D weight
      _ = weight Finset.univ := partition_weight hD
      _ = PetersenWeights.target := full_weight
  obtain ⟨a,b,c,d,h⟩ := four_padding D.card hfour (f ∘ e)
  have he : PetersenWeights.weight a + PetersenWeights.weight b +
      PetersenWeights.weight c + PetersenWeights.weight d = PetersenWeights.target := h.symm.trans hs
  exact PetersenWeights.no_four a b c d he

#print axioms circuit_weight
#print axioms lower
end Erdos184Work.DoublePetersen
