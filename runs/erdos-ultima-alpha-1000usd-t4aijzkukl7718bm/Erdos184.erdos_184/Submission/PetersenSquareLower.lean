import Submission.DoublePetersenCore

/-! Two adjacent doubled-edge deletions retain optimum at least four.
This obstructs an auxiliary square-deletion induction, not Erdős184. -/
namespace Erdos184Work.DoublePetersen.SquareLower
open Erdos184Serial LabelKernel
set_option maxHeartbeats 3000000
set_option maxRecDepth 20000

def nextEdge : Fin 15 → Fin 15 := ![1,0,0,0,0,3,3,5,5,1,2,2,4,4,6]
def mark : Fin 15 → Fin 15 → ℕ := ![![0,0,1,1,0,1,1,0,0,0,0,0,0,0,0],![0,0,1,1,0,1,1,0,0,0,0,0,0,0,0],![0,1,0,1,0,1,1,0,0,0,0,0,0,0,0],![0,0,0,0,1,1,0,1,1,0,0,0,0,0,0],![0,0,0,1,0,1,0,1,1,0,0,0,0,0,0],![1,1,1,0,0,0,1,0,0,0,0,0,0,0,0],![1,1,1,0,0,1,0,0,0,0,0,0,0,0,0],![1,1,1,0,0,0,0,0,1,0,0,0,0,0,0],![1,1,1,0,0,0,0,1,0,0,0,0,0,0,0],![1,0,0,1,1,0,0,1,0,0,0,0,0,0,0],![1,0,0,1,1,0,0,0,0,0,0,1,0,0,0],![1,0,0,1,1,0,0,0,0,0,1,0,0,0,0],![1,1,1,0,0,0,0,0,0,0,0,0,0,1,0],![1,1,1,0,0,0,0,0,0,0,0,0,1,0,0],![1,1,1,0,0,0,0,0,0,0,1,0,0,0,0]]
def rest (e : Fin 15) : Finset Edge :=
  (Finset.univ \ Parallel.pair e) \ Parallel.pair (nextEdge e)
def score (e : Fin 15) (s : Finset Edge) : ℕ := ∑ p ∈ s, mark e p.1

def pairData (e : Fin 15) : CycleData Edge Vertex :=
  ⟨0,![(e,false),(e,true)],![PetersenBase.src e,PetersenBase.dst e]⟩
lemma pairData_valid : ∀ e, (pairData e).Valid src dst := by decide +kernel
lemma pair_circuit (e : Fin 15) : Circuit code (Parallel.pair e) := by
  have h := CycleData.circuit (pairData_valid e)
  convert h using 1
  ext x
  simp [pairData,CycleData.support,Parallel.pair,Fin.exists_fin_two,eq_comm]

lemma distinct : ∀ e, nextEdge e ≠ e := by decide +kernel
lemma pairs_disjoint : ∀ e, Disjoint (Parallel.pair e) (Parallel.pair (nextEdge e)) := by decide +kernel
lemma pair_bound : ∀ e j, score e (Parallel.pair j) ≤ 2 := by decide +kernel
lemma cycle_bound : ∀ e (i : Fin 57),
    e ∉ PetersenBase.edges i → nextEdge e ∉ PetersenBase.edges i →
      (∑ j ∈ PetersenBase.edges i, mark e j) ≤ 2 := by decide +kernel
lemma rest_score : ∀ e, score e (rest e) = 8 := by decide +kernel
lemma rest_valid (e : Fin 15) : code.valid (rest e) := by
  apply code.diff
  · exact code.diff full_valid (pair_circuit e).1 (Finset.subset_univ _)
  · exact (pair_circuit (nextEdge e)).1
  · exact Finset.subset_sdiff.mpr ⟨Finset.subset_univ _,(pairs_disjoint e).symm⟩

lemma circuit_bound (e : Fin 15) (s : Finset Edge) (hs : Circuit code s)
    (hsub : s ⊆ rest e) : score e s ≤ 2 := by
  rcases Parallel.circuit_cases PetersenBase.src PetersenBase.dst hs with ⟨j,rfl⟩ | ⟨t,b,ht,he⟩
  · exact pair_bound e j
  · obtain ⟨i,rfl⟩ := PetersenBase.catalogue t ht
    have hh (j : Fin 15) (hj : j ∈ PetersenBase.edges i) :
        (j,b j) ∈ rest e := by
      apply hsub
      rw [he]
      exact Finset.mem_map.mpr ⟨j,hj,rfl⟩
    have h0 : e ∉ PetersenBase.edges i := by
      intro h
      have h' := hh e h
      simp [rest,Parallel.pair] at h'
    have h1 : nextEdge e ∉ PetersenBase.edges i := by
      intro h
      have h' := hh (nextEdge e) h
      simp [rest,Parallel.pair] at h'
    rw [he,score,Parallel.sum_choice]
    exact cycle_bound e i h0 h1

lemma lower (e : Fin 15) (D : Finset (Finset Edge))
    (hD : Partition code (rest e) D) : 4 ≤ D.card := by
  have hs := Finset.sum_biUnion (f := fun p : Edge => mark e p.1) hD.2.1
  change score e (D.biUnion id) = ∑ a ∈ D, score e a at hs
  rw [hD.2.2,rest_score] at hs
  have hb : (∑ a ∈ D, score e a) ≤ D.card * 2 := by
    calc
      _ ≤ ∑ _a ∈ D, 2 := Finset.sum_le_sum (fun a ha => circuit_bound e a (hD.1 a ha) (hD.piece_subset ha))
      _ = _ := by simp
  omega

lemma no_critical_pair_cofactor (e : Fin 15) :
    ¬ (∀ s, Circuit code s → s ⊆ Finset.univ \ Parallel.pair e →
      HasNumber code ((Finset.univ \ Parallel.pair e) \ s) 3) := by
  intro h
  have hn := h (Parallel.pair (nextEdge e)) (pair_circuit (nextEdge e))
    (Finset.subset_sdiff.mpr ⟨Finset.subset_univ _,(pairs_disjoint e).symm⟩)
  obtain ⟨D,hD,hc⟩ := hn.1
  have hb := lower e D hD
  omega

#print axioms lower
#print axioms no_critical_pair_cofactor
end Erdos184Work.DoublePetersen.SquareLower
