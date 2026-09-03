import Submission.FourNumericalPatterns

/-! Applying the nine numerical patterns to an actual four-cycle subfamily. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.FourNumericalPatterns
open MaximumCoreFamilies Critical MaximumCycles
set_option maxHeartbeats 2000000

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

lemma four_contacts_classified {D : Finset G.Subgraph} (hD : IsMaximum G D)
    (hdeg : ∀ x, G.degree x ≤ 4)
    (H : Fin 4 → G.Subgraph) (hH : Function.Injective H) (hmem : ∀ i, H i ∈ D)
    (hthree : ∀ T : Fin 3 → Fin 4, Function.Injective T →
      number (subfamilyGraph {H (T 0),H (T 1),H (T 2)}) ≤ 2) :
    ∃ k : Fin 9, ∃ p : Equiv.Perm (Fin 4), ∀ i j, i ≠ j →
      ((H (p i)).verts ∩ (H (p j)).verts).ncard = (between (representative k) i j).val := by
  let a : Fin 4 → Fin 4 → ℕ := fun i j => ((H i).verts ∩ (H j).verts).ncard
  have ha (i j : Fin 4) (hij : i ≠ j) : a i j ≤ 2 :=
    maximum_decomposition_intersection_le_two D hD.1 hD.2.1 hD.2.2 _ _
      (hmem i) (hmem j) (hH.ne hij)
  let b : Fin 6 → Fin 3 := ![⟨a 0 1,by have := ha 0 1 (by decide); omega⟩,
    ⟨a 0 2,by have := ha 0 2 (by decide); omega⟩,
    ⟨a 0 3,by have := ha 0 3 (by decide); omega⟩,
    ⟨a 1 2,by have := ha 1 2 (by decide); omega⟩,
    ⟨a 1 3,by have := ha 1 3 (by decide); omega⟩,
    ⟨a 2 3,by have := ha 2 3 (by decide); omega⟩]
  have ht (T : Fin 3 → Fin 4) (hT : Function.Injective T) :
      AdmissibleTriple (a (T 0) (T 1)) (a (T 0) (T 2)) (a (T 1) (T 2)) :=
    maximum_triple_admissible hD hdeg (H ∘ T) (hH.comp hT) (fun i => hmem (T i)) (hthree T hT)
  have hb : Admissible b := by
    refine ⟨?_,?_,?_,?_⟩
    · exact ht ![0,1,2] (by decide)
    · exact ht ![0,1,3] (by decide)
    · exact ht ![0,2,3] (by decide)
    · exact ht ![1,2,3] (by decide)
  obtain ⟨k,p,hp⟩ := classified b hb
  have hab (i j : Fin 4) (hij : i ≠ j) : a i j = (between b i j).val := by
    fin_cases i <;> fin_cases j <;>
      simp_all only [Fin.zero_eta,Fin.isValue,ne_eq,not_true_eq_false] <;>
      simp [between,pairIndex,b,a,Set.inter_comm] <;>
      exact congrArg Set.ncard (Set.inter_comm _ _)
  refine ⟨k,p,?_⟩
  intro i j hij
  change a (p i) (p j) = _
  rw [hab _ _ (p.injective.ne hij),hp i j]

#print axioms four_contacts_classified
end Erdos184Work.FourNumericalPatterns
