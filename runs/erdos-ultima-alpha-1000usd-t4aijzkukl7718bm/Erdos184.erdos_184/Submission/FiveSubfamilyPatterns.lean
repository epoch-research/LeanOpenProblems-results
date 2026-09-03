import Submission.FiveNumericalPatterns

/-! Transport of the five numerical contact patterns to actual cycle families.
This remains a necessary local condition, not an exclusion of all cores. -/
namespace Erdos184Work.FiveNumericalPatterns
open PairJunctionCoding
set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false

lemma classified_nat (a : Fin 5 → Fin 5 → ℕ)
    (hsym : ∀ i j, a i j = a j i)
    (hpos : ∀ i j, i ≠ j → 0 < a i j)
    (hbound : ∀ i j, i ≠ j → a i j ≤ 2)
    (hquad : ∀ T : Fin 4 → Fin 5, Function.Injective T →
      (AllowedFourCounts.doublePairs (fun i j => a (T i) (T j))).card ≤ 2) :
    ∃ k : Fin 5, ∃ p : Equiv.Perm (Fin 5), ∀ i j, i ≠ j →
      a (p i) (p j) = between (representative k) i j := by
  let b : Fin 10 → Bool := fun q => decide (a (pairCoords q).1 (pairCoords q).2 = 2)
  have he (i j : Fin 5) (hij : i ≠ j) : between b i j = a i j := by
    unfold between
    rw [if_neg hij]
    have hp := pairCoords_pairIndex i j hij
    have hbi : b (pairIndex i j) = decide (a i j = 2) := by
      rcases hp with hp | hp <;> simp only [b,hp]
      rw [hsym j i]
    rw [hbi]
    by_cases h : a i j = 2
    · simp [h]
    · have ha : a i j = 1 := by have := hpos i j hij; have := hbound i j hij; omega
      simp [ha]
  have hb : Admissible b := by
    intro v
    have hv := omit_double_card (b 0) (b 1) (b 2) (b 3) (b 4)
      (b 5) (b 6) (b 7) (b 8) (b 9) v
    have hvec : b = ![b 0,b 1,b 2,b 3,b 4,b 5,b 6,b 7,b 8,b 9] := by
      funext i
      fin_cases i <;> rfl
    rw [← hvec] at hv
    rw [hv]
    have hh := hquad (embedding v) (embedding_injective v)
    have hf : AllowedFourCounts.doublePairs (fun i j => between b (embedding v i) (embedding v j)) =
        AllowedFourCounts.doublePairs (fun i j => a (embedding v i) (embedding v j)) := by
      ext q
      simp only [AllowedFourCounts.doublePairs,Finset.mem_filter,Finset.mem_univ,true_and]
      rw [he _ _ ((embedding_injective v).ne (ne_of_lt q.property))]
    rwa [hf]
  obtain ⟨k,p,hp⟩ := classified b hb
  refine ⟨k,p,?_⟩
  intro i j hij
  rw [← he _ _ (p.injective.ne hij)]
  exact hp i j

variable {I : Type*}

def Pattern (a : I → I → ℕ) (T : Fin 5 → I) : Prop :=
  ∃ k : Fin 5, ∃ p : Equiv.Perm (Fin 5), ∀ i j, i ≠ j →
    a (T (p i)) (T (p j)) = between (representative k) i j

lemma pattern_of_counts (a : I → I → ℕ)
    (hsym : ∀ i j, a i j = a j i)
    (hpos : ∀ i j, i ≠ j → 0 < a i j)
    (hbound : ∀ i j, i ≠ j → a i j ≤ 2)
    (hquad : ∀ T : Fin 4 → I, Function.Injective T →
      (AllowedFourCounts.doublePairs (fun i j => a (T i) (T j))).card ≤ 2)
    (T : Fin 5 → I) (hT : Function.Injective T) : Pattern a T := by
  apply classified_nat (fun i j => a (T i) (T j))
  · exact fun i j => hsym _ _
  · exact fun i j hij => hpos _ _ (hT.ne hij)
  · exact fun i j hij => hbound _ _ (hT.ne hij)
  · exact fun Q hQ => hquad (T ∘ Q) (hT.comp hQ)

#print axioms classified_nat
#print axioms pattern_of_counts
end Erdos184Work.FiveNumericalPatterns

open SimpleGraph
open scoped Classical
namespace Erdos184Work.FiveSubfamilyPatterns
open Critical MaximumCoreFamilies MaximumCycles
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

lemma core_pattern {D : Finset G.Subgraph} (hD : IsMaximum G D)
    (he : ∀ v, Even (G.degree v)) (hm : EvenCore.EvenMinimal G)
    (hn : number G = 3) (hr : ¬ Rigidity.CycleRigid G)
    (T : Fin 5 → D) (hT : Function.Injective T) :
    FiveNumericalPatterns.Pattern (fun i j : D => (i.val.verts ∩ j.val.verts).ncard) T := by
  apply FiveNumericalPatterns.pattern_of_counts _ ?_ ?_ ?_ ?_ T hT
  · intro i j
    rw [Set.inter_comm]
  · exact FourSubfamilyPatterns.core_pair_contact_pos hD he hm hn hr
  · intro i j hij
    exact maximum_decomposition_intersection_le_two D hD.1 hD.2.1 hD.2.2
      i.val j.val i.property j.property (fun h => hij (Subtype.ext h))
  · exact FourSubfamilyPatterns.core_double_pairs_bound hD he hm hn hr

#print axioms core_pattern
end Erdos184Work.FiveSubfamilyPatterns
