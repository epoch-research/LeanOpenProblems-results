import Submission.FewDoubleContacts

/-! At most two pairs in any selected four-color subfamily have double
contacts, once all contacts are positive. -/
namespace Erdos184Work.AllowedFourCounts
open PairJunctionCoding
set_option maxHeartbeats 3000000
set_option maxRecDepth 20000
local instance fourDoublePermFintype : Fintype (Equiv.Perm (Fin 4)) := fintypePerm

def doublePairs (a : Fin 4 → Fin 4 → ℕ) : Finset (PairIndex 4) :=
  Finset.univ.filter (fun q => a q.val.1 q.val.2 = 2)

lemma doublePairs_valid : ∀ k : Fin 9, k ∈ FourRepresentativeKernels.allowed →
    ∀ p : Equiv.Perm (Fin 4), (∀ i j, i ≠ j → 0 < value k (p i) (p j)) →
      (doublePairs (fun i j => value k (p i) (p j))).card ≤ 2 := by
  decide +kernel

variable {I : Type*} (a : I → I → ℕ)

lemma doublePairs_le {T : Fin 4 → I} (h : Pattern a T)
    (hpos : ∀ i j, i ≠ j → 0 < a (T i) (T j)) :
    (doublePairs (fun i j => a (T i) (T j))).card ≤ 2 := by
  obtain ⟨k,hk,p,hp⟩ := h
  have he (i j : Fin 4) (hij : i ≠ j) :
      a (T i) (T j) = value k (p.symm i) (p.symm j) := by
    have hh := hp (p.symm i) (p.symm j) (p.symm.injective.ne hij)
    simpa only [p.apply_symm_apply] using hh
  have hvalues : ∀ i j, i ≠ j → 0 < value k (p.symm i) (p.symm j) := by
    intro i j hij
    rw [← he i j hij]
    exact hpos i j hij
  have hh := doublePairs_valid k hk p.symm hvalues
  have hf : doublePairs (fun i j => a (T i) (T j)) =
      doublePairs (fun i j => value k (p.symm i) (p.symm j)) := by
    ext q
    simp only [doublePairs,Finset.mem_filter,Finset.mem_univ,true_and]
    rw [he _ _ (ne_of_lt q.property)]
  rwa [← hf] at hh

#print axioms doublePairs_le
end Erdos184Work.AllowedFourCounts

open SimpleGraph
open scoped Classical
namespace Erdos184Work.FourSubfamilyPatterns
open Critical MaximumCoreFamilies
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

lemma core_double_pairs_bound {D : Finset G.Subgraph} (hD : IsMaximum G D)
    (he : ∀ v, Even (G.degree v)) (hm : EvenCore.EvenMinimal G)
    (hn : number G = 3) (hr : ¬ Rigidity.CycleRigid G)
    (T : Fin 4 → D) (hT : Function.Injective T) :
    (AllowedFourCounts.doublePairs (fun i j => ((T i).val.verts ∩ (T j).val.verts).ncard)).card ≤ 2 := by
  apply AllowedFourCounts.doublePairs_le _ (core_pattern hD he hm hn hr T hT)
  intro i j hij
  exact core_pair_contact_pos hD he hm hn hr _ _ (hT.ne hij)

#print axioms core_double_pairs_bound
end Erdos184Work.FourSubfamilyPatterns
