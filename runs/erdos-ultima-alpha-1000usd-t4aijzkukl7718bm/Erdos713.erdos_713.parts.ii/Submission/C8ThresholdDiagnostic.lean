import FormalConjecturesUtil
import Submission.UpToExpandingRegularization

/-! Diagnostic for the unresolved C8 case. This is not a proof or disproof of the conjecture. -/
open SimpleGraph Filter Asymptotics
namespace Erdos713C8ThresholdDiagnostic

lemma path8_tree : (pathGraph 8).IsTree := by
  classical
  have he : (pathGraph 8).edgeFinset =
      {s(0,1),s(1,2),s(2,3),s(3,4),s(4,5),s(5,6),s(6,7)} := by
    ext e
    induction e using Sym2.inductionOn with
    | hf a b =>
      rw [mem_edgeFinset,mem_edgeSet,pathGraph_adj]
      fin_cases a <;> fin_cases b <;> decide
  have hCard : (pathGraph 8).edgeFinset.card = 7 := by
    rw [he]
    decide
  apply isTree_iff_connected_and_card.mpr
  refine ⟨pathGraph_connected 7,?_⟩
  simpa only [edgeFinset_card,Fintype.card_eq_nat_card] using
    (show (pathGraph 8).edgeFinset.card + 1 = Fintype.card (Fin 8) by rw [hCard]; rfl)

lemma cycle8_adj_not_path : ∀ a b : Fin 8, (cycleGraph 8).Adj a b → ¬ (pathGraph 8).Adj a b →
    (a = 7 ∧ b = 0) ∨ (a = 0 ∧ b = 7) := by
  simp only [cycleGraph_adj,pathGraph_adj]
  decide

lemma strict_spanning_acyclic (J : SimpleGraph (Fin 8)) (hJ : J < cycleGraph 8) : J.IsAcyclic := by
  classical
  have hMissing : ∃ i : Fin 8, ¬ J.Adj i (i+1) := by
    by_contra hh
    push_neg at hh
    apply hJ.ne
    apply le_antisymm hJ.le
    intro u v huv
    rcases cycleGraph_adj.mp huv with h | h
    · have hu : u = v+1 := by
        have hh := congrArg (fun x : Fin 8 => x+v) h
        simp only [sub_add_cancel] at hh
        exact hh.trans (add_comm _ _)
      rw [hu]
      exact (hh v).symm
    · have hv : v = u+1 := by
        have hh := congrArg (fun x : Fin 8 => x+u) h
        simp only [sub_add_cancel] at hh
        exact hh.trans (add_comm _ _)
      rw [hv]
      exact hh u
  obtain ⟨i,hi⟩ := hMissing
  let e : Fin 8 ≃ Fin 8 := Equiv.addRight (i+1)
  have hLe : J.comap e.toEmbedding ≤ pathGraph 8 := by
    intro a b hab
    change J.Adj (a+(i+1)) (b+(i+1)) at hab
    have hc : (cycleGraph 8).Adj a b := circulantGraph_adj_translate.mp (hJ.le hab)
    by_contra hPath
    rcases cycle8_adj_not_path a b hc hPath with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · have h7 : (7 : Fin 8)+(i+1) = i := by omega
      have h0 : (0 : Fin 8)+(i+1) = i+1 := zero_add _
      rw [h7,h0] at hab
      exact hi hab
    · have h7 : (7 : Fin 8)+(i+1) = i := by omega
      have h0 : (0 : Fin 8)+(i+1) = i+1 := zero_add _
      rw [h7,h0] at hab
      exact hi hab.symm
  have hA : (J.comap e.toEmbedding).IsAcyclic :=
    path8_tree.IsAcyclic.comap (Copy.ofLE _ _ hLe).toHom (Copy.ofLE _ _ hLe).injective
  exact (Iso.comap e J).isAcyclic_iff.mp hA

lemma proper_contained_acyclic {W : Type*} (J : SimpleGraph W) (hJ : J ⊑ cycleGraph 8)
    (hNe : ¬ Nonempty (J ≃g cycleGraph 8)) : J.IsAcyclic := by
  obtain ⟨f⟩ := hJ
  have hle : J.map f.toEmbedding ≤ cycleGraph 8 :=
    (map_le_iff_le_comap f.toEmbedding J _).mpr (fun _ _ h => f.toHom.map_adj h)
  have hlt : J.map f.toEmbedding < cycleGraph 8 := lt_of_le_of_ne hle (by
    intro heq
    apply hNe
    apply Erdos713PowerCritical.iso_of_map_eq_of_no_isolates (f := f) _ heq
    intro a
    refine ⟨a+1,?_⟩
    rw [cycleGraph_adj]
    exact Or.inr (by abel))
  exact (strict_spanning_acyclic _ hlt).of_map _

lemma proper_contained_linear {W : Type*} [Fintype W] (J : SimpleGraph W)
    (hJ : J ⊑ cycleGraph 8) (hNe : ¬ Nonempty (J ≃g cycleGraph 8)) :
    (fun n : ℕ => (extremalNumber n J : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ)^ (1 : ℝ)) :=
  (Erdos713Rate.forest_rate J (proper_contained_acyclic J hJ hNe)).upper

lemma proper_gap_is_automatic {r c : ℝ} (hr : 1 < r) (hc : c ≠ 0)
    (h : IsEquivalent atTop (fun n : ℕ => (extremalNumber n (cycleGraph 8) : ℝ))
      (fun n : ℕ => c*(n : ℝ)^r)) :
    (6 : ℝ)/5 ≤ r ∧ r ≤ (5 : ℝ)/4 ∧
      (∀ (W : Type) [Fintype W] (J : SimpleGraph W), J ⊑ cycleGraph 8 →
        ¬ Nonempty (J ≃g cycleGraph 8) →
          (fun n : ℕ => (extremalNumber n J : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ)^(1 : ℝ))) := by
  obtain ⟨hLo,hHi⟩ := Erdos713C8.exponent_bounds hc h
  exact ⟨hLo,hHi,fun _ _ J hJ hNe => proper_contained_linear J hJ hNe⟩

#print axioms proper_contained_acyclic
#print axioms proper_gap_is_automatic
end Erdos713C8ThresholdDiagnostic
