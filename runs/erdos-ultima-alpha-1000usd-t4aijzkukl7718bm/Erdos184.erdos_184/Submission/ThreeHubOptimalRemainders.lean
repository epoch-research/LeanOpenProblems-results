import Submission.NoBestMinimalRemainder
import Submission.TightDual

/-! Optimal even remainders of K_(3,3q+1) have exact half-star dual
certificates. For q >= 3 none is even-minimal. These are auxiliary family
results, not a proof of the conjecture in Spec.lean. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.ThreeHubOptimalRemainders
open Critical EvenCore SingletonExchange ThreeHubCompleteNumber
open CycleCertificates TightDual
set_option maxHeartbeats 1600000

abbrev source (q : ℕ) := graph (3*q+1)

lemma source_number (q : ℕ) (hq : 1 ≤ q) : number (source q) = 4*q+2 := by
  have h := exact_number (3*q+1) (by omega)
  change number (source q) = _ at h
  omega

lemma source_card (q : ℕ) : Nat.card (source q).edgeSet = 9*q+3 := by
  have h := BipartiteLower.complete_edge_card (A := Fin 3) (B := Fin (3*q+1))
  simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card, Nat.card_fin] at h
  change Nat.card (source q).edgeSet = _ at h
  omega

lemma singleton_lower {q : ℕ} {F : SimpleGraph (Fin 3 ⊕ Fin (3*q+1))}
    (hF : Optimal (source q) F) : 3*q+1 ≤ Nat.card F.edgeSet := by
  have hd (b : Fin (3*q+1)) : 1 ≤ F.degree (.inr b) := by
    have he := Nat.even_iff.mp (hF.2.1 (.inr b))
    have hg := degree_sdiff_add (source q) F hF.1 (.inr b)
    have hs := BipartiteLower.complete_degree_right (A := Fin 3) b
    simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card,
      Nat.card_fin] at hg hs ⊢
    change Nat.card ((source q).neighborSet (.inr b)) = 3 at hs
    omega
  have he := (BipartiteLower.bipartite_edge_sums F hF.1).2
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun b _ => hd b)
  simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card,
    Finset.sum_const, Finset.card_univ, Nat.card_fin, smul_eq_mul, mul_one,
    SimpleGraph.edgeFinset_card] at hs he
  omega

lemma remainder_card_add {q : ℕ} {F : SimpleGraph (Fin 3 ⊕ Fin (3*q+1))}
    (hF : Optimal (source q) F) :
    Nat.card ((source q) \ F).edgeSet + Nat.card F.edgeSet = 9*q+3 := by
  have h := Finset.card_sdiff_add_card_eq_card (SimpleGraph.edgeFinset_mono hF.1)
  rw [← SimpleGraph.edgeFinset_sdiff] at h
  simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] at h
  exact h.trans (source_card q)

lemma remainder_edge_bound {q : ℕ} {F : SimpleGraph (Fin 3 ⊕ Fin (3*q+1))}
    (hF : Optimal (source q) F) :
    Nat.card ((source q) \ F).edgeSet ≤ 6 * number ((source q) \ F) := by
  let E := (source q) \ F
  have he := (BipartiteLower.bipartite_edge_sums E
    (show E ≤ completeBipartiteGraph (Fin 3) (Fin (3*q+1)) from sdiff_le)).1
  simp only [SimpleGraph.edgeFinset_card, ← SimpleGraph.card_neighborSet_eq_degree,
    ← Nat.card_eq_fintype_card] at he
  have hd (a : Fin 3) : Nat.card (E.neighborSet (.inl a)) ≤ 2 * number E := by
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using StarCore.number_degree_bound E (.inl a)
  change Nat.card E.edgeSet ≤ 6 * number E
  rw [he]
  calc
    _ ≤ ∑ _a : Fin 3, 2 * number E := Finset.sum_le_sum (fun a _ => hd a)
    _ = _ := by simp; omega

lemma optimal_counts {q : ℕ} (hq : 1 ≤ q)
    {F : SimpleGraph (Fin 3 ⊕ Fin (3*q+1))} (hF : Optimal (source q) F) :
    Nat.card F.edgeSet = 3*q+1 ∧ number ((source q) \ F) = q+1 ∧
      Nat.card ((source q) \ F).edgeSet = 6*q+2 := by
  have hl := singleton_lower hF
  have hc := remainder_card_add hF
  have he := remainder_edge_bound hF
  have hn := hF.2.2
  rw [source_number q hq] at hn
  omega

lemma every_optimal_best {q : ℕ} (hq : 1 ≤ q)
    {F : SimpleGraph (Fin 3 ⊕ Fin (3*q+1))} (hF : Optimal (source q) F) :
    Best (source q) F := by
  refine ⟨hF,?_⟩
  intro R hR
  rw [(optimal_counts hq hF).1, (optimal_counts hq hR).1]

lemma saturated_hub {q : ℕ} (hq : 1 ≤ q)
    {F : SimpleGraph (Fin 3 ⊕ Fin (3*q+1))} (hF : Optimal (source q) F) :
    ∃ a : Fin 3, Nat.card (((source q) \ F).neighborSet (.inl a)) = 2*q+2 := by
  let E := (source q) \ F
  obtain ⟨_,hEn,hEC⟩ := optimal_counts hq hF
  have hEe := hF.2.1
  change number E = q+1 at hEn
  change Nat.card E.edgeSet = 6*q+2 at hEC
  by_contra! hn
  have hd (a : Fin 3) : Nat.card (E.neighborSet (.inl a)) ≤ 2*q := by
    have hb := StarCore.number_degree_bound E (.inl a)
    have he := Nat.even_iff.mp (hEe (.inl a))
    have hh := hn a
    simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hb
    rw [hEn] at hb
    change Nat.card (E.neighborSet (.inl a)) ≠ 2*q+2 at hh
    change Nat.card (E.neighborSet (.inl a)) % 2 = 0 at he
    omega
  have hs := (BipartiteLower.bipartite_edge_sums E
    (show E ≤ completeBipartiteGraph (Fin 3) (Fin (3*q+1)) from sdiff_le)).1
  simp only [SimpleGraph.edgeFinset_card, ← SimpleGraph.card_neighborSet_eq_degree,
    ← Nat.card_eq_fintype_card] at hs
  have hb : (∑ a : Fin 3, Nat.card (E.neighborSet (.inl a))) ≤ 6*q := by
    calc
      _ ≤ ∑ _a : Fin 3, 2*q := Finset.sum_le_sum (fun a _ => hd a)
      _ = _ := by simp; omega
  omega

/-- A half-star always satisfies the upper cycle inequalities, regardless of
whether every cycle meets its center. -/
lemma feedbackWeight_upper {W : Type*} [Fintype W] (G : SimpleGraph W) (v : W) :
    CycleUpperWeight G (feedbackWeight v) := by
  intro u p hp
  have hreg := (cycle_coe_regular G hp).2
  have hd := regular_two_spanning_degree p.toSubgraph (by
    simpa only [SimpleGraph.IsRegularOfDegree, ← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] using hreg) v
  rw [← cycle_edge_weight p hp, feedbackWeight_total, hd]
  split_ifs <;> norm_num

lemma optimal_exact_dual {q : ℕ} (hq : 1 ≤ q)
    {F : SimpleGraph (Fin 3 ⊕ Fin (3*q+1))} (hF : Optimal (source q) F) :
    ∃ w : Sym2 (Fin 3 ⊕ Fin (3*q+1)) → ℝ,
      CycleUpperWeight ((source q) \ F) w ∧
      (∑ e ∈ ((source q) \ F).edgeFinset, w e) = (number ((source q) \ F) : ℝ) := by
  obtain ⟨a,ha⟩ := saturated_hub hq hF
  refine ⟨feedbackWeight (.inl a),feedbackWeight_upper _ _,?_⟩
  have hw := feedbackWeight_total ((source q) \ F) (.inl a)
  have hn := (optimal_counts hq hF).2.1
  simp only [SimpleGraph.edgeFinset, ← Set.toFinite_toFinset,
    ← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hw ⊢
  rw [hw,ha,hn]
  push_cast
  ring

lemma any_optimal_not_evenMinimal {q : ℕ} (hq : 3 ≤ q)
    {F : SimpleGraph (Fin 3 ⊕ Fin (3*q+1))} (hF : Optimal (source q) F) :
    ¬ EvenMinimal ((source q) \ F) := by
  let E := (source q) \ F
  obtain ⟨_,hEn,hEC⟩ := optimal_counts (by omega) hF
  obtain ⟨a,ha⟩ := saturated_hub (by omega) hF
  intro hm
  change EvenMinimal E at hm
  have hacy : (E.induce ({Sum.inl a}ᶜ : Set (Fin 3 ⊕ Fin (3*q+1)))).IsAcyclic := by
    apply (StarCore.EvenMinimal.saturated_vertex hm ?_ (Sum.inl a) ?_).1
    · simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
        using hF.2.1
    · simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      change Nat.card (((source q) \ F).neighborSet (.inl a)) = 2 * number ((source q) \ F)
      rw [ha,hEn]
      omega
  letI : Nonempty ({Sum.inl a}ᶜ : Set (Fin 3 ⊕ Fin (3*q+1))) :=
    ⟨⟨Sum.inr 0,by simp⟩⟩
  have hf := acyclic_card_edges_lt (E.induce ({Sum.inl a}ᶜ : Set (Fin 3 ⊕ Fin (3*q+1)))) hacy
  have hv : Fintype.card ({Sum.inl a}ᶜ : Set (Fin 3 ⊕ Fin (3*q+1))) = 3*q+3 := by
    rw [Fintype.card_compl_set]
    simp
    omega
  have he : (E.induce ({Sum.inl a}ᶜ : Set (Fin 3 ⊕ Fin (3*q+1)))).edgeFinset.card +
      E.degree (.inl a) = E.edgeFinset.card := by
    rw [SimpleGraph.card_edgeFinset_induce_compl_singleton,
      SimpleGraph.card_edgeFinset_deleteIncidenceSet]
    have hb := E.degree_le_card_edgeFinset (.inl a)
    simp only [SimpleGraph.edgeFinset_card, ← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] at hb ⊢
    omega
  simp only [SimpleGraph.edgeFinset_card, ← SimpleGraph.card_neighborSet_eq_degree,
    ← Nat.card_eq_fintype_card] at hf hv he
  change Nat.card E.edgeSet = 6*q+2 at hEC
  change Nat.card (E.neighborSet (.inl a)) = 2*q+2 at ha
  omega

lemma any_optimal_not_rigid {q : ℕ} (hq : 3 ≤ q)
    {F : SimpleGraph (Fin 3 ⊕ Fin (3*q+1))} (hF : Optimal (source q) F) :
    ¬ Rigidity.CycleRigid ((source q) \ F) := by
  intro hr
  apply any_optimal_not_evenMinimal hq hF
  apply hr.evenMinimal
  simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
    using hF.2.1

lemma any_optimal_not_cycleCritical {q : ℕ} (hq : 3 ≤ q)
    {F : SimpleGraph (Fin 3 ⊕ Fin (3*q+1))} (hF : Optimal (source q) F) :
    ¬ CycleCritical ((source q) \ F) := by
  intro hc
  obtain ⟨w,hw,hex⟩ := optimal_exact_dual (by omega) hF
  have hunit := unitWeight_of_critical_exact hw (by
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using hF.2.1) hc (by
    simp only [SimpleGraph.edgeFinset, ← Set.toFinite_toFinset] at hex ⊢
    exact hex.symm.le)
  exact any_optimal_not_rigid hq hF (hunit.rigid (by
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using hF.2.1))

/-- On this infinite family the proposed exactness property holds for every
optimal remainder, whereas cycle-criticality and rigidity fail for all of
those remainders. The source graphs themselves are globally minimal. -/
lemma family (q : ℕ) (hq : 3 ≤ q) :
    EdgeHull.Minimal (source q) ∧
    (∃ F, Best (source q) F) ∧
    ∀ F : SimpleGraph (Fin 3 ⊕ Fin (3*q+1)), Optimal (source q) F →
      Best (source q) F ∧
      ¬ EvenMinimal ((source q) \ F) ∧
      ¬ CycleCritical ((source q) \ F) ∧
      ¬ Rigidity.CycleRigid ((source q) \ F) ∧
      ∃ w : Sym2 (Fin 3 ⊕ Fin (3*q+1)) → ℝ,
        CycleUpperWeight ((source q) \ F) w ∧
        (∑ e ∈ ((source q) \ F).edgeFinset, w e) =
          (number ((source q) \ F) : ℝ) := by
  refine ⟨ThreeHubGlobalMinimal.complete_minimal q (by omega), exists_best _, ?_⟩
  intro F hF
  exact ⟨every_optimal_best (by omega) hF, any_optimal_not_evenMinimal hq hF,
    any_optimal_not_cycleCritical hq hF, any_optimal_not_rigid hq hF,
    optimal_exact_dual (by omega) hF⟩

end Erdos184Work.ThreeHubOptimalRemainders
#print axioms Erdos184Work.ThreeHubOptimalRemainders.optimal_counts
#print axioms Erdos184Work.ThreeHubOptimalRemainders.optimal_exact_dual
#print axioms Erdos184Work.ThreeHubOptimalRemainders.any_optimal_not_evenMinimal

#print axioms Erdos184Work.ThreeHubOptimalRemainders.family
