import Submission.FractionalAveraging
import Submission.CycleEnvelope

/-!
The attained exact fractional cycle optimum and its monotone envelope over
all even edge subgraphs. These parameters do not assert integral rounding.
-/
open SimpleGraph
open scoped Classical BigOperators
namespace Erdos184.FractionalEnvelope
open FractionalCycles CountCritical CycleNumberSubmodularity
variable {V : Type*} [Fintype V]
attribute [local instance] FractionalCycles.cyclePieceFintype
set_option maxHeartbeats 1000000

noncomputable def cost {G : SimpleGraph V} (t : CyclePiece G → ℝ) : ℝ := ∑ H, t H

def feasible (G : SimpleGraph V) : Set (CyclePiece G → ℝ) :=
  {t | IsFractionalPartition G t}

lemma cost_continuous (G : SimpleGraph V) : Continuous (@cost V _ G) := by
  unfold cost
  exact continuous_finset_sum _ (fun H _ => continuous_apply H)

lemma feasible_closed (G : SimpleGraph V) : IsClosed (feasible G) := by
  have hpos : IsClosed {t : CyclePiece G → ℝ | ∀ H, 0 ≤ t H} := by
    simpa only [Set.setOf_forall] using
      isClosed_iInter (fun H : CyclePiece G => isClosed_le continuous_const (continuous_apply H))
  have hcov : IsClosed {t : CyclePiece G → ℝ | ∀ e ∈ G.edgeSet,
      (∑ H : CyclePiece G, if e ∈ H.val.edgeSet then t H else 0) = 1} := by
    have hc (e : Sym2 V) : Continuous (fun t : CyclePiece G → ℝ =>
        ∑ H : CyclePiece G, if e ∈ H.val.edgeSet then t H else 0) := by
      apply continuous_finset_sum
      intro H _
      split_ifs <;> fun_prop
    simpa only [Set.setOf_forall] using
      isClosed_iInter (fun e : Sym2 V => isClosed_iInter
        (fun _ : e ∈ G.edgeSet => isClosed_eq (hc e) continuous_const))
  exact hpos.inter hcov

lemma feasible_compact (G : SimpleGraph V) : IsCompact (feasible G) := by
  apply (isCompact_Icc (a := (fun _ : CyclePiece G => (0 : ℝ)))
    (b := fun _ => 1)).of_isClosed_subset (feasible_closed G)
  intro t ht
  exact ⟨ht.1,fun H => coefficient_le_one G t ht H⟩

lemma cost_nonneg {G : SimpleGraph V} {t : CyclePiece G → ℝ}
    (ht : IsFractionalPartition G t) : 0 ≤ cost t :=
  Finset.sum_nonneg (fun H _ => ht.1 H)

lemma feasible_nonempty (G : SimpleGraph V) (he : ∀ v, Even (G.degree v)) :
    (feasible G).Nonempty := by
  obtain ⟨t,ht,_⟩ := exists_fractional_partition_linear G he
  exact ⟨t,ht⟩

noncomputable def optimum (G : SimpleGraph V) : ℝ := sInf (cost '' feasible G)

lemma cost_image_bddBelow (G : SimpleGraph V) : BddBelow (cost '' feasible G) := by
  refine ⟨0,?_⟩
  rintro x ⟨t,ht,rfl⟩
  exact cost_nonneg ht

lemma optimum_le_cost {G : SimpleGraph V} {t : CyclePiece G → ℝ}
    (ht : IsFractionalPartition G t) : optimum G ≤ cost t :=
  csInf_le (cost_image_bddBelow G) ⟨t,ht,rfl⟩

/-- Compactness supplies an actual minimizing fractional partition. -/
lemma optimum_attained (G : SimpleGraph V) (he : ∀ v, Even (G.degree v)) :
    ∃ t : CyclePiece G → ℝ, IsFractionalPartition G t ∧ cost t = optimum G := by
  have hc := (feasible_compact G).image (cost_continuous G)
  have hn : (cost '' feasible G).Nonempty := (feasible_nonempty G he).image cost
  obtain ⟨t,ht,hval⟩ := hc.sInf_mem hn
  exact ⟨t,ht,hval⟩

lemma optimum_nonneg (G : SimpleGraph V) (he : ∀ v, Even (G.degree v)) :
    0 ≤ optimum G := by
  obtain ⟨t,ht,hval⟩ := optimum_attained G he
  rw [← hval]
  exact cost_nonneg ht

lemma optimum_le_linear (G : SimpleGraph V) (he : ∀ v, Even (G.degree v)) :
    optimum G ≤ 2 * Fintype.card V := by
  obtain ⟨t,ht,hb⟩ := exists_fractional_partition_linear G he
  exact (optimum_le_cost ht).trans hb

lemma packingWeight_fractional (G : SimpleGraph V) (D : Finset G.Subgraph)
    (hc : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition G D) : IsFractionalPartition G (packingWeight G D hc) := by
  refine ⟨packingWeight_nonneg G D hc,?_⟩
  intro e he
  rw [packingWeight_coverage,decomposition_edge_sum G D hd,if_pos he]

lemma optimum_le_number (G : SimpleGraph V) (he : ∀ v, Even (G.degree v)) :
    optimum G ≤ cycleNumber G := by
  obtain ⟨D,hc,hd,hcard⟩ := minimum_exists G he
  have hh := optimum_le_cost (packingWeight_fractional G D hc hd)
  rw [cost,packingWeight_sum,hcard] at hh
  exact hh

lemma degree_le_twice_optimum (G : SimpleGraph V) (he : ∀ v, Even (G.degree v)) (v : V) :
    (G.degree v : ℝ) ≤ 2 * optimum G := by
  obtain ⟨t,ht,hval⟩ := optimum_attained G he
  simpa only [← hval,cost] using degree_lower G t ht v

lemma optimum_bot : optimum (⊥ : SimpleGraph V) = 0 := by
  have he : ∀ v, Even ((⊥ : SimpleGraph V).degree v) := by simp
  have hh := optimum_le_number (⊥ : SimpleGraph V) (by
    intro v
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using he v)
  rw [number_bot,Nat.cast_zero] at hh
  exact le_antisymm hh (optimum_nonneg _ (by
    intro v
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using he v))

lemma optimum_le_residual_add_one (G : SimpleGraph V)
    (he : ∀ v, Even (G.degree v)) (H : CyclePiece G) :
    optimum G ≤ optimum (G \ H.val.spanningCoe) + 1 := by
  have hr : ∀ v, Even ((G \ H.val.spanningCoe).degree v) := by
    intro v
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
      using residual_even he H.val H.property v
  obtain ⟨s,hs,hval⟩ := optimum_attained (G \ H.val.spanningCoe) (by
    intro v
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using hr v)
  obtain ⟨t,ht,hcost,_⟩ := extend_removed_cycle G H s hs
  have hh := optimum_le_cost ht
  change cost t = 1 + cost s at hcost
  rw [hcost,hval] at hh
  linarith

lemma evenSubgraphs_nonempty (G : SimpleGraph V) : (CycleEnvelope.evenSubgraphs G).Nonempty := by
  refine ⟨⊥,CycleEnvelope.mem_evenSubgraphs.mpr ⟨bot_le,?_⟩⟩
  intro v
  simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
  simp

noncomputable def envelope (G : SimpleGraph V) : ℝ :=
  (CycleEnvelope.evenSubgraphs G).sup' (evenSubgraphs_nonempty G) optimum

lemma optimum_le_envelope {G H : SimpleGraph V} (hle : H ≤ G)
    (he : ∀ v, Even (H.degree v)) : optimum H ≤ envelope G :=
  Finset.le_sup' optimum (CycleEnvelope.mem_evenSubgraphs.mpr ⟨hle,he⟩)

lemma envelope_le {G : SimpleGraph V} {B : ℝ}
    (h : ∀ H : SimpleGraph V, H ≤ G → (∀ v, Even (H.degree v)) → optimum H ≤ B) :
    envelope G ≤ B := by
  apply Finset.sup'_le
  intro H hH
  obtain ⟨hle,he⟩ := CycleEnvelope.mem_evenSubgraphs.mp hH
  exact h H hle he

lemma attained (G : SimpleGraph V) :
    ∃ H : SimpleGraph V, H ≤ G ∧ (∀ v, Even (H.degree v)) ∧ optimum H = envelope G := by
  obtain ⟨H,hH,hval⟩ := Finset.exists_mem_eq_sup' (evenSubgraphs_nonempty G) optimum
  obtain ⟨hle,he⟩ := CycleEnvelope.mem_evenSubgraphs.mp hH
  exact ⟨H,hle,he,hval.symm⟩

lemma envelope_nonneg (G : SimpleGraph V) : 0 ≤ envelope G := by
  have hh := optimum_le_envelope (G := G) (H := ⊥) bot_le (by
    intro v
    simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
    simp)
  simpa only [optimum_bot] using hh

lemma envelope_mono {A G : SimpleGraph V} (hle : A ≤ G) : envelope A ≤ envelope G := by
  apply envelope_le
  intro H hHA he
  exact optimum_le_envelope (hHA.trans hle) he

lemma envelope_le_linear (G : SimpleGraph V) : envelope G ≤ 2 * Fintype.card V := by
  apply envelope_le
  intro H _ he
  exact optimum_le_linear H he

lemma envelope_le_integral (G : SimpleGraph V) : envelope G ≤ CycleEnvelope.envelope G := by
  apply envelope_le
  intro H hHG he
  exact (optimum_le_number H he).trans (by exact_mod_cast CycleEnvelope.number_le_envelope hHG he)

lemma envelope_bot : envelope (⊥ : SimpleGraph V) = 0 := by
  have hh := envelope_le_integral (⊥ : SimpleGraph V)
  rw [CycleEnvelope.envelope_bot,Nat.cast_zero] at hh
  exact le_antisymm hh (envelope_nonneg _)

/-- Fractional envelope loss under one edge deletion is at most one.
No monotonicity of the fractional optimum itself is used. -/
lemma delete_edge_lipschitz (G : SimpleGraph V) (e : Sym2 V) :
    envelope G ≤ envelope (G.deleteEdges {e}) + 1 := by
  apply envelope_le
  intro H hHG heH
  by_cases he : e ∈ H.edgeSet
  · obtain ⟨D,hcD,hdD,_⟩ := minimum_exists H heH
    obtain ⟨C,hC,heC⟩ := Set.mem_iUnion₂.mp (hdD.2.symm ▸ he)
    have hr : H \ C.spanningCoe ≤ G.deleteEdges {e} := by
      apply edgeSet_subset_edgeSet.mp
      rw [edgeSet_sdiff,edgeSet_deleteEdges]
      intro f hf
      refine ⟨edgeSet_mono hHG hf.1,?_⟩
      intro hfe
      have hfe' : f = e := Set.mem_singleton_iff.mp hfe
      subst f
      exact hf.2 heC
    have hb := optimum_le_envelope hr (by
      intro v
      simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
        using residual_even heH C (hcD C hC) v)
    have hh := optimum_le_residual_add_one H heH (⟨C,hcD C hC⟩ : CyclePiece H)
    change optimum H ≤ optimum (H \ C.spanningCoe) + 1 at hh
    linarith
  · have hle : H ≤ G.deleteEdges {e} := by
      apply edgeSet_subset_edgeSet.mp
      rw [edgeSet_deleteEdges]
      intro f hf
      refine ⟨edgeSet_mono hHG hf,?_⟩
      intro hfe
      exact he ((Set.mem_singleton_iff.mp hfe) ▸ hf)
    have hh := optimum_le_envelope hle heH
    linarith

lemma delete_finset_lipschitz (G : SimpleGraph V) (S : Finset (Sym2 V)) :
    envelope G ≤ envelope (G.deleteEdges (S : Set (Sym2 V))) + S.card := by
  induction S using Finset.induction_on generalizing G with
  | empty => simp
  | @insert e S he ih =>
    have h₁ := delete_edge_lipschitz G e
    have h₂ := ih (G.deleteEdges {e})
    have hid : (G.deleteEdges {e}).deleteEdges (S : Set (Sym2 V)) =
        G.deleteEdges ((insert e S : Finset (Sym2 V)) : Set (Sym2 V)) := by
      rw [deleteEdges_deleteEdges]
      congr 1
      ext f
      simp
    rw [hid] at h₂
    rw [Finset.card_insert_of_notMem he,Nat.cast_add,Nat.cast_one]
    linarith

lemma envelope_acyclic {G : SimpleGraph V} (ha : G.IsAcyclic) : envelope G = 0 := by
  have hh := envelope_le_integral G
  rw [CycleEnvelope.envelope_acyclic ha,Nat.cast_zero] at hh
  exact le_antisymm hh (envelope_nonneg G)

/-- Every proper even restriction of an integral k-critical graph has
fractional optimum at most k-1. -/
lemma critical_proper_optimum_le {G H : SimpleGraph V} {k : ℕ}
    (hG : IsCountCritical k G) (hHG : H ≤ G) (hne : H ≠ G)
    (heH : ∀ v, Even (H.degree v)) : optimum H ≤ (k : ℝ) - 1 := by
  have hlo := hG.2.2 H hHG hne heH
  have hcast : (cycleNumber H : ℝ) + 1 ≤ k := by exact_mod_cast hlo
  exact (optimum_le_number H heH).trans (by linarith)

/-- Above the proper-restriction threshold, the envelope is attained at the
whole critical graph, not at an unspecified subgraph. -/
lemma critical_optimum_eq_of_envelope_gt {G : SimpleGraph V} {k : ℕ}
    (hG : IsCountCritical k G) (hgt : (k : ℝ) - 1 < envelope G) :
    optimum G = envelope G := by
  obtain ⟨H,hHG,heH,hval⟩ := attained G
  by_cases h : H = G
  · simpa [h] using hval
  · have hh := critical_proper_optimum_le hG hHG h heH
    rw [hval] at hh
    linarith

/-- Equality of fractional and integral envelopes on a critical graph would
force invariant partition count. Equality is NOT asserted in general. -/
lemma invariant_of_critical_envelope_eq {G : SimpleGraph V} {k : ℕ}
    (hG : IsCountCritical k G) (heq : envelope G = k) :
    InvariantPartitions.HasInvariantCount G := by
  have hopt : optimum G = k := by
    rw [critical_optimum_eq_of_envelope_gt hG (by rw [heq]; linarith),heq]
  apply invariant_of_countCritical_fractionalExact G k hG
  intro t ht
  have hh := optimum_le_cost ht
  rw [hopt] at hh
  exact hh

end Erdos184.FractionalEnvelope
