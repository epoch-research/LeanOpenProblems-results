import Submission.InvariantMean
import Submission.RootedEnvelopeProfiles

/-!
The maximum sum of fractional costs of two complementary even restrictions.
The low-count split theorem below is unconditional. The comparison needed
for arbitrary count-critical graphs is only a hypothesis of the reduction.
This file does not settle Erdős 184.
-/
open SimpleGraph
open scoped Classical BigOperators
namespace Erdos184.PairedFractionalEnvelope
open CountCritical CycleNumberSubmodularity FractionalEnvelope UniformEvenMean
variable {V : Type*} [Fintype V]
set_option maxHeartbeats 1000000

noncomputable def paired (G : SimpleGraph V) : ℝ :=
  (CycleEnvelope.evenSubgraphs G).sup' (evenSubgraphs_nonempty G)
    (fun H => optimum H + optimum (G \ H))

lemma split_le_paired {G H : SimpleGraph V}
    (hH : H ∈ CycleEnvelope.evenSubgraphs G) :
    optimum H + optimum (G \ H) ≤ paired G :=
  Finset.le_sup' (fun H => optimum H + optimum (G \ H)) hH

lemma paired_le {G : SimpleGraph V} {b : ℝ}
    (h : ∀ H ∈ CycleEnvelope.evenSubgraphs G,
      optimum H + optimum (G \ H) ≤ b) : paired G ≤ b := by
  apply Finset.sup'_le
  exact h

lemma attained (G : SimpleGraph V) :
    ∃ H : SimpleGraph V, H ∈ CycleEnvelope.evenSubgraphs G ∧
      optimum H + optimum (G \ H) = paired G := by
  obtain ⟨H,hH,hh⟩ := Finset.exists_mem_eq_sup' (evenSubgraphs_nonempty G)
    (fun H => optimum H + optimum (G \ H))
  exact ⟨H,hH,hh.symm⟩

lemma paired_le_twice_envelope {G : SimpleGraph V} (he : ∀ v, Even (G.degree v)) :
    paired G ≤ 2 * FractionalEnvelope.envelope G := by
  apply paired_le
  intro H hH
  have hR := complement_mem he hH
  have h₁ := optimum_le_envelope (CycleEnvelope.mem_evenSubgraphs.mp hH).1
    (CycleEnvelope.mem_evenSubgraphs.mp hH).2
  have h₂ := optimum_le_envelope (CycleEnvelope.mem_evenSubgraphs.mp hR).1
    (CycleEnvelope.mem_evenSubgraphs.mp hR).2
  linarith

/-- Complementary parts use the marked edge on exactly one side. The
sum of the two rooted envelopes therefore bounds the paired maximum. -/
lemma paired_le_rooted_sum {G : SimpleGraph V} (he : ∀ v, Even (G.degree v))
    (e : Sym2 V) (heG : e ∈ G.edgeSet) :
    paired G ≤ FractionalEnvelope.envelope (G.deleteEdges {e}) +
      RootedEnvelopeProfiles.through G e := by
  have avoiding (A : SimpleGraph V) (hAG : A ≤ G)
      (heA : ∀ v, Even (A.degree v)) (hea : e ∉ A.edgeSet) :
      optimum A ≤ FractionalEnvelope.envelope (G.deleteEdges {e}) := by
    apply optimum_le_envelope _ heA
    apply edgeSet_subset_edgeSet.mp
    rw [edgeSet_deleteEdges]
    intro f hf
    refine ⟨edgeSet_mono hAG hf,?_⟩
    intro hh
    exact hea ((Set.mem_singleton_iff.mp hh) ▸ hf)
  apply paired_le
  intro H hH
  obtain ⟨hHG,heH⟩ := CycleEnvelope.mem_evenSubgraphs.mp hH
  have heR := (CycleEnvelope.mem_evenSubgraphs.mp (complement_mem he hH)).2
  by_cases hm : e ∈ H.edgeSet
  · have h₁ := RootedEnvelopeProfiles.optimum_le_through hHG heH hm
    have h₂ := avoiding (G \ H) sdiff_le heR (by
      rw [edgeSet_sdiff]
      exact fun hh => hh.2 hm)
    linarith
  · have h₁ := avoiding H hHG heH hm
    have h₂ := RootedEnvelopeProfiles.optimum_le_through
      (show G \ H ≤ G from sdiff_le) heR (by
        rw [edgeSet_sdiff]
        exact ⟨heG,hm⟩)
    linarith

lemma paired_le_linear {G : SimpleGraph V} (he : ∀ v, Even (G.degree v)) :
    paired G ≤ 4 * Fintype.card V := by
  have h₁ := paired_le_twice_envelope he
  have h₂ := envelope_le_linear G
  linarith

lemma optimum_le_paired (G : SimpleGraph V) : optimum G ≤ paired G := by
  have hH : (⊥ : SimpleGraph V) ∈ CycleEnvelope.evenSubgraphs G := by
    apply CycleEnvelope.mem_evenSubgraphs.mpr
    refine ⟨bot_le,?_⟩
    intro v
    simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
    simp
  have hh := split_le_paired hH
  simpa only [optimum_bot,sdiff_bot,zero_add] using hh

lemma twice_mean_le_paired {G : SimpleGraph V} (he : ∀ v, Even (G.degree v)) :
    2 * fractionalMean G ≤ paired G := by
  have hh := mean_le G (fun H => optimum H + optimum (G \ H)) (paired G)
    (fun _ hH => split_le_paired hH)
  unfold mean at hh
  rw [Finset.sum_add_distrib,sum_complement G he optimum] at hh
  unfold fractionalMean mean
  rw [add_div] at hh
  linarith

/-- At most four pieces can be divided into two families of at most two.
Both unions have exactly their family cardinality as fractional optimum. -/
lemma split_of_partition_card_le_four {G : SimpleGraph V}
    (D : Finset G.Subgraph)
    (hc : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition G D) (hk : D.card ≤ 4) :
    ∃ H : SimpleGraph V, H ∈ CycleEnvelope.evenSubgraphs G ∧
      optimum H + optimum (G \ H) = (D.card : ℝ) := by
  obtain ⟨S,hSD,hS⟩ := Finset.exists_subset_card_eq (show min 2 D.card ≤ D.card from min_le_right _ _)
  have hcard : (D \ S).card + S.card = D.card :=
    Finset.card_sdiff_add_card_eq_card hSD
  have hs2 : S.card ≤ 2 := by omega
  have ht2 : (D \ S).card ≤ 2 := by omega
  have hcS : ∀ H ∈ S, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2 :=
    fun H hH => hc H (hSD hH)
  have hdS : Set.PairwiseDisjoint (S : Set G.Subgraph) (fun H => H.edgeSet) :=
    fun _ hH _ hK hne => hd.1 (hSD hH) (hSD hK) hne
  have hcT : ∀ H ∈ D \ S, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2 :=
    fun H hH => hc H (Finset.mem_sdiff.mp hH).1
  have hdT : Set.PairwiseDisjoint ((D \ S : Finset G.Subgraph) : Set G.Subgraph)
      (fun H => H.edgeSet) := fun _ hH _ hK hne =>
    hd.1 (Finset.mem_sdiff.mp hH).1 (Finset.mem_sdiff.mp hK).1 hne
  refine ⟨unionPieces G S,CycleEnvelope.mem_evenSubgraphs.mpr
    ⟨unionPieces_le G S,SmallSlackExact.union_even S hcS hdS⟩,?_⟩
  rw [← LowCountMean.union_complement D S hd hSD,
    SmallSlackExact.at_most_two_exact S hcS hdS hs2,
    SmallSlackExact.at_most_two_exact (D \ S) hcT hdT ht2]
  exact_mod_cast hcard.symm ▸ (Nat.add_comm S.card (D \ S).card)

lemma exists_split_of_number_le_four {G : SimpleGraph V}
    (he : ∀ v, Even (G.degree v)) (hk : cycleNumber G ≤ 4) :
    ∃ H : SimpleGraph V, H ∈ CycleEnvelope.evenSubgraphs G ∧
      optimum H + optimum (G \ H) = (cycleNumber G : ℝ) := by
  obtain ⟨D,hc,hd,hcard⟩ := minimum_exists G he
  simpa only [hcard] using split_of_partition_card_le_four D hc hd (by omega)

lemma number_le_paired_of_number_le_four {G : SimpleGraph V}
    (he : ∀ v, Even (G.degree v)) (hk : cycleNumber G ≤ 4) :
    (cycleNumber G : ℝ) ≤ paired G := by
  obtain ⟨H,hH,hh⟩ := exists_split_of_number_le_four he hk
  rw [← hh]
  exact split_le_paired hH

lemma rooted_comparison_of_number_le_four {G : SimpleGraph V}
    (he : ∀ v, Even (G.degree v)) (hk : cycleNumber G ≤ 4)
    (e : Sym2 V) (heG : e ∈ G.edgeSet) :
    (cycleNumber G : ℝ) ≤ FractionalEnvelope.envelope (G.deleteEdges {e}) +
      RootedEnvelopeProfiles.through G e :=
  (number_le_paired_of_number_le_four he hk).trans (paired_le_rooted_sum he e heG)

lemma paired_le_number_of_invariant {G : SimpleGraph V}
    (he : ∀ v, Even (G.degree v)) (hi : InvariantPartitions.HasInvariantCount G) :
    paired G ≤ (cycleNumber G : ℝ) := by
  apply paired_le
  intro H hH
  have hr := complement_mem he hH
  have h₁ := optimum_le_number H (CycleEnvelope.mem_evenSubgraphs.mp hH).2
  have h₂ := optimum_le_number (G \ H) (CycleEnvelope.mem_evenSubgraphs.mp hr).2
  have hsum : (cycleNumber H : ℝ) + cycleNumber (G \ H) = cycleNumber G := by
    exact_mod_cast InvariantMean.number_complement_add he hi H hH
  linarith

/-- In the invariant class, attaining the integral count is equivalent to
having a complementary split with both sides fractionally exact. This
statement does not assert the existence of such a split in general. -/
lemma paired_eq_number_iff_exact_split {G : SimpleGraph V}
    (he : ∀ v, Even (G.degree v)) (hi : InvariantPartitions.HasInvariantCount G) :
    paired G = (cycleNumber G : ℝ) ↔
      ∃ H : SimpleGraph V, H ∈ CycleEnvelope.evenSubgraphs G ∧
        optimum H = (cycleNumber H : ℝ) ∧
        optimum (G \ H) = (cycleNumber (G \ H) : ℝ) := by
  constructor
  · intro hh
    obtain ⟨H,hH,hval⟩ := attained G
    have hr := complement_mem he hH
    have h₁ := optimum_le_number H (CycleEnvelope.mem_evenSubgraphs.mp hH).2
    have h₂ := optimum_le_number (G \ H) (CycleEnvelope.mem_evenSubgraphs.mp hr).2
    have hsum : (cycleNumber H : ℝ) + cycleNumber (G \ H) = cycleNumber G := by
      exact_mod_cast InvariantMean.number_complement_add he hi H hH
    refine ⟨H,hH,?_,?_⟩ <;> linarith
  · rintro ⟨H,hH,h₁,h₂⟩
    apply le_antisymm (paired_le_number_of_invariant he hi)
    have hh := split_le_paired hH
    rw [h₁,h₂] at hh
    have hsum : (cycleNumber H : ℝ) + cycleNumber (G \ H) = cycleNumber G := by
      exact_mod_cast InvariantMean.number_complement_add he hi H hH
    rwa [hsum] at hh

universe u
/-- A uniform comparison on critical graphs would settle the original
conjecture. The comparison is an explicit unproved premise, not a result. -/
lemma conjecture_of_critical_paired_comparison (K : ℝ) (hK : 0 ≤ K)
    (hcomp : ∀ {V : Type u} [Fintype V] (G : SimpleGraph V) (k : ℕ),
      IsCountCritical k G → (k : ℝ) ≤ K * paired G) :
    ∃ f : ℕ → ℝ,
      (f =O[Filter.atTop] fun n : ℕ => (n : ℝ)) ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      ∃ D : Finset G.Subgraph,
        (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition G D ∧
        (D.card : ℝ) ≤ f (Fintype.card V) := by
  apply conjecture_iff_even_bound.mpr
  refine ⟨4*K,?_⟩
  intro V _ _ G he
  obtain ⟨D,hc,hd,hcard⟩ := bound_of_critical_subgraph_bound G he
    ((4*K)*Fintype.card V) (by positivity) (by
      intro H _ k hk
      have hl := hcomp H k hk
      have hu := mul_le_mul_of_nonneg_left (paired_le_linear hk.1) hK
      nlinarith)
  refine ⟨D,?_,hd,hcard⟩
  intro H hH
  apply Or.inl
  refine ⟨(hc H hH).1,?_⟩
  intro v
  simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using (hc H hH).2 v

end Erdos184.PairedFractionalEnvelope
