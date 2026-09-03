import Submission.LowCountMean

/-!
Exact uniform-mean identities under invariant integral partition count.
The equivalences below do not assert fractional exactness of that class,
and do not settle Erdos 184.
-/
open SimpleGraph
open scoped Classical BigOperators
namespace Erdos184.InvariantMean
open CountCritical CycleNumberSubmodularity FractionalEnvelope UniformEvenMean
set_option maxHeartbeats 1000000

lemma combine_pure_decompositions_exact {V : Type*} [Fintype V] {G A B : SimpleGraph V}
    (hA : A ≤ G) (hB : B ≤ G)
    (hab : Disjoint A.edgeSet B.edgeSet) (hcover : A.edgeSet ∪ B.edgeSet = G.edgeSet)
    (DA : Finset A.Subgraph) (DB : Finset B.Subgraph)
    (hca : ∀ H ∈ DA, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) (hcb : ∀ H ∈ DB, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hda : IsDecomposition A DA) (hdb : IsDecomposition B DB) :
    ∃ D : Finset G.Subgraph,
      (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧ IsDecomposition G D ∧ D.card = DA.card + DB.card := by
  let D := DA.image (promote hA) ∪ DB.image (promote hB)
  refine ⟨D, ?_, ⟨?_, ?_⟩, ?_⟩
  · intro H hH
    rcases Finset.mem_union.mp hH with hH | hH
    · obtain ⟨K, hK, rfl⟩ := Finset.mem_image.mp hH
      refine ⟨(hca K hK).1,?_⟩
      intro v
      simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using (hca K hK).2 v
    · obtain ⟨K, hK, rfl⟩ := Finset.mem_image.mp hH
      refine ⟨(hcb K hK).1,?_⟩
      intro v
      simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using (hcb K hK).2 v
  · intro H hH K hK hne
    rcases Finset.mem_union.mp hH with hH | hH <;>
      rcases Finset.mem_union.mp hK with hK | hK
    · obtain ⟨X, hX, rfl⟩ := Finset.mem_image.mp hH
      obtain ⟨Y, hY, rfl⟩ := Finset.mem_image.mp hK
      exact hda.1 hX hY (fun h => hne (congrArg (promote hA) h))
    · obtain ⟨X, hX, rfl⟩ := Finset.mem_image.mp hH
      obtain ⟨Y, hY, rfl⟩ := Finset.mem_image.mp hK
      exact hab.mono X.edgeSet_subset Y.edgeSet_subset
    · obtain ⟨X, hX, rfl⟩ := Finset.mem_image.mp hH
      obtain ⟨Y, hY, rfl⟩ := Finset.mem_image.mp hK
      exact hab.symm.mono X.edgeSet_subset Y.edgeSet_subset
    · obtain ⟨X, hX, rfl⟩ := Finset.mem_image.mp hH
      obtain ⟨Y, hY, rfl⟩ := Finset.mem_image.mp hK
      exact hdb.1 hX hY (fun h => hne (congrArg (promote hB) h))
  · ext e
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨H, _, he⟩
      exact H.edgeSet_subset he
    · intro he
      rw [← hcover] at he
      rcases he with he | he
      · rw [← hda.2] at he
        simp only [Set.mem_iUnion] at he
        obtain ⟨H, hH, he⟩ := he
        exact ⟨promote hA H, Finset.mem_union_left _ (Finset.mem_image.mpr ⟨H, hH, rfl⟩), he⟩
      · rw [← hdb.2] at he
        simp only [Set.mem_iUnion] at he
        obtain ⟨H, hH, he⟩ := he
        exact ⟨promote hB H, Finset.mem_union_right _ (Finset.mem_image.mpr ⟨H, hH, rfl⟩), he⟩
  · have hdis : Disjoint (DA.image (promote hA)) (DB.image (promote hB)) := by
      apply Finset.disjoint_left.mpr
      intro H hHA hHB
      obtain ⟨X,hX,hXH⟩ := Finset.mem_image.mp hHA
      obtain ⟨Y,hY,hYH⟩ := Finset.mem_image.mp hHB
      obtain ⟨e,he⟩ := cycle_edgeSet_nonempty X (hca X hX).1 (hca X hX).2
      have he' : e ∈ Y.edgeSet := by
        have hh : (promote hA X).edgeSet = (promote hB Y).edgeSet :=
          congrArg (fun K : G.Subgraph => K.edgeSet) (hXH.trans hYH.symm)
        exact hh ▸ he
      exact Set.disjoint_left.mp hab (X.edgeSet_subset he) (Y.edgeSet_subset he')
    dsimp only [D]
    rw [Finset.card_union_of_disjoint hdis,
      Finset.card_image_of_injective _ (InvariantPartitions.promote_injective hA),
      Finset.card_image_of_injective _ (InvariantPartitions.promote_injective hB)]

variable {V : Type*} [Fintype V]

lemma number_complement_add {G : SimpleGraph V}
    (he : ∀ v, Even (G.degree v)) (hi : InvariantPartitions.HasInvariantCount G)
    (H : SimpleGraph V) (hH : H ∈ CycleEnvelope.evenSubgraphs G) :
    cycleNumber H + cycleNumber (G \ H) = cycleNumber G := by
  obtain ⟨hle,heH⟩ := CycleEnvelope.mem_evenSubgraphs.mp hH
  have heR := (CycleEnvelope.mem_evenSubgraphs.mp (complement_mem he hH)).2
  obtain ⟨D,hcD,hdD,hcardD⟩ := minimum_exists H heH
  obtain ⟨E,hcE,hdE,hcardE⟩ := minimum_exists (G \ H) heR
  have hdis : Disjoint H.edgeSet (G \ H).edgeSet := by
    rw [edgeSet_sdiff]
    exact Set.disjoint_sdiff_right
  have hcov : H.edgeSet ∪ (G \ H).edgeSet = G.edgeSet := by
    rw [edgeSet_sdiff]
    exact Set.union_diff_cancel (edgeSet_mono hle)
  obtain ⟨P,hcP,hdP,hcardP⟩ := combine_pure_decompositions_exact hle sdiff_le hdis hcov
    D E hcD hcE hdD hdE
  obtain ⟨Q,hcQ,hdQ,hcardQ⟩ := minimum_exists G he
  have hh := hi P Q hcP hdP hcQ hdQ
  rwa [hcardP,hcardD,hcardE,hcardQ] at hh

lemma twice_integral_mean {G : SimpleGraph V}
    (he : ∀ v, Even (G.degree v)) (hi : InvariantPartitions.HasInvariantCount G) :
    2 * mean G (fun H => (cycleNumber H : ℝ)) = cycleNumber G := by
  have hs : (∑ H ∈ CycleEnvelope.evenSubgraphs G,
      ((cycleNumber H : ℝ) + cycleNumber (G \ H))) =
      ∑ _H ∈ CycleEnvelope.evenSubgraphs G, (cycleNumber G : ℝ) := by
    apply Finset.sum_congr rfl
    intro H hH
    exact_mod_cast number_complement_add he hi H hH
  rw [Finset.sum_add_distrib,sum_complement G he (fun H => (cycleNumber H : ℝ))] at hs
  simp only [Finset.sum_const,nsmul_eq_mul] at hs
  have hp : (0 : ℝ) < (CycleEnvelope.evenSubgraphs G).card := by
    exact_mod_cast card_pos G
  unfold mean
  rw [← mul_div_assoc]
  apply (div_eq_iff hp.ne').mpr
  linarith

lemma twice_fractional_mean_le {G : SimpleGraph V}
    (he : ∀ v, Even (G.degree v)) (hi : InvariantPartitions.HasInvariantCount G) :
    2 * fractionalMean G ≤ cycleNumber G := by
  have hh := fractionalMean_le_integralMean G
  rw [← twice_integral_mean he hi]
  linarith

lemma means_equal_iff_exact_restrictions (G : SimpleGraph V) :
    fractionalMean G = mean G (fun H => (cycleNumber H : ℝ)) ↔
      ∀ H ∈ CycleEnvelope.evenSubgraphs G, optimum H = (cycleNumber H : ℝ) := by
  have hp : (0 : ℝ) < (CycleEnvelope.evenSubgraphs G).card := by
    exact_mod_cast card_pos G
  have hle : ∀ H ∈ CycleEnvelope.evenSubgraphs G,
      optimum H ≤ (cycleNumber H : ℝ) := by
    intro H hH
    exact optimum_le_number H (CycleEnvelope.mem_evenSubgraphs.mp hH).2
  unfold fractionalMean mean
  rw [div_left_inj' hp.ne']
  exact Finset.sum_eq_sum_iff_of_le hle

lemma exact_restrictions_of_exact {G : SimpleGraph V}
    (he : ∀ v, Even (G.degree v)) (hi : InvariantPartitions.HasInvariantCount G)
    (hx : optimum G = (cycleNumber G : ℝ)) :
    ∀ H ∈ CycleEnvelope.evenSubgraphs G, optimum H = (cycleNumber H : ℝ) := by
  intro H hH
  have hHe := (CycleEnvelope.mem_evenSubgraphs.mp hH).2
  have hRe := (CycleEnvelope.mem_evenSubgraphs.mp (complement_mem he hH)).2
  have hnum : (cycleNumber H : ℝ) + cycleNumber (G \ H) = cycleNumber G := by
    exact_mod_cast number_complement_add he hi H hH
  have hsum := optimum_le_complement_sum G he H hH
  have hHle := optimum_le_number H hHe
  have hRle := optimum_le_number (G \ H) hRe
  rw [hx] at hsum
  linarith

/-- Equality in the invariant-class fractional mean is equivalent to own
fractional exactness. Neither side is assumed to hold for every invariant graph. -/
lemma twice_fractional_mean_eq_iff_exact {G : SimpleGraph V}
    (he : ∀ v, Even (G.degree v)) (hi : InvariantPartitions.HasInvariantCount G) :
    2 * fractionalMean G = (cycleNumber G : ℝ) ↔
      optimum G = (cycleNumber G : ℝ) := by
  constructor
  · intro h
    have hm : fractionalMean G = mean G (fun H => (cycleNumber H : ℝ)) := by
      have hh := twice_integral_mean he hi
      linarith
    exact (means_equal_iff_exact_restrictions G).mp hm G
      (CycleEnvelope.mem_evenSubgraphs.mpr ⟨le_rfl,he⟩)
  · intro hx
    have hm := (means_equal_iff_exact_restrictions G).mpr (exact_restrictions_of_exact he hi hx)
    rw [hm]
    exact twice_integral_mean he hi

/-- Thus a coefficient-two LOWER bound is not an easier invariant-class
substitute for fractional exactness: it is equivalent to that assertion. -/
lemma coefficient_two_iff_exact {G : SimpleGraph V}
    (he : ∀ v, Even (G.degree v)) (hi : InvariantPartitions.HasInvariantCount G) :
    (cycleNumber G : ℝ) ≤ 2 * fractionalMean G ↔
      optimum G = (cycleNumber G : ℝ) := by
  constructor
  · intro hh
    exact (twice_fractional_mean_eq_iff_exact he hi).mp
      (le_antisymm (twice_fractional_mean_le he hi) hh)
  · intro hh
    exact ((twice_fractional_mean_eq_iff_exact he hi).mpr hh).ge

lemma strict_deficit_iff_inexact {G : SimpleGraph V}
    (he : ∀ v, Even (G.degree v)) (hi : InvariantPartitions.HasInvariantCount G) :
    2 * fractionalMean G < (cycleNumber G : ℝ) ↔
      optimum G < (cycleNumber G : ℝ) := by
  have hle := twice_fractional_mean_le he hi
  have hxle := optimum_le_number G he
  have hh := twice_fractional_mean_eq_iff_exact he hi
  constructor
  · intro hm
    by_contra! hn
    have hx := le_antisymm hxle hn
    have heq := hh.mpr hx
    linarith
  · intro hx
    by_contra! hn
    have hm := le_antisymm hle hn
    have heq := hh.mp hm
    linarith

lemma count_le_two_mean_eq {G : SimpleGraph V} {k : ℕ}
    (hG : IsCountCritical k G) (hk : k ≤ 2) : 2 * fractionalMean G = k := by
  have hi := LowCountCritical.invariant_of_count_le_two hG hk
  have hx := LowCountCritical.optimum_eq_number_of_number_le_two hG.1
    (by rw [hG.2.1]; exact hk)
  simpa only [hG.2.1] using (twice_fractional_mean_eq_iff_exact hG.1 hi).mpr hx

end Erdos184.InvariantMean
