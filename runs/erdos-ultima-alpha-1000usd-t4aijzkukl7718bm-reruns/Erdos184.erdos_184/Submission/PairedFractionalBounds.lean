import Submission.PairedFractionalEnvelope
import Submission.EvenCycleFactorization

/-!
Unconditional restricted comparisons for the paired fractional maximum.
They cover maximum degree four, minimum count at most five, and degree slack
at most two. No uniform high-count comparison is asserted.
-/
open SimpleGraph
open scoped Classical BigOperators
namespace Erdos184.PairedFractionalEnvelope
open CountCritical CycleNumberSubmodularity FractionalEnvelope UniformEvenMean
variable {V : Type*} [Fintype V]
set_option maxHeartbeats 1000000

lemma envelope_le_paired {G : SimpleGraph V} (he : ∀ v, Even (G.degree v)) :
    FractionalEnvelope.envelope G ≤ paired G := by
  obtain ⟨H,hHG,heH,hval⟩ := FractionalEnvelope.attained G
  have hH := CycleEnvelope.mem_evenSubgraphs.mpr ⟨hHG,heH⟩
  have hr := (CycleEnvelope.mem_evenSubgraphs.mp (complement_mem he hH)).2
  have hn := optimum_nonneg (G \ H) hr
  have hh := split_le_paired hH
  rw [hval] at hh
  linarith

lemma number_le_paired_of_exact_split {G A B : SimpleGraph V}
    (hcover : A.edgeSet ∪ B.edgeSet = G.edgeSet)
    (hdis : Disjoint A.edgeSet B.edgeSet)
    (heA : ∀ v, Even (A.degree v)) (heB : ∀ v, Even (B.degree v))
    (hxA : optimum A = (cycleNumber A : ℝ))
    (hxB : optimum B = (cycleNumber B : ℝ)) :
    (cycleNumber G : ℝ) ≤ paired G := by
  have hAG : A ≤ G := edgeSet_subset_edgeSet.mp (by
    rw [← hcover]
    exact Set.subset_union_left)
  have hB : B = G \ A := by
    apply edgeSet_injective
    rw [edgeSet_sdiff,← hcover]
    ext e
    constructor
    · intro hb
      exact ⟨Or.inr hb,fun ha => Set.disjoint_left.mp hdis ha hb⟩
    · rintro ⟨ha | hb,hn⟩
      · exact (hn ha).elim
      · exact hb
  have hn : (cycleNumber G : ℝ) ≤ (cycleNumber A : ℝ) + cycleNumber B := by
    exact_mod_cast CycleFactors.number_le_add hcover hdis heA heB
  rw [← hxA,← hxB,hB] at hn
  exact hn.trans (split_le_paired (CycleEnvelope.mem_evenSubgraphs.mpr ⟨hAG,heA⟩))

/-- The two cycle factors need not jointly minimize the cycle count. Their
fractional exactness and integral subadditivity suffice for the comparison. -/
lemma number_le_paired_of_degree_le_four {G : SimpleGraph V}
    (he : ∀ v, Even (G.degree v)) (hd : ∀ v, G.degree v ≤ 4) :
    (cycleNumber G : ℝ) ≤ paired G := by
  obtain ⟨A,B,hA,hB,hdis,hcov⟩ := EvenCycleFactorization.exists_two_factors G he hd
  exact number_le_paired_of_exact_split hcov hdis
    (CycleFactors.cycles_even hA) (CycleFactors.cycles_even hB)
    (CycleFactors.optimum_eq_number hA) (CycleFactors.optimum_eq_number hB)

/-- At a vertex with degree slack at most two, the star of an optimum and
its complementary family are both fractionally exact. -/
lemma exists_split_of_small_degree_slack {G : SimpleGraph V}
    (he : ∀ v, Even (G.degree v)) (v : V)
    (hslack : 2 * cycleNumber G ≤ G.degree v + 4) :
    ∃ H : SimpleGraph V, H ∈ CycleEnvelope.evenSubgraphs G ∧
      optimum H + optimum (G \ H) = (cycleNumber G : ℝ) := by
  obtain ⟨D,hc,hd,hcard⟩ := minimum_exists G he
  let S := StarElimination.star D v
  have hSD : S ⊆ D := StarElimination.star_subset D v
  have hcS : ∀ H ∈ S, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2 :=
    fun H hH => hc H (hSD hH)
  have hdS : Set.PairwiseDisjoint (S : Set G.Subgraph) (fun H => H.edgeSet) :=
    fun _ hH _ hK hne => hd.1 (hSD hH) (hSD hK) hne
  have hcost := SmallSlackExact.split_of_small_slack D hc hd v (by omega)
  change optimum (unionPieces G S) = (S.card : ℝ) ∧
    optimum (unionPieces G (D \ S)) = ((D \ S).card : ℝ) at hcost
  refine ⟨unionPieces G S,CycleEnvelope.mem_evenSubgraphs.mpr
    ⟨unionPieces_le G S,SmallSlackExact.union_even S hcS hdS⟩,?_⟩
  rw [← LowCountMean.union_complement D S hd hSD,hcost.1,hcost.2]
  have hh := Finset.card_sdiff_add_card_eq_card hSD
  have hh' : S.card + (D \ S).card = cycleNumber G := by omega
  exact_mod_cast hh'

lemma number_le_paired_of_small_degree_slack {G : SimpleGraph V}
    (he : ∀ v, Even (G.degree v)) (v : V)
    (hslack : 2 * cycleNumber G ≤ G.degree v + 4) :
    (cycleNumber G : ℝ) ≤ paired G := by
  obtain ⟨H,hH,hh⟩ := exists_split_of_small_degree_slack he v hslack
  rw [← hh]
  exact split_le_paired hH

/-- At count five, either maximum degree is at most four, or a degree-six
vertex has degree slack at most two. This does not require criticality. -/
lemma number_le_paired_of_number_le_five {G : SimpleGraph V}
    (he : ∀ v, Even (G.degree v)) (hk : cycleNumber G ≤ 5) :
    (cycleNumber G : ℝ) ≤ paired G := by
  by_cases hd : ∀ v, G.degree v ≤ 4
  · exact number_le_paired_of_degree_le_four he hd
  push_neg at hd
  obtain ⟨v,hv⟩ := hd
  obtain ⟨d,hd⟩ := he v
  exact number_le_paired_of_small_degree_slack he v (by omega)

lemma bad_count_at_least_six {G : SimpleGraph V}
    (he : ∀ v, Even (G.degree v)) (hbad : paired G < (cycleNumber G : ℝ)) :
    6 ≤ cycleNumber G := by
  by_contra! hh
  have hk : cycleNumber G ≤ 5 := by omega
  exact (not_lt_of_ge (number_le_paired_of_number_le_five he hk)) hbad

/-- A failure must have at least three optimum pieces avoiding every vertex.
Evenness strengthens the strict degree-slack inequality to this integer bound. -/
lemma degree_bound_of_bad {G : SimpleGraph V}
    (he : ∀ v, Even (G.degree v)) (hbad : paired G < (cycleNumber G : ℝ))
    (v : V) : G.degree v + 6 ≤ 2 * cycleNumber G := by
  have hn : ¬ 2 * cycleNumber G ≤ G.degree v + 4 := by
    intro hh
    exact (not_lt_of_ge (number_le_paired_of_small_degree_slack he v hh)) hbad
  obtain ⟨d,hd⟩ := he v
  omega

lemma bad_has_degree_above_four {G : SimpleGraph V}
    (he : ∀ v, Even (G.degree v)) (hbad : paired G < (cycleNumber G : ℝ)) :
    ∃ v, 4 < G.degree v := by
  by_contra! hd
  exact (not_lt_of_ge (number_le_paired_of_degree_le_four he hd)) hbad

lemma bad_at_six_maximum_degree_six {G : SimpleGraph V}
    (he : ∀ v, Even (G.degree v)) (hk : cycleNumber G = 6)
    (hbad : paired G < (cycleNumber G : ℝ)) :
    (∀ v, G.degree v ≤ 6) ∧ ∃ v, G.degree v = 6 := by
  have hd (v : V) := degree_bound_of_bad he hbad v
  constructor
  · intro v
    have := hd v
    omega
  · obtain ⟨v,hv⟩ := bad_has_degree_above_four he hbad
    obtain ⟨d,hde⟩ := he v
    have := hd v
    exact ⟨v,by omega⟩

end Erdos184.PairedFractionalEnvelope
