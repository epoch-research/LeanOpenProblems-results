import Submission.MixedSevenWalks
import Submission.MixedSevenFractional
import Submission.MixedSevenData

/-! The seven-vertex split graph is itself mixed-count-critical. This is
an auxiliary finite obstruction, not a counterexample to Erdős 184. -/
open SimpleGraph
open scoped Classical
namespace Erdos184.MixedSevenCriticalDev
open MixedCritical MixedCriticalNonforest MixedSevenFinite MixedSevenWalks
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

noncomputable def indices (H : SimpleGraph V) : Finset E :=
  Finset.univ.filter (fun e => MixedSevenWalks.edge e ∈ H.edgeSet)

lemma mem_indices (H : SimpleGraph V) (e : E) :
    e ∈ indices H ↔ MixedSevenWalks.edge e ∈ H.edgeSet := by simp [indices]

lemma indices_edges (H : SimpleGraph V) (hHG : H ≤ G) :
    H.edgeSet = ((indices H).image MixedSevenWalks.edge : Set (Sym2 V)) := by
  ext e
  constructor
  · intro he
    induction e using Sym2.ind with
    | h u v =>
      obtain ⟨a,ha⟩ := edge_surjective u v (hHG he)
      exact Finset.mem_image.mpr ⟨a,(mem_indices H a).mpr (ha.symm ▸ he),ha⟩
  · intro he
    change e ∈ (indices H).image MixedSevenWalks.edge at he
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp he
    exact (mem_indices H a).mp ha

lemma indices_proper (H : SimpleGraph V) (hHG : H ≤ G) (hne : H ≠ G) :
    indices H ≠ Finset.univ := by
  intro hi
  apply hne
  apply le_antisymm hHG
  intro u v huv
  obtain ⟨e,he⟩ := edge_surjective u v huv
  have hm : e ∈ indices H := hi.symm ▸ Finset.mem_univ _
  have hh := (mem_indices H e).mp hm
  change s(u,v) ∈ H.edgeSet
  rwa [← he]

lemma indices_card (H : SimpleGraph V) (hHG : H ≤ G) :
    H.edgeSet.ncard = (indices H).card := by
  rw [indices_edges H hHG,Set.ncard_coe_finset,Finset.card_image_of_injective _ edge_injective]

lemma cyc_card_pos : ∀ i, 1 ≤ (cyc i).card := by decide

variable (certificate : ∀ S : Finset E, S ≠ Finset.univ → Valid S)
include certificate

lemma proper_number_le (H : SimpleGraph V) (hHG : H ≤ G) (hne : H ≠ G) :
    number H ≤ 6 := by
  let S := indices H
  let P := pack S
  have hcert := certificate S (indices_proper H hHG hne)
  rcases hcert with ⟨hsub,hdis,hcost⟩
  let T := P.biUnion cyc
  have hTS : T ⊆ S := by
    intro e he
    obtain ⟨i,hi,he⟩ := Finset.mem_biUnion.mp he
    exact hsub i hi he
  have hTdis : Set.PairwiseDisjoint (P : Set I) cyc := by
    intro i hi j hj hij
    exact hdis i hi j hj hij
  have hTcard : T.card = ∑ i ∈ P, (cyc i).card := Finset.card_biUnion hTdis
  have hsaving : (∑ i ∈ P, ((cyc i).card-1)) + P.card = T.card := by
    have hone : (∑ _i ∈ P, (1 : ℕ)) = P.card := by simp
    rw [hTcard,← hone,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    exact Nat.sub_add_cancel (cyc_card_pos i)
  let U : SimpleGraph V := fromEdgeSet (T.image MixedSevenWalks.edge : Set (Sym2 V))
  have hTU : (T.image MixedSevenWalks.edge : Set (Sym2 V)) ⊆ H.edgeSet := by
    intro e he
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp he
    exact (mem_indices H a).mp (hTS ha)
  have hUedge : U.edgeSet = (T.image MixedSevenWalks.edge : Set (Sym2 V)) := by
    rw [edgeSet_fromEdgeSet]
    ext e
    constructor
    · exact fun he => he.1
    · exact fun he => ⟨he,H.edgeSet_subset_setOf_not_isDiag (hTU he)⟩
  have hUH : U ≤ H := by
    apply edgeSet_subset_edgeSet.mp
    rw [hUedge]
    exact hTU
  have hUcard : U.edgeSet.ncard = T.card := by
    rw [hUedge,Set.ncard_coe_finset,Finset.card_image_of_injective _ edge_injective]
  have hpiece (i : P) : (piece i.val).edgeSet ⊆ U.edgeSet := by
    rw [piece_edgeSet,hUedge]
    intro e he
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp he
    exact Finset.mem_image.mpr ⟨a,Finset.mem_biUnion.mpr ⟨i.val,i.property,ha⟩,rfl⟩
  let F : P → U.Subgraph := fun i => {
    verts := (piece i.val).verts
    Adj := (piece i.val).Adj
    adj_sub := fun {u v} huv => hpiece i (show s(u,v) ∈ (piece i.val).edgeSet from huv)
    edge_vert := (piece i.val).edge_vert
    symm := (piece i.val).symm }
  have hcF : ∀ i, (F i).coe.Connected ∧ (F i).coe.IsRegularOfDegree 2 := by
    intro i
    refine ⟨(piece_cycle i.val).1,?_⟩
    intro v
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
      using (piece_cycle i.val).2 v
  have hdF : Pairwise (fun i j => Disjoint (F i).edgeSet (F j).edgeSet) := by
    intro i j hij
    change Disjoint (piece i.val).edgeSet (piece j.val).edgeSet
    rw [piece_edgeSet,piece_edgeSet]
    apply Set.disjoint_left.mpr
    intro e he hf
    obtain ⟨a,ha,hea⟩ := Finset.mem_image.mp he
    obtain ⟨b,hb,heb⟩ := Finset.mem_image.mp hf
    have hab : a = b := edge_injective (hea.trans heb.symm)
    subst b
    exact Finset.disjoint_left.mp (hdis i.val i.property j.val j.property
      (fun he => hij (Subtype.ext he))) ha hb
  have hcov : ∀ e ∈ U.edgeSet, ∃ i, e ∈ (F i).edgeSet := by
    intro e he
    rw [hUedge] at he
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp he
    obtain ⟨i,hi,ha⟩ := Finset.mem_biUnion.mp ha
    refine ⟨⟨i,hi⟩,?_⟩
    change MixedSevenWalks.edge a ∈ (piece i).edgeSet
    rw [piece_edgeSet]
    exact Finset.mem_image.mpr ⟨a,ha,rfl⟩
  have hUn : number U ≤ Fintype.card P := by
    apply number_le_family_cover U F
    · intro i
      refine ⟨(hcF i).1,?_⟩
      intro v
      simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using (hcF i).2 v
    · exact hdF
    · exact hcov
  have hPcard : Fintype.card P = P.card := Fintype.card_coe _
  rw [hPcard] at hUn
  have hrem := Set.ncard_diff_add_ncard_of_subset (edgeSet_mono hUH)
  rw [← edgeSet_sdiff,hUcard,indices_card H hHG] at hrem
  have hn := number_le_restriction_add_edges hUH
  change S.card ≤ 6 + ∑ i ∈ P, ((cyc i).card-1) at hcost
  change (H \ U).edgeSet.ncard + T.card = S.card at hrem
  omega

lemma graph_critical : MixedCritical.IsCritical 7 G := by
  refine ⟨number_eq,?_⟩
  intro H hHG hne
  have hh := proper_number_le certificate H hHG hne
  omega

omit certificate in
lemma graph_minimum_degree : ∀ v : V, 3 ≤ G.degree v := by decide

lemma not_critical_degree_two :
    ¬ (∀ (H : SimpleGraph V) (k : ℕ), MixedCritical.IsCritical k H → 0 < k →
      ∃ v : V, 0 < H.degree v ∧ H.degree v ≤ 2) := by
  intro h
  obtain ⟨v,hv,hd⟩ := h G 7 (graph_critical certificate) (by decide)
  have hh := graph_minimum_degree v
  simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hd hh
  omega

attribute [local instance] FractionalCycles.cyclePieceFintype

lemma not_twice_fractional_comparison :
    ¬ (∀ (H : SimpleGraph V) (k : ℕ), MixedCritical.IsCritical k H →
      ∀ t : FractionalCycles.CyclePiece H → ℝ, FractionalCycles.IsFractionalPartition H t →
        (k : ℝ) ≤ 2 * ∑ J, t J) := by
  intro h
  have hb := h G 7 (graph_critical certificate) MixedSevenFractional.weight MixedSevenFractional.fractional
  rw [MixedSevenFractional.weight_cost] at hb
  norm_num at hb

end Erdos184.MixedSevenCriticalDev
