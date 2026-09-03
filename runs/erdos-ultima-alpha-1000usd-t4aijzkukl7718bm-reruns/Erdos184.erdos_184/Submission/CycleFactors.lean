import Submission.FractionalSeparated
import Submission.RootedEnvelopeProfiles
import Submission.SmallSlackExact
import Submission.MixedSmoothing

/-! Fractional exactness of disjoint unions of cycles and a rooted comparison
for graphs that explicitly split into two fractionally exact even parts.
No existence of such a split in arbitrary graphs is asserted. -/
open SimpleGraph
open scoped Classical BigOperators
namespace Erdos184.CycleFactors
open FractionalCycles FractionalEnvelope CountCritical CycleNumberSubmodularity
variable {V : Type*} [Fintype V]
attribute [local instance] FractionalCycles.cyclePieceFintype
set_option maxHeartbeats 1000000

lemma cycles_degree {G : SimpleGraph V} (hG : G.IsCycles) (v : V) :
    G.degree v = 0 ∨ G.degree v = 2 := by
  by_cases hn : (G.neighborSet v).Nonempty
  · right
    simpa only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card,
      Nat.card_coe_set_eq] using hG hn
  · left
    have hh := Set.not_nonempty_iff_eq_empty.mp hn
    simp only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card,
      Nat.card_coe_set_eq, hh, Set.ncard_empty]

lemma cycles_even {G : SimpleGraph V} (hG : G.IsCycles) : ∀ v, Even (G.degree v) := by
  intro v
  rcases cycles_degree hG v with hv | hv <;> rw [hv] <;> decide

lemma even_subgraph_isCycles {G A : SimpleGraph V} (hG : G.IsCycles) (hle : A ≤ G)
    (he : ∀ v, Even (A.degree v)) : A.IsCycles := by
  intro v hn
  have hp := (A.degree_pos_iff_nonempty).mpr hn
  have hl := SimpleGraph.degree_le_of_le (v := v) hle
  have hd := cycles_degree hG v
  obtain ⟨k,hk⟩ := he v
  have heq : A.degree v = 2 := by
    simp only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hp hl hd hk ⊢
    omega
  simpa only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card,
    Nat.card_coe_set_eq] using heq

lemma cycle_residual_support_disjoint {G : SimpleGraph V} (hG : G.IsCycles)
    (H : CyclePiece G) : Disjoint H.val.spanningCoe.support (G \ H.val.spanningCoe).support := by
  apply Set.disjoint_left.mpr
  rintro v ⟨w,hw⟩ hv
  have hg : G.degree v = 2 := by
    simpa only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card,
      Nat.card_coe_set_eq] using hG (show (G.neighborSet v).Nonempty from ⟨w,H.val.adj_sub hw⟩)
  have hc : H.val.spanningCoe.degree v = 2 := by
    rw [Subgraph.degree_spanningCoe]
    simpa only [cycle_piece_degree, if_pos (H.val.edge_vert hw)] using cycle_piece_degree G H v
  have hh := degree_sdiff_of_le H.val.spanningCoe_le v
  have hp := ((G \ H.val.spanningCoe).degree_pos_iff_mem_support v).mpr hv
  simp only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hg hc hh hp
  omega

lemma optimum_cycle {G : SimpleGraph V} (H : CyclePiece G) :
    optimum H.val.spanningCoe = 1 := by
  obtain ⟨v,hv⟩ := H.property.1.nonempty
  have hh := SmallSlackExact.star_exact {H.val} (by simpa using H.property)
    (by simp) v (by simpa using hv)
  simpa only [singleton_union, Finset.card_singleton, Nat.cast_one] using hh

/-- There is no fractional saving in a graph of vertex-disjoint cycles. -/
lemma optimum_eq_number {G : SimpleGraph V} (hG : G.IsCycles) :
    optimum G = (cycleNumber G : ℝ) := by
  generalize hn : G.edgeSet.ncard = n
  induction n using Nat.strong_induction_on generalizing G with
  | h n ih =>
    by_cases hb : G = ⊥
    · subst G
      simp only [optimum_bot, number_bot, Nat.cast_zero]
    have he := cycles_even hG
    obtain ⟨v,p,hp⟩ := exists_cycle_of_even_nonempty G (by
      intro w
      simpa only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] using he w) hb
    let H : CyclePiece G := ⟨p.toSubgraph,cycle_subgraph_regular G hp⟩
    have hr := residual_even he H.val H.property
    have hr' : ∀ w, Even ((G \ H.val.spanningCoe).degree w) := by
      intro w
      simpa only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] using hr w
    have hrc : (G \ H.val.spanningCoe).IsCycles := even_subgraph_isCycles hG sdiff_le (by
      intro w
      simpa only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] using hr' w)
    have hlt := edges_lt (G := G) sdiff_le (residual_proper H.val H.property)
    have hie := ih _ (by omega) hrc rfl
    have hcov : H.val.spanningCoe.edgeSet ∪ (G \ H.val.spanningCoe).edgeSet = G.edgeSet := by
      rw [edgeSet_sdiff]
      exact Set.union_diff_cancel H.val.edgeSet_subset
    have hov : (H.val.spanningCoe.support ∩ (G \ H.val.spanningCoe).support).ncard ≤ 1 := by
      rw [Set.disjoint_iff_inter_eq_empty.mp (cycle_residual_support_disjoint hG H)]
      simp
    have heH : ∀ w, Even (H.val.spanningCoe.degree w) :=
      cycles_even hp.isCycles_spanningCoe_toSubgraph
    have heq := FractionalSeparated.optimum_add hcov hov (by
      intro w
      simpa only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] using heH w) (by
      intro w
      simpa only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] using hr' w)
    rw [optimum_cycle, hie] at heq
    have hnum := number_le_residual_add_one he H.val H.property
    have hle := optimum_le_number G he
    have hnum' : (cycleNumber G : ℝ) ≤ (cycleNumber (G \ H.val.spanningCoe) : ℝ) + 1 := by
      exact_mod_cast hnum
    linarith

lemma number_le_add {G A B : SimpleGraph V}
    (hcover : A.edgeSet ∪ B.edgeSet = G.edgeSet) (hdis : Disjoint A.edgeSet B.edgeSet)
    (heA : ∀ v, Even (A.degree v)) (heB : ∀ v, Even (B.degree v)) :
    cycleNumber G ≤ cycleNumber A + cycleNumber B := by
  have hAG : A ≤ G := edgeSet_subset_edgeSet.mp (by rw [← hcover]; exact Set.subset_union_left)
  have hBG : B ≤ G := edgeSet_subset_edgeSet.mp (by rw [← hcover]; exact Set.subset_union_right)
  obtain ⟨DA,hcA,hdA,hcardA⟩ := minimum_exists A heA
  obtain ⟨DB,hcB,hdB,hcardB⟩ := minimum_exists B heB
  obtain ⟨D,hc,hd,hcard⟩ := combine_pure_decompositions hAG hBG hdis hcover DA DB hcA hcB hdA hdB
  exact (number_le G D hc hd).trans (by simpa only [hcardA,hcardB] using hcard)

omit [Fintype V] in
lemma avoiding_le {G A B : SimpleGraph V} {e : Sym2 V}
    (hcover : A.edgeSet ∪ B.edgeSet = G.edgeSet) (hdis : Disjoint A.edgeSet B.edgeSet)
    (he : e ∈ A.edgeSet) : B ≤ G.deleteEdges {e} := by
  apply edgeSet_subset_edgeSet.mp
  rw [edgeSet_deleteEdges]
  intro f hf
  refine ⟨hcover ▸ (Or.inr hf), ?_⟩
  intro hfe
  have hh : f = e := Set.mem_singleton_iff.mp hfe
  subst f
  exact Set.disjoint_left.mp hdis he hf

/-- A sufficient marked-edge comparison, with the exact split supplied explicitly. -/
lemma rooted_of_exact_split {G A B : SimpleGraph V} {e : Sym2 V}
    (hcover : A.edgeSet ∪ B.edgeSet = G.edgeSet) (hdis : Disjoint A.edgeSet B.edgeSet)
    (heA : ∀ v, Even (A.degree v)) (heB : ∀ v, Even (B.degree v))
    (hxA : optimum A = (cycleNumber A : ℝ)) (hxB : optimum B = (cycleNumber B : ℝ))
    (he : e ∈ G.edgeSet) :
    (cycleNumber G : ℝ) ≤ envelope (G.deleteEdges {e}) + RootedEnvelopeProfiles.through G e := by
  have hAG : A ≤ G := edgeSet_subset_edgeSet.mp (by rw [← hcover]; exact Set.subset_union_left)
  have hBG : B ≤ G := edgeSet_subset_edgeSet.mp (by rw [← hcover]; exact Set.subset_union_right)
  have hnum : (cycleNumber G : ℝ) ≤ (cycleNumber A : ℝ) + (cycleNumber B : ℝ) := by
    exact_mod_cast number_le_add hcover hdis heA heB
  rw [← hcover] at he
  rcases he with he | he
  · have h₁ := RootedEnvelopeProfiles.optimum_le_through hAG heA he
    have h₀ := optimum_le_envelope (avoiding_le hcover hdis he) heB
    rw [hxA] at h₁
    rw [hxB] at h₀
    linarith
  · have h₁ := RootedEnvelopeProfiles.optimum_le_through hBG heB he
    have h₀ := optimum_le_envelope (avoiding_le (by rwa [Set.union_comm]) hdis.symm he) heA
    rw [hxB] at h₁
    rw [hxA] at h₀
    linarith

lemma rooted_of_two_factors {G A B : SimpleGraph V} {e : Sym2 V}
    (hcover : A.edgeSet ∪ B.edgeSet = G.edgeSet) (hdis : Disjoint A.edgeSet B.edgeSet)
    (hA : A.IsCycles) (hB : B.IsCycles) (he : e ∈ G.edgeSet) :
    (cycleNumber G : ℝ) ≤ envelope (G.deleteEdges {e}) + RootedEnvelopeProfiles.through G e :=
  rooted_of_exact_split hcover hdis (cycles_even hA) (cycles_even hB)
    (optimum_eq_number hA) (optimum_eq_number hB) he

end Erdos184.CycleFactors
