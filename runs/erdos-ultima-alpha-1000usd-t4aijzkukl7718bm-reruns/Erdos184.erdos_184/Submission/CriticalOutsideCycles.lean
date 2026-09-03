import Submission.HighGirthCritical
import Submission.LowCountMean

/-!
At critical count at most three, a cycle separated in vertices from two
edge-disjoint cycles certifies a degree-two vertex. Consequently the graph
outside any cycle in a degree-two-free critical graph has cycle envelope at
most one. This is a restricted obstruction, not a uniform critical bound.
-/
open SimpleGraph
open scoped Classical
namespace Erdos184.CriticalOutsideCycles
open CountCritical CycleNumberSubmodularity FractionalCycles FractionalEnvelope
open HighGirthCritical
variable {V : Type*} [Fintype V] {G : SimpleGraph V}
set_option maxHeartbeats 1000000

lemma cycle_verts_in_support {A : SimpleGraph V} (P : A.Subgraph)
    (hp : P.coe.IsRegularOfDegree 2) : P.verts ⊆ A.support := by
  intro v hv
  have hd := hp ⟨v,hv⟩
  have hn : 0 < P.coe.degree ⟨v,hv⟩ := by
    simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hd ⊢
    omega
  obtain ⟨w,hw⟩ := (P.coe.degree_pos_iff_exists_adj ⟨v,hv⟩).mp hn
  exact ⟨w.val,P.adj_sub hw⟩

lemma cycle_even (C : G.Subgraph)
    (hc : C.coe.Connected ∧ C.coe.IsRegularOfDegree 2) :
    ∀ v, Even (C.spanningCoe.degree v) := by
  intro v
  have hh := CriticalNestedCycles.cycle_degree C hc v
  simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hh ⊢
  rw [hh]
  split_ifs <;> decide

/-- An even restriction of fractional cost at least two, separated from a
cycle, gives a degree-two vertex at critical count at most three. -/
lemma degree_two_of_separated_even {k : ℕ} (hG : IsCountCritical k G) (hk : k ≤ 3)
    (C : G.Subgraph) (hc : C.coe.Connected ∧ C.coe.IsRegularOfDegree 2)
    (A : SimpleGraph V) (hAG : A ≤ G) (heA : ∀ v, Even (A.degree v))
    (hsep : Disjoint C.verts A.support) (hcost : 2 ≤ optimum A) :
    ∃ v, G.degree v = 2 := by
  have hs : Disjoint C.spanningCoe.support A.support :=
    Set.disjoint_left.mpr (fun _ hv ha => Set.disjoint_left.mp hsep
      (by obtain ⟨w,hw⟩ := hv; exact C.edge_vert hw) ha)
  have hover : (C.spanningCoe.support ∩ A.support).ncard ≤ 1 := by
    rw [Set.disjoint_iff_inter_eq_empty.mp hs]
    simp
  have hed := FractionalSeparated.disjoint_of_support_inter_le_one hover
  have heC := cycle_even C hc
  have heU : ∀ v, Even ((C.spanningCoe ⊔ A).degree v) := by
    intro v
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
      using FractionalSeparated.even_sup hed heC heA v
  have hadd : optimum (C.spanningCoe ⊔ A) = 1 + optimum A := by
    rw [FractionalSeparated.optimum_add (by rw [edgeSet_sup]) hover heC heA,
      CycleFactors.optimum_cycle (G := G) (⟨C,hc⟩ : CyclePiece G)]
  have hupper := optimum_le_number (C.spanningCoe ⊔ A) (by
    intro v
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using heU v)
  have hl : 3 ≤ cycleNumber (C.spanningCoe ⊔ A) := by
    have hh : (3 : ℝ) ≤ (cycleNumber (C.spanningCoe ⊔ A) : ℝ) := by
      rw [hadd] at hupper
      linarith
    exact_mod_cast hh
  have heq : C.spanningCoe ⊔ A = G := by
    by_contra hn
    have hh := hG.2.2 _ (sup_le C.spanningCoe_le hAG) hn (by
      intro v
      simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using heU v)
    omega
  obtain ⟨v,hv⟩ := hc.1.nonempty
  have hC := CriticalNestedCycles.cycle_degree C hc v
  rw [if_pos hv] at hC
  have hA : A.degree v = 0 := (A.degree_eq_zero_iff_notMem_support v).mpr
    (fun ha => Set.disjoint_left.mp hsep hv ha)
  have hdeg := degree_sup_of_edge_disjoint C.spanningCoe A hed v
  refine ⟨v,?_⟩
  simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hC hA hdeg ⊢
  rw [heq] at hdeg
  omega

/-- The outside graph need not be even. Every one of its even restrictions
has integral minimum at most one in this degree-two-free critical case. -/
lemma outside_even_number_le_one {k : ℕ} (hG : IsCountCritical k G) (hk : k ≤ 3)
    (hno : ∀ v, G.degree v ≠ 2)
    (C : G.Subgraph) (hc : C.coe.Connected ∧ C.coe.IsRegularOfDegree 2)
    {A : SimpleGraph V} (hA : A ≤ avoid G C.verts) (heA : ∀ v, Even (A.degree v)) :
    cycleNumber A ≤ 1 := by
  by_contra! hn
  obtain ⟨D,hcD,hdD,hcard⟩ := minimum_exists A heA
  have hlo := LowCountMean.two_le_optimum_of_packing heA D hcD hdD.1 (by omega)
  have hsep : Disjoint C.verts A.support := by
    apply Set.disjoint_left.mpr
    intro v hv ha
    exact (avoid_support_subset G C.verts (support_mono hA ha)).2 hv
  obtain ⟨v,hv⟩ := degree_two_of_separated_even hG hk C hc A
    (hA.trans (avoid_le G C.verts)) heA hsep hlo
  exact hno v hv

lemma outside_envelope_le_one {k : ℕ} (hG : IsCountCritical k G) (hk : k ≤ 3)
    (hno : ∀ v, G.degree v ≠ 2)
    (C : G.Subgraph) (hc : C.coe.Connected ∧ C.coe.IsRegularOfDegree 2) :
    CycleEnvelope.envelope (avoid G C.verts) ≤ 1 := by
  apply CycleEnvelope.envelope_le
  intro A hA heA
  exact outside_even_number_le_one hG hk hno C hc hA heA

lemma degree_two_of_separated_pair {k : ℕ} (hG : IsCountCritical k G) (hk : k ≤ 3)
    (C P Q : G.Subgraph)
    (hc : C.coe.Connected ∧ C.coe.IsRegularOfDegree 2)
    (hp : P.coe.Connected ∧ P.coe.IsRegularOfDegree 2)
    (hq : Q.coe.Connected ∧ Q.coe.IsRegularOfDegree 2)
    (hed : Disjoint P.edgeSet Q.edgeSet)
    (hsep : Disjoint C.verts (P.verts ∪ Q.verts)) : ∃ v, G.degree v = 2 := by
  have hne : P ≠ Q := by
    intro heq
    obtain ⟨e,he⟩ := cycle_edgeSet_nonempty P hp.1 hp.2
    exact Set.disjoint_left.mp hed he (heq ▸ he)
  let A := unionPieces G {P,Q}
  have hcA : ∀ H ∈ ({P,Q} : Finset G.Subgraph),
      H.coe.Connected ∧ H.coe.IsRegularOfDegree 2 := by
    intro H hH
    simp only [Finset.mem_insert,Finset.mem_singleton] at hH
    rcases hH with rfl | rfl <;> assumption
  have hdA : Set.PairwiseDisjoint (({P,Q} : Finset G.Subgraph) : Set G.Subgraph)
      (fun H => H.edgeSet) := by
    intro H hH J hJ hHJ
    simp only [Finset.mem_coe,Finset.mem_insert,Finset.mem_singleton] at hH hJ
    rcases hH with rfl | rfl <;> rcases hJ with rfl | rfl
    · exact (hHJ rfl).elim
    · exact hed
    · exact hed.symm
    · exact (hHJ rfl).elim
  have hs : Disjoint C.verts A.support := by
    apply Set.disjoint_left.mpr
    rintro v hv ⟨w,hw⟩
    change s(v,w) ∈ (unionPieces G {P,Q}).edgeSet at hw
    rw [unionPieces_edgeSet] at hw
    obtain ⟨H,hH,he⟩ := Set.mem_iUnion₂.mp hw
    simp only [Finset.mem_insert,Finset.mem_singleton] at hH
    apply Set.disjoint_left.mp hsep hv
    rcases hH with rfl | rfl
    · exact Or.inl (H.edge_vert he)
    · exact Or.inr (H.edge_vert he)
  exact degree_two_of_separated_even hG hk C hc A (unionPieces_le G {P,Q})
    (SmallSlackExact.union_even _ hcA hdA) hs (by
      exact (SmallSlackExact.pair_exact P Q hne hp hq hed).ge)

/-- In the outside graph every pair of genuine cycles must share an edge. -/
lemma outside_cycles_not_disjoint {k : ℕ} (hG : IsCountCritical k G) (hk : k ≤ 3)
    (hno : ∀ v, G.degree v ≠ 2)
    (C : G.Subgraph) (hc : C.coe.Connected ∧ C.coe.IsRegularOfDegree 2)
    (P Q : (avoid G C.verts).Subgraph)
    (hp : P.coe.Connected ∧ P.coe.IsRegularOfDegree 2)
    (hq : Q.coe.Connected ∧ Q.coe.IsRegularOfDegree 2) :
    ¬ Disjoint P.edgeSet Q.edgeSet := by
  intro hed
  let p : CyclePiece G := promoteCycle (avoid_le G C.verts) ⟨P,hp⟩
  let q : CyclePiece G := promoteCycle (avoid_le G C.verts) ⟨Q,hq⟩
  have hvP : P.verts ⊆ (avoid G C.verts).support :=
    cycle_verts_in_support P hp.2
  have hvQ : Q.verts ⊆ (avoid G C.verts).support :=
    cycle_verts_in_support Q hq.2
  have hsep : Disjoint C.verts (p.val.verts ∪ q.val.verts) := by
    apply Set.disjoint_left.mpr
    intro v hv h
    change v ∈ P.verts ∪ Q.verts at h
    rcases h with h | h
    · exact (avoid_support_subset G C.verts (hvP h)).2 hv
    · exact (avoid_support_subset G C.verts (hvQ h)).2 hv
  obtain ⟨v,hv⟩ := degree_two_of_separated_pair hG hk C p.val q.val hc
    p.property q.property hed hsep
  exact hno v hv

end Erdos184.CriticalOutsideCycles
