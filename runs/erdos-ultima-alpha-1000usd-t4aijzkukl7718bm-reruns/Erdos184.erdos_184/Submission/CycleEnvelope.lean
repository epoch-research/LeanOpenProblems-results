import Submission.CountCritical

/-!
The maximum minimum cycle count among even edge subgraphs. Unlike cycleNumber,
this envelope is monotone. No vertex-linear estimate is asserted.
-/
open SimpleGraph
open scoped Classical
namespace Erdos184.CycleEnvelope
open CountCritical CycleNumberSubmodularity
variable {V : Type*} [Fintype V]
set_option maxHeartbeats 1000000

noncomputable def evenSubgraphs (G : SimpleGraph V) : Finset (SimpleGraph V) :=
  Finset.univ.filter (fun H => H ≤ G ∧ ∀ v, Even (H.degree v))

lemma mem_evenSubgraphs {G H : SimpleGraph V} :
    H ∈ evenSubgraphs G ↔ H ≤ G ∧ ∀ v, Even (H.degree v) := by
  simp [evenSubgraphs]

noncomputable def envelope (G : SimpleGraph V) : ℕ :=
  (evenSubgraphs G).sup cycleNumber

lemma number_le_envelope {G H : SimpleGraph V} (hle : H ≤ G)
    (he : ∀ v, Even (H.degree v)) : cycleNumber H ≤ envelope G :=
  Finset.le_sup (mem_evenSubgraphs.mpr ⟨hle,he⟩)

lemma envelope_le {G : SimpleGraph V} {k : ℕ}
    (h : ∀ H : SimpleGraph V, H ≤ G → (∀ v, Even (H.degree v)) → cycleNumber H ≤ k) :
    envelope G ≤ k := by
  apply Finset.sup_le
  intro H hH
  obtain ⟨hle,he⟩ := mem_evenSubgraphs.mp hH
  exact h H hle he

lemma attained (G : SimpleGraph V) :
    ∃ H : SimpleGraph V, H ≤ G ∧ (∀ v, Even (H.degree v)) ∧
      cycleNumber H = envelope G := by
  have hn : (evenSubgraphs G).Nonempty := by
    refine ⟨⊥,mem_evenSubgraphs.mpr ⟨bot_le,?_⟩⟩
    intro v
    simp only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
    simp
  obtain ⟨H,hH,hval⟩ := Finset.exists_mem_eq_sup (evenSubgraphs G) hn cycleNumber
  obtain ⟨hle,he⟩ := mem_evenSubgraphs.mp hH
  exact ⟨H,hle,he,hval.symm⟩

lemma envelope_mono {A G : SimpleGraph V} (hle : A ≤ G) : envelope A ≤ envelope G := by
  apply envelope_le
  intro H hHA he
  exact number_le_envelope (hHA.trans hle) he

lemma envelope_bot : envelope (⊥ : SimpleGraph V) = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply envelope_le
  intro H hH _
  have h : H = ⊥ := le_bot_iff.mp hH
  simp [h,number_bot]

lemma critical_envelope {G : SimpleGraph V} {k : ℕ} (hc : IsCountCritical k G) :
    envelope G = k := by
  apply Nat.le_antisymm
  · apply envelope_le
    intro H hHG heH
    by_cases heq : H = G
    · simpa [heq] using hc.2.1.le
    · exact (hc.2.2 H hHG heq heH).le
  · rw [← hc.2.1]
    exact number_le_envelope le_rfl hc.1

lemma critical_proper_envelope {G A : SimpleGraph V} {k : ℕ}
    (hc : IsCountCritical k G) (hle : A ≤ G) (hne : A ≠ G) : envelope A < k := by
  obtain ⟨H,hHA,heH,hval⟩ := attained A
  rw [← hval]
  apply hc.2.2 H (hHA.trans hle) _ heH
  intro h
  have : G ≤ A := h ▸ hHA
  exact hne (le_antisymm hle this)

lemma critical_kernel (G : SimpleGraph V) (hk : 0 < envelope G) :
    ∃ H : SimpleGraph V, H ≤ G ∧ IsCountCritical (envelope G) H := by
  obtain ⟨A,hAG,heA,hval⟩ := attained G
  obtain ⟨H,hHA,hc⟩ := extract A heA (envelope G) hk hval.ge
  exact ⟨H,hHA.trans hAG,hc⟩

lemma number_le_delete_edge_envelope_add_one (G : SimpleGraph V) (e : Sym2 V)
    {H : SimpleGraph V} (hHG : H ≤ G) (heH : ∀ v, Even (H.degree v)) :
    cycleNumber H ≤ envelope (G.deleteEdges {e}) + 1 := by
  by_cases he : e ∈ H.edgeSet
  · obtain ⟨D,hcD,hdD,_⟩ := minimum_exists H heH
    have heD : e ∈ ⋃ C ∈ D, C.edgeSet := hdD.2.symm ▸ he
    obtain ⟨C,hC,heC⟩ := Set.mem_iUnion₂.mp heD
    have hr : H \ C.spanningCoe ≤ G.deleteEdges {e} := by
      apply edgeSet_subset_edgeSet.mp
      rw [edgeSet_sdiff,edgeSet_deleteEdges]
      intro f hf
      refine ⟨edgeSet_mono hHG hf.1,?_⟩
      intro hfe
      have hfe' : f = e := Set.mem_singleton_iff.mp hfe
      subst f
      exact hf.2 heC
    have hh := number_le_envelope hr (by
      intro v
      simpa only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
        using residual_even heH C (hcD C hC) v)
    exact (number_le_residual_add_one heH C (hcD C hC)).trans (Nat.add_le_add_right hh 1)
  · have hle : H ≤ G.deleteEdges {e} := by
      apply edgeSet_subset_edgeSet.mp
      rw [edgeSet_deleteEdges]
      intro f hf
      refine ⟨edgeSet_mono hHG hf,?_⟩
      intro hfe
      exact he ((Set.mem_singleton_iff.mp hfe) ▸ hf)
    exact (number_le_envelope hle heH).trans (Nat.le_add_right _ _)

/-- Removing one edge lowers the monotone envelope by at most one.
The graph and its one-edge deletion need not be even. -/
lemma delete_edge_lipschitz (G : SimpleGraph V) (e : Sym2 V) :
    envelope G ≤ envelope (G.deleteEdges {e}) + 1 := by
  apply envelope_le
  intro H hHG heH
  exact number_le_delete_edge_envelope_add_one G e hHG heH

/-- Every edge is essential in a count-critical graph, even when the
comparison graph after deletion is not itself even. -/
lemma critical_delete_edge {G : SimpleGraph V} {k : ℕ} (hc : IsCountCritical k G)
    (e : Sym2 V) (he : e ∈ G.edgeSet) : envelope (G.deleteEdges {e}) + 1 = k := by
  have hne : G.deleteEdges {e} ≠ G := by
    intro h
    have hh : e ∈ (G.deleteEdges {e}).edgeSet := h.symm ▸ he
    rw [edgeSet_deleteEdges] at hh
    exact hh.2 (Set.mem_singleton e)
  have hlo := critical_proper_envelope hc (deleteEdges_le {e}) hne
  have hhi := delete_edge_lipschitz G e
  rw [critical_envelope hc] at hhi
  omega

lemma critical_cycle_residual {G : SimpleGraph V} {k : ℕ}
    (hc : IsCountCritical k G) (C : G.Subgraph)
    (hC : C.coe.Connected ∧ C.coe.IsRegularOfDegree 2) :
    envelope (G \ C.spanningCoe) + 1 = k := by
  have hlo := critical_proper_envelope hc sdiff_le (residual_proper C hC)
  have he : ∀ v, Even ((G \ C.spanningCoe).degree v) := by
    intro v
    simpa only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using residual_even hc.1 C hC v
  have hnum := number_le_envelope (G := G \ C.spanningCoe) le_rfl (by
    intro v
    simpa only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] using he v)
  have hres := hc.residual_number C hC
  omega

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
    rw [Finset.card_insert_of_notMem he]
    omega

/-- A forest is a valid zero-count comparison graph, even if it is not even. -/
lemma envelope_acyclic {G : SimpleGraph V} (ha : G.IsAcyclic) : envelope G = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply envelope_le
  intro H hHG heH
  let f : H →g G := ⟨id,fun {_ _} h => hHG h⟩
  have hHa : H.IsAcyclic := ha.comap f Function.injective_id
  have hbot := even_acyclic_eq_bot H heH hHa
  simp [hbot,number_bot]

lemma envelope_forest_bound (G T : SimpleGraph V) (ht : T.IsAcyclic) :
    envelope G ≤ (G.edgeFinset \ T.edgeFinset).card := by
  apply envelope_le
  intro H hHG heH
  obtain ⟨D,hc,hd,hcard⟩ := minimum_exists H heH
  rw [← hcard]
  apply (cycle_decomposition_forest_bound H T ht D hc hd).trans
  apply Finset.card_le_card
  intro e he
  obtain ⟨heH,heT⟩ := Finset.mem_sdiff.mp he
  exact Finset.mem_sdiff.mpr ⟨mem_edgeFinset.mpr (edgeSet_mono hHG
    (mem_edgeFinset.mp heH)),heT⟩

/-- Vertex deletion has a half-degree cost for the monotone envelope.
This is not a uniform constant: the degree is explicit. -/
lemma delete_vertex_degree_cost (G : SimpleGraph V) (v : V) :
    2 * envelope G ≤ 2 * envelope (G.deleteIncidenceSet v) + G.degree v := by
  obtain ⟨H,hHG,heH,hval⟩ := attained G
  obtain ⟨D,hcD,hdD,hcard⟩ := minimum_exists H heH
  let P := StarElimination.star D v
  have hPD : P ⊆ D := StarElimination.star_subset D v
  have hcP : ∀ C ∈ P, C.coe.Connected ∧ C.coe.IsRegularOfDegree 2 :=
    fun C hC => hcD C (hPD hC)
  have hdP : Set.PairwiseDisjoint (P : Set H.Subgraph) (fun C => C.edgeSet) :=
    fun _ hC _ hK hne => hdD.1 (hPD hC) (hPD hK) hne
  let R := H \ unionPieces H P
  have heR : ∀ w, Even (R.degree w) := by
    intro w
    simpa only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using even_residual_of_cycle_packing H heH P hcP hdP w
  have hv : v ∉ R.support :=
    (StarElimination.isolated_iff_star_subset D P hPD hcD hdD v).mpr (by intro C hC; exact hC)
  have hRG : R ≤ G.deleteIncidenceSet v := by
    intro a b hab
    refine deleteIncidenceSet_adj.mpr ⟨hHG hab.1,?_,?_⟩
    · intro h
      exact hv ⟨b,h ▸ hab⟩
    · intro h
      exact hv ⟨a,h ▸ hab.symm⟩
  obtain ⟨E,hcE,hdE,hcardE⟩ := minimum_exists R (by
    intro w
    simpa only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] using heR w)
  obtain ⟨F,hcF,hdF,hbF⟩ := complete_cycle_packing H P hcP hdP E (by
    intro J hJ
    refine ⟨(hcE J hJ).1,?_⟩
    intro w
    simpa only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using (hcE J hJ).2 w) hdE
  have hnum := number_le H F hcF hdF
  have henv := number_le_envelope hRG (by
    intro w
    simpa only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] using heR w)
  have hstar := StarElimination.star_card D hcD hdD v
  have hdeg := H.degree_le_of_le (v := v) hHG
  change 2 * P.card = H.degree v at hstar
  rw [hcardE] at hbF
  rw [hval] at hnum
  simp only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hstar hdeg ⊢
  omega

end Erdos184.CycleEnvelope
