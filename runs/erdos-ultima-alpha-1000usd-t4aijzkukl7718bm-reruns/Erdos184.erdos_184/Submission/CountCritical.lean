import Submission.CycleNumberSubmodularity
import Submission.GlobalVertexMinimal

/-!
Fixed-count critical kernels and exact one-step extraction.
These are auxiliary results. No invariance or uniform size bound is asserted.
-/
open SimpleGraph
open scoped Classical
namespace Erdos184.CountCritical
open CycleNumberSubmodularity
set_option maxHeartbeats 1000000

variable {V : Type*} [Fintype V]

lemma minimum_exists (G : SimpleGraph V) (he : ∀ v, Even (G.degree v)) :
    ∃ D : Finset G.Subgraph,
      (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      IsDecomposition G D ∧ D.card = cycleNumber G := by
  obtain ⟨D,hc,hd⟩ := even_cycle_decomposition G he
  have hex : ∃ n : ℕ, ∃ D : Finset G.Subgraph,
      (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      IsDecomposition G D ∧ D.card = n := ⟨D.card,D,hc,hd,rfl⟩
  rw [cycleNumber,dif_pos hex]
  exact Nat.find_spec hex

lemma number_le (G : SimpleGraph V) (D : Finset G.Subgraph)
    (hc : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition G D) : cycleNumber G ≤ D.card := by
  have hex : ∃ n : ℕ, ∃ E : Finset G.Subgraph,
      (∀ H ∈ E, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      IsDecomposition G E ∧ E.card = n := ⟨D.card,D,hc,hd,rfl⟩
  rw [cycleNumber,dif_pos hex]
  exact Nat.find_min' hex ⟨D,hc,hd,rfl⟩

lemma number_bot : cycleNumber (⊥ : SimpleGraph V) = 0 := by
  apply cycleNumber_eq
  · exact ⟨∅,by simp,by simp [IsDecomposition],by simp⟩
  · intros; omega

lemma edges_lt {G H : SimpleGraph V} (hle : H ≤ G) (hne : H ≠ G) :
    H.edgeSet.ncard < G.edgeSet.ncard := by
  apply Set.ncard_lt_ncard (ht := Set.toFinite _)
  refine Set.ssubset_iff_subset_ne.mpr ⟨SimpleGraph.edgeSet_mono hle,?_⟩
  intro h
  exact hne (edgeSet_injective h)

omit [Fintype V] in
lemma singleton_union (G : SimpleGraph V) (H : G.Subgraph) :
    unionPieces G {H} = H.spanningCoe := by
  ext u v
  simp [unionPieces]

lemma residual_even {G : SimpleGraph V} (he : ∀ v, Even (G.degree v))
    (H : G.Subgraph) (hc : H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) :
    ∀ v, Even ((G \ H.spanningCoe).degree v) := by
  have hcP : ∀ J ∈ ({H} : Finset G.Subgraph),
      J.coe.Connected ∧ J.coe.IsRegularOfDegree 2 := by simpa using hc
  have hdP : Set.PairwiseDisjoint (({H} : Finset G.Subgraph) : Set G.Subgraph)
      (fun J => J.edgeSet) := by simp
  have hh := even_residual_of_cycle_packing G he {H} hcP hdP
  rw [singleton_union G H] at hh
  intro v
  simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using hh v

lemma residual_proper {G : SimpleGraph V} (H : G.Subgraph)
    (hc : H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) : G \ H.spanningCoe ≠ G := by
  obtain ⟨e,he⟩ := cycle_edgeSet_nonempty H hc.1 hc.2
  intro h
  have hh : e ∈ (G \ H.spanningCoe).edgeSet := h.symm ▸ H.edgeSet_subset he
  rw [edgeSet_sdiff] at hh
  exact hh.2 he

lemma cycle_lift {G : SimpleGraph V} (he : ∀ v, Even (G.degree v))
    (H : G.Subgraph) (hc : H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) :
    ∃ D : Finset G.Subgraph,
      (∀ J ∈ D, J.coe.Connected ∧ J.coe.IsRegularOfDegree 2) ∧
      IsDecomposition G D ∧ H ∈ D ∧
      D.card ≤ cycleNumber (G \ H.spanningCoe) + 1 := by
  obtain ⟨E,hcE,hdE,hbE⟩ := minimum_exists (G \ unionPieces G {H}) (by
    intro v
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card,singleton_union]
      using residual_even he H hc v)
  have hcP : ∀ J ∈ ({H} : Finset G.Subgraph),
      J.coe.Connected ∧ J.coe.IsRegularOfDegree 2 := by simpa using hc
  have hdP : Set.PairwiseDisjoint (({H} : Finset G.Subgraph) : Set G.Subgraph)
      (fun J => J.edgeSet) := by simp
  obtain ⟨D,hcD,hdD,hsub,hbD⟩ := complete_cycle_packing_extension G {H} hcP hdP E
    (by
      intro J hJ
      simpa only [IsRegularOfDegree,← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
        using hcE J hJ) hdE
  refine ⟨D,hcD,hdD,hsub (by simp),?_⟩
  rw [hbE] at hbD
  simpa only [Finset.card_singleton,singleton_union,Nat.add_comm] using hbD

lemma number_le_residual_add_one {G : SimpleGraph V} (he : ∀ v, Even (G.degree v))
    (H : G.Subgraph) (hc : H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) :
    cycleNumber G ≤ cycleNumber (G \ H.spanningCoe) + 1 := by
  obtain ⟨D,hcD,hdD,_,hbD⟩ := cycle_lift he H hc
  exact (number_le G D hcD hdD).trans hbD

/-- Every proper even spanning subgraph has strictly smaller minimum count.
This is stronger than merely requiring every individual cycle to extend optimally. -/
def IsCountCritical (k : ℕ) (G : SimpleGraph V) : Prop :=
  (∀ v, Even (G.degree v)) ∧ cycleNumber G = k ∧
  ∀ H : SimpleGraph V, H ≤ G → H ≠ G → (∀ v, Even (H.degree v)) → cycleNumber H < k

lemma extract (G : SimpleGraph V) (he : ∀ v, Even (G.degree v))
    (k : ℕ) (hk : 0 < k) (hkg : k ≤ cycleNumber G) :
    ∃ H : SimpleGraph V, H ≤ G ∧ IsCountCritical k H := by
  let P (m : ℕ) := ∃ H : SimpleGraph V, H ≤ G ∧
    (∀ v, Even (H.degree v)) ∧ k ≤ cycleNumber H ∧ H.edgeSet.ncard = m
  have hex : ∃ m, P m := ⟨_,G,le_rfl,he,hkg,rfl⟩
  obtain ⟨H,hHG,heH,hkH,hm⟩ := Nat.find_spec hex
  have hproper (A : SimpleGraph V) (hAH : A ≤ H) (hne : A ≠ H)
      (heA : ∀ v, Even (A.degree v)) : cycleNumber A < k := by
    by_contra hn
    have hmin := Nat.find_min' hex
      (show P A.edgeSet.ncard from ⟨A,hAH.trans hHG,heA,by omega,rfl⟩)
    have hlt := edges_lt hAH hne
    omega
  have hne : H ≠ ⊥ := by
    intro h; rw [h,number_bot] at hkH; omega
  obtain ⟨v,p,hp⟩ := exists_cycle_of_even_nonempty H heH hne
  have hc := cycle_subgraph_regular H hp
  have hlow := hproper (H \ p.toSubgraph.spanningCoe) sdiff_le
    (residual_proper p.toSubgraph hc) (by
      intro v
      simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
        using residual_even heH p.toSubgraph hc v)
  have hup := number_le_residual_add_one heH p.toSubgraph hc
  exact ⟨H,hHG,heH,by omega,hproper⟩

lemma IsCountCritical.residual_number {k : ℕ} {G : SimpleGraph V}
    (hG : IsCountCritical k G) (H : G.Subgraph)
    (hc : H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) :
    cycleNumber (G \ H.spanningCoe) + 1 = k := by
  have hlo := hG.2.2 (G \ H.spanningCoe) sdiff_le
    (residual_proper H hc) (by
      intro v
      simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
        using residual_even hG.1 H hc v)
  have hhi := number_le_residual_add_one hG.1 H hc
  rw [hG.2.1] at hhi
  omega

lemma IsCountCritical.allCyclesOptimal {k : ℕ} {G : SimpleGraph V}
    (hG : IsCountCritical k G) : MinimalCounterexample.AllCyclesOptimal G := by
  intro H hc
  obtain ⟨D,hcD,hdD,hmem,hb⟩ := cycle_lift hG.1 H hc
  rw [hG.residual_number H hc] at hb
  refine ⟨D,hcD,hdD,hmem,?_⟩
  intro E hcE hdE
  have hE := number_le G E hcE hdE
  rw [hG.2.1] at hE
  omega

/-- Re-extracting a critical kernel after any chosen cycle deletion is valid.
The new kernel has exact count k; it need NOT equal the entire residual. -/
lemma IsCountCritical.residual_kernel {k : ℕ} {G : SimpleGraph V}
    (hG : IsCountCritical (k+1) G) (hk : 0 < k) (H : G.Subgraph)
    (hc : H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) :
    ∃ A : SimpleGraph V, A ≤ G \ H.spanningCoe ∧ IsCountCritical k A := by
  apply extract (G \ H.spanningCoe) (by
    intro v
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
      using residual_even hG.1 H hc v) k hk
  have hh := hG.residual_number H hc
  omega

lemma of_support_critical {C : ℕ} {G : SimpleGraph V}
    (hG : MinimalCounterexample.IsCritical C G) :
    IsCountCritical (C * G.support.ncard + 1) G := by
  obtain ⟨D,hcD,hdD,hbD⟩ := hG.exists_decomposition_card
  have heq : cycleNumber G = C * G.support.ncard + 1 := by
    apply cycleNumber_eq
    · exact ⟨D,hcD,hdD,hbD.le⟩
    · intro E hcE hdE
      by_contra hn
      exact hG.2.1 ⟨E,hcE,hdE,by omega⟩
  refine ⟨hG.1,heq,?_⟩
  intro H hHG hne heH
  obtain ⟨E,hcE,hdE,hbE⟩ := hG.2.2 H hHG (edges_lt hHG hne) heH
  have hn := number_le H E hcE hdE
  have hs := Nat.mul_le_mul_left C (Set.ncard_le_ncard (SimpleGraph.support_mono hHG))
  omega

/-- Invariant partition size implies fixed-count criticality. The converse is
NOT asserted. A proper even subgraph can be completed by at least one cycle. -/
lemma of_invariant {G : SimpleGraph V} (he : ∀ v, Even (G.degree v))
    (hi : InvariantPartitions.HasInvariantCount G) :
    IsCountCritical (cycleNumber G) G := by
  refine ⟨he,rfl,?_⟩
  intro H hHG hne heH
  obtain ⟨E,hcE,hdE,hbE⟩ := minimum_exists H heH
  let P : Finset G.Subgraph := E.image (promote hHG)
  have hcP : ∀ J ∈ P, J.coe.Connected ∧ J.coe.IsRegularOfDegree 2 := by
    intro J hJ
    obtain ⟨K,hK,rfl⟩ := Finset.mem_image.mp hJ
    refine ⟨(hcE K hK).1,?_⟩
    intro v
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
      using (hcE K hK).2 v
  have hdP : Set.PairwiseDisjoint (P : Set G.Subgraph) (fun J => J.edgeSet) := by
    intro J hJ K hK hne
    obtain ⟨A,hA,rfl⟩ := Finset.mem_image.mp hJ
    obtain ⟨B,hB,rfl⟩ := Finset.mem_image.mp hK
    exact hdE.1 hA hB (fun h => hne (congrArg (promote hHG) h))
  have hPcard : P.card = E.card := Finset.card_image_of_injective E
    (InvariantPartitions.promote_injective hHG)
  have hPedge : (unionPieces G P).edgeSet = H.edgeSet := by
    rw [unionPieces_edgeSet,← hdE.2]
    ext e
    constructor
    · intro h
      obtain ⟨J,hJ,heJ⟩ := Set.mem_iUnion₂.mp h
      obtain ⟨K,hK,rfl⟩ := Finset.mem_image.mp hJ
      exact Set.mem_iUnion₂.mpr ⟨K,hK,heJ⟩
    · intro h
      obtain ⟨J,hJ,heJ⟩ := Set.mem_iUnion₂.mp h
      exact Set.mem_iUnion₂.mpr ⟨promote hHG J,Finset.mem_image.mpr ⟨J,hJ,rfl⟩,heJ⟩
  have her := even_residual_of_cycle_packing G he P hcP hdP
  obtain ⟨F,hcF,hdF⟩ := even_cycle_decomposition (G \ unionPieces G P) (by
    intro v
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using her v)
  obtain ⟨D,hcD,hdD,hPD,_⟩ := complete_cycle_packing_extension G P hcP hdP F
    (by
      intro J hJ
      simpa only [IsRegularOfDegree,← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
        using hcF J hJ) hdF
  have hproper : P ≠ D := by
    intro h
    have hh : H.edgeSet = G.edgeSet := by
      rw [← hPedge,unionPieces_edgeSet,h]
      exact hdD.2
    exact hne (edgeSet_injective hh)
  have hlt := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hPD,hproper⟩)
  obtain ⟨Q,hcQ,hdQ,hbQ⟩ := minimum_exists G he
  have heq := hi D Q hcD hdD hcQ hdQ
  rw [hPcard,hbE,heq,hbQ] at hlt
  exact hlt

universe u

/-- Smaller-order minimality forces every sufficiently high-count graph on the
same vertex type to retain all vertices in its support. No subgraph assumption
on H is needed here. -/
lemma support_full_of_high_number {V : Type u} [Fintype V] {C : ℕ}
    {G : SimpleGraph V} (hG : GlobalVertexMinimal.IsVertexMinimal C G)
    (H : SimpleGraph V) (heH : ∀ v, Even (H.degree v))
    (hk : C * (Fintype.card V - 1) < cycleNumber H) : H.support = Set.univ := by
  by_contra hne
  have hcard : H.support.ncard < Fintype.card V := by
    have hh := Set.ncard_lt_ncard (ht := Set.toFinite (Set.univ : Set V))
      (Set.ssubset_iff_subset_ne.mpr ⟨Set.subset_univ _,hne⟩)
    simpa only [Set.ncard_univ,Nat.card_eq_fintype_card] using hh
  have hsmaller : Fintype.card H.support < Fintype.card V := by
    simpa only [← Nat.card_eq_fintype_card,Nat.card_coe_set_eq] using hcard
  have hb := hG.2.2 (H.induce H.support) hsmaller (by
    intro v
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
      using GlobalVertexMinimal.even_induce_support H heH v)
  obtain ⟨D,hc,hd,hbD⟩ := GlobalVertexMinimal.supportBound_of_induce H hb
  have hn := number_le H D hc hd
  have hs : H.support.ncard ≤ Fintype.card V - 1 := by omega
  have hh := Nat.mul_le_mul_left C hs
  omega

/-- Kernel extraction really does preserve support while the count is above
C*(n-1). It does not say that support is lost within a bounded number of steps. -/
lemma kernel_with_full_support {V : Type u} [Fintype V] {C : ℕ}
    {G : SimpleGraph V} (hG : GlobalVertexMinimal.IsVertexMinimal C G)
    (H : SimpleGraph V) (heH : ∀ v, Even (H.degree v)) (k : ℕ)
    (hk : C * (Fintype.card V - 1) < k) (hkn : k ≤ cycleNumber H) :
    ∃ A : SimpleGraph V, A ≤ H ∧ IsCountCritical k A ∧ A.support = Set.univ := by
  obtain ⟨A,hAH,hA⟩ := extract H heH k (by omega) hkn
  refine ⟨A,hAH,hA,support_full_of_high_number hG A hA.1 ?_⟩
  rwa [hA.2.1]

/-- After any selected cycle, a high-count critical kernel can be re-extracted
with exactly one less cycle and without losing support. The graph changes:
criticality of the entire unprocessed residual is not asserted. -/
lemma residual_kernel_with_full_support {V : Type u} [Fintype V] {C k : ℕ}
    {G A : SimpleGraph V} (hG : GlobalVertexMinimal.IsVertexMinimal C G)
    (hA : IsCountCritical (k+1) A) (hk : C * (Fintype.card V - 1) < k)
    (H : A.Subgraph) (hc : H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) :
    ∃ B : SimpleGraph V, B ≤ A \ H.spanningCoe ∧
      IsCountCritical k B ∧ B.support = Set.univ := by
  obtain ⟨B,hBA,hB⟩ := hA.residual_kernel (by omega) H hc
  refine ⟨B,hBA,hB,support_full_of_high_number hG B hB.1 ?_⟩
  rwa [hB.2.1]

end Erdos184.CountCritical
