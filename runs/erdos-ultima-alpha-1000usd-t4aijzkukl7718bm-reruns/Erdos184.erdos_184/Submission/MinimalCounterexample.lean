import Submission.StarElimination

/-!
Necessary structure of an edge-minimal counterexample to a fixed linear
support bound. These results do not prove that such counterexamples are absent.
-/
open SimpleGraph
open scoped Classical
namespace Erdos184
namespace MinimalCounterexample

/-- The fixed-constant pure-cycle bound, charging only nonisolated vertices. -/
def HasBound {V : Type*} [Fintype V] (C : ℕ) (G : SimpleGraph V) : Prop :=
  ∃ D : Finset G.Subgraph,
    (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
    IsDecomposition G D ∧ D.card ≤ C * G.support.ncard

lemma hasBound_bot {V : Type*} [Fintype V] (C : ℕ) :
    HasBound C (⊥ : SimpleGraph V) :=
  ⟨∅, by simp, by simp [IsDecomposition], by simp⟩

/-- Minimality is among even spanning subgraphs, ordered by edge count.
No connectedness or minimum-degree assumption is included in the definition. -/
def IsCritical {V : Type*} [Fintype V] (C : ℕ) (G : SimpleGraph V) : Prop :=
  (∀ v, Even (G.degree v)) ∧ ¬ HasBound C G ∧
  ∀ H : SimpleGraph V, H ≤ G → H.edgeSet.ncard < G.edgeSet.ncard →
    (∀ v, Even (H.degree v)) → HasBound C H

lemma exists_critical_subgraph {V : Type*} [Fintype V] (C : ℕ)
    (G : SimpleGraph V) (he : ∀ v, Even (G.degree v)) (hb : ¬ HasBound C G) :
    ∃ H : SimpleGraph V, H ≤ G ∧ IsCritical C H := by
  let P (n : ℕ) := ∃ H : SimpleGraph V, H ≤ G ∧
    (∀ v, Even (H.degree v)) ∧ ¬ HasBound C H ∧ H.edgeSet.ncard = n
  have hex : ∃ n, P n := ⟨_, G, le_rfl, he, hb, rfl⟩
  obtain ⟨H, hHG, heH, hbH, hnH⟩ := Nat.find_spec hex
  refine ⟨H, hHG, heH, hbH, ?_⟩
  intro K hKH hlt heK
  by_contra hbK
  have hmin := Nat.find_min' hex
    (show P K.edgeSet.ncard from ⟨K, hKH.trans hHG, heK, hbK, rfl⟩)
  omega

lemma IsCritical.ne_bot {V : Type*} [Fintype V] {C : ℕ} {G : SimpleGraph V}
    (hG : IsCritical C G) : G ≠ ⊥ := by
  intro h
  exact hG.2.1 (h ▸ hasBound_bot C)

/-- Deleting a nonempty packing of genuine cycles strictly lowers the edge count. -/
lemma residual_edge_card_lt {V : Type*} [Fintype V] (G : SimpleGraph V)
    (P : Finset G.Subgraph) (hp : P.Nonempty)
    (hc : ∀ H ∈ P, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) :
    (G \ unionPieces G P).edgeSet.ncard < G.edgeSet.ncard := by
  apply Set.ncard_lt_ncard (ht := Set.toFinite _)
  refine Set.ssubset_iff_subset_ne.mpr ⟨SimpleGraph.edgeSet_mono sdiff_le, ?_⟩
  intro heq
  obtain ⟨H, hH⟩ := hp
  obtain ⟨e, he⟩ := cycle_edgeSet_nonempty H (hc H hH).1 (hc H hH).2
  have heG := H.edgeSet_subset he
  have heR : e ∈ (G \ unionPieces G P).edgeSet := heq.symm ▸ heG
  rw [SimpleGraph.edgeSet_sdiff] at heR
  apply heR.2
  rw [unionPieces_edgeSet]
  exact Set.mem_iUnion.mpr ⟨H, Set.mem_iUnion.mpr ⟨hH, he⟩⟩

/-- In a critical graph every nonempty packing costs strictly more than
its support loss can pay. This allows arbitrary packings, not just stars. -/
lemma IsCritical.packing_cost {V : Type*} [Fintype V] {C : ℕ} {G : SimpleGraph V}
    (hG : IsCritical C G) (P : Finset G.Subgraph) (hp : P.Nonempty)
    (hc : ∀ H ∈ P, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : Set.PairwiseDisjoint (P : Set G.Subgraph) (fun H => H.edgeSet)) :
    C * G.support.ncard < P.card + C * (G \ unionPieces G P).support.ncard := by
  have heR := even_residual_of_cycle_packing G hG.1 P hc hd
  obtain ⟨F, hcF, hdF, hbF⟩ := hG.2.2 (G \ unionPieces G P) sdiff_le
    (residual_edge_card_lt G P hp hc) (by
      intro v
      simpa only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
        using heR v)
  obtain ⟨D, hcD, hdD, hbD⟩ := complete_cycle_packing G P hc hd F (by
    intro H hH
    refine ⟨(hcF H hH).1, ?_⟩
    intro v
    simpa only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using (hcF H hH).2 v) hdF
  have hbad : C * G.support.ncard < D.card := by
    by_contra! h
    exact hG.2.1 ⟨D, hcD, hdD, h⟩
  omega

/-- The pieces of a decomposition incident with a set of vertices. -/
noncomputable def touching {V : Type*} {G : SimpleGraph V}
    (D : Finset G.Subgraph) (S : Finset V) : Finset G.Subgraph :=
  S.biUnion (StarElimination.star D)

lemma mem_touching {V : Type*} {G : SimpleGraph V}
    (D : Finset G.Subgraph) (S : Finset V) (H : G.Subgraph) :
    H ∈ touching D S ↔ H ∈ D ∧ ∃ v ∈ S, v ∈ H.verts := by
  simp only [touching, Finset.mem_biUnion, StarElimination.mem_star]
  aesop

lemma touching_subset {V : Type*} {G : SimpleGraph V}
    (D : Finset G.Subgraph) (S : Finset V) : touching D S ⊆ D := by
  intro H hH
  exact ((mem_touching D S H).mp hH).1

lemma touching_nonempty {V : Type*} [Fintype V] {G : SimpleGraph V}
    (D : Finset G.Subgraph)
    (hc : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition G D) (S : Finset V) (hne : S.Nonempty)
    (hs : (S : Set V) ⊆ G.support) : (touching D S).Nonempty := by
  obtain ⟨v, hv⟩ := hne
  have hdeg := (G.degree_pos_iff_mem_support v).mpr (hs hv)
  have hcard := StarElimination.star_card D hc hd v
  obtain ⟨H, hH⟩ := Finset.card_pos.mp (show 0 < (StarElimination.star D v).card by omega)
  exact ⟨H, Finset.mem_biUnion.mpr ⟨v, hv, hH⟩⟩

lemma touching_support_loss {V : Type*} [Fintype V] {G : SimpleGraph V}
    (D : Finset G.Subgraph)
    (hc : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition G D) (S : Finset V) (hs : (S : Set V) ⊆ G.support) :
    (G \ unionPieces G (touching D S)).support.ncard + S.card ≤ G.support.ncard := by
  let R := G \ unionPieces G (touching D S)
  have hsub : (S : Set V) ⊆ G.support \ R.support := by
    intro v hv
    refine ⟨hs hv, ?_⟩
    apply (StarElimination.isolated_iff_star_subset D (touching D S)
      (touching_subset D S) hc hd v).mpr
    intro H hH
    exact Finset.mem_biUnion.mpr ⟨v, hv, hH⟩
  have hcount := Set.ncard_le_ncard hsub
  rw [Set.ncard_coe_finset] at hcount
  have heq := Set.ncard_diff_add_ncard_of_subset
    (SimpleGraph.support_mono (show R ≤ G from sdiff_le))
  change R.support.ncard + S.card ≤ G.support.ncard
  omega

/-- Every nonempty vertex set meets strictly more than C times its size
many pieces of EVERY decomposition of a critical graph. -/
lemma IsCritical.touching_card {V : Type*} [Fintype V] {C : ℕ} {G : SimpleGraph V}
    (hG : IsCritical C G) (D : Finset G.Subgraph)
    (hc : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition G D) (S : Finset V) (hne : S.Nonempty)
    (hs : (S : Set V) ⊆ G.support) : C * S.card < (touching D S).card := by
  have hcost := hG.packing_cost (touching D S) (touching_nonempty D hc hd S hne hs)
    (fun H hH => hc H (touching_subset D S hH))
    (fun H hH K hK hne => hd.1 (touching_subset D S hH) (touching_subset D S hK) hne)
  have hloss := Nat.mul_le_mul_left C (touching_support_loss D hc hd S hs)
  rw [Nat.mul_add] at hloss
  omega

/-- In particular, a nonisolated vertex has degree at least 2(C+1). -/
lemma IsCritical.degree_lower {V : Type*} [Fintype V] {C : ℕ} {G : SimpleGraph V}
    (hG : IsCritical C G) (v : V) (hv : v ∈ G.support) :
    2 * (C + 1) ≤ G.degree v := by
  obtain ⟨D, hc, hd⟩ := even_cycle_decomposition G hG.1
  have h := hG.touching_card D hc hd {v} (Finset.singleton_nonempty v)
    (by simpa using hv)
  simp only [touching, Finset.singleton_biUnion, Finset.card_singleton, Nat.mul_one] at h
  have hdeg := StarElimination.star_card D hc hd v
  omega


/-- Every specified cycle of a critical graph extends to an optimal
cycle decomposition. Minimality is therefore much stronger than a numerical
lower bound on one previously chosen decomposition. -/
lemma IsCritical.extend_cycle {V : Type*} [Fintype V]
    {C : ℕ} {G : SimpleGraph V} (hG : IsCritical C G)
    (H : G.Subgraph) (hcH : H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) :
    ∃ D : Finset G.Subgraph,
      (∀ K ∈ D, K.coe.Connected ∧ K.coe.IsRegularOfDegree 2) ∧
      IsDecomposition G D ∧ H ∈ D ∧ D.card = C * G.support.ncard + 1 := by
  let P : Finset G.Subgraph := {H}
  have hc : ∀ K ∈ P, K.coe.Connected ∧ K.coe.IsRegularOfDegree 2 := by
    intro K hK
    have : K = H := Finset.mem_singleton.mp hK
    subst K
    exact hcH
  have hd : Set.PairwiseDisjoint (P : Set G.Subgraph) (fun H => H.edgeSet) := by
    simp [P]
  have heR := even_residual_of_cycle_packing G hG.1 P hc hd
  obtain ⟨F, hcF, hdF, hbF⟩ := hG.2.2 (G \ unionPieces G P) sdiff_le
    (residual_edge_card_lt G P (Finset.singleton_nonempty _) hc) (by
      intro w
      simpa only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
        using heR w)
  obtain ⟨D, hcD, hdD, hPD, hbD⟩ := complete_cycle_packing_extension G P hc hd F (by
    intro H hH
    refine ⟨(hcF H hH).1, ?_⟩
    intro w
    simpa only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using (hcF H hH).2 w) hdF
  have hbad : C * G.support.ncard < D.card := by
    by_contra! h
    exact hG.2.1 ⟨D, hcD, hdD, h⟩
  have hsupport := Nat.mul_le_mul_left C (Set.ncard_le_ncard
    (SimpleGraph.support_mono (show G \ unionPieces G P ≤ G from sdiff_le)))
  have hP : P.card = 1 := Finset.card_singleton _
  exact ⟨D, hcD, hdD, hPD (Finset.mem_singleton_self H), by omega⟩

/-- An edge-minimal counterexample misses its proposed bound by exactly one
cycle. -/
lemma IsCritical.exists_decomposition_card {V : Type*} [Fintype V]
    {C : ℕ} {G : SimpleGraph V} (hG : IsCritical C G) :
    ∃ D : Finset G.Subgraph,
      (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      IsDecomposition G D ∧ D.card = C * G.support.ncard + 1 := by
  obtain ⟨v, p, hp⟩ := exists_cycle_of_even_nonempty G hG.1 hG.ne_bot
  obtain ⟨D, hcD, hdD, _, hcard⟩ := hG.extend_cycle p.toSubgraph
    (cycle_subgraph_regular G hp)
  exact ⟨D, hcD, hdD, hcard⟩

lemma IsCritical.minimum_card {V : Type*} [Fintype V]
    {C : ℕ} {G : SimpleGraph V} (hG : IsCritical C G)
    (D : Finset G.Subgraph)
    (hc : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition G D)
    (hm : ∀ E : Finset G.Subgraph,
      (∀ H ∈ E, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) →
      IsDecomposition G E → D.card ≤ E.card) :
    D.card = C * G.support.ncard + 1 := by
  obtain ⟨E, hcE, hdE, hcardE⟩ := hG.exists_decomposition_card
  have hle := hm E hcE hdE
  have hbad : C * G.support.ncard < D.card := by
    by_contra! h
    exact hG.2.1 ⟨D, hc, hd, h⟩
  omega

/-- Hall's theorem applied with C copies of each nonisolated vertex. Even
after reserving ANY specified cycle, all these copies have distinct incident
cycle representatives. This does not produce a cycle-count reduction. -/
lemma IsCritical.incident_representatives {V : Type*} [Fintype V]
    {C : ℕ} {G : SimpleGraph V} (hG : IsCritical C G)
    (D : Finset G.Subgraph)
    (hc : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition G D) (H₀ : G.Subgraph) :
    ∃ f : G.support × Fin C ↪ D,
      (∀ i, i.1.val ∈ (f i).val.verts) ∧ (∀ i, (f i).val ≠ H₀) := by
  let t (i : G.support × Fin C) := (StarElimination.star D i.1.val).erase H₀
  have hall : ∀ I : Finset (G.support × Fin C), I.card ≤ (I.biUnion t).card := by
    intro I
    by_cases hI : I.Nonempty
    · let S : Finset V := I.image (fun i => i.1.val)
      have hS : S.Nonempty := hI.image _
      have hSG : (S : Set V) ⊆ G.support := by
        intro v hv
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv
        exact i.1.property
      have hIS : I.card ≤ S.card * C := by
        let emb : G.support × Fin C → V × Fin C := fun i => (i.1.val, i.2)
        have hinj : Function.Injective emb := by
          intro i j h
          change (i.1.val, i.2) = (j.1.val, j.2) at h
          exact Prod.ext (Subtype.ext (congrArg (fun x : V × Fin C => x.1) h))
            (congrArg (fun x : V × Fin C => x.2) h)
        have hsub : I.image emb ⊆ S ×ˢ (Finset.univ : Finset (Fin C)) := by
          intro i hi
          obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
          exact Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨j, hj, rfl⟩,
            Finset.mem_univ _⟩
        have hh := Finset.card_le_card hsub
        simpa only [Finset.card_image_of_injective I hinj, Finset.card_product,
          Finset.card_univ, Fintype.card_fin] using hh
      have htouch := hG.touching_card D hc hd S hS hSG
      have herase : C * S.card ≤ ((touching D S).erase H₀).card := by
        have hh' := Finset.card_erase_eq_ite (s := touching D S) (a := H₀)
        split_ifs at hh' <;> omega
      have hsub : (touching D S).erase H₀ ⊆ I.biUnion t := by
        intro H hH
        obtain ⟨hne, hH⟩ := Finset.mem_erase.mp hH
        obtain ⟨hHD, v, hvS, hvH⟩ := (mem_touching D S H).mp hH
        obtain ⟨i, hi, hiv⟩ := Finset.mem_image.mp hvS
        apply Finset.mem_biUnion.mpr
        refine ⟨i, hi, Finset.mem_erase.mpr ⟨hne, ?_⟩⟩
        exact (StarElimination.mem_star D i.1.val H).mpr ⟨hHD, hiv.symm ▸ hvH⟩
      exact hIS.trans (by simpa only [Nat.mul_comm] using
        (herase.trans (Finset.card_le_card hsub)))
    · simp [Finset.not_nonempty_iff_eq_empty.mp hI]
  obtain ⟨f, hinj, hf⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' t).mp hall
  have hmem : ∀ i, f i ∈ D := fun i =>
    (StarElimination.mem_star D i.1.val (f i)).mp (Finset.mem_erase.mp (hf i)).2 |>.1
  refine ⟨⟨fun i => ⟨f i, hmem i⟩, fun i j h => hinj (congrArg Subtype.val h)⟩, ?_, ?_⟩
  · intro i
    exact ((StarElimination.mem_star D i.1.val (f i)).mp
      (Finset.mem_erase.mp (hf i)).2).2
  · intro i
    exact (Finset.mem_erase.mp (hf i)).1


/-- For an optimal critical decomposition, the representatives give an actual
bijection after any one cycle has been reserved. -/
lemma IsCritical.incident_equiv {V : Type*} [Fintype V]
    {C : ℕ} {G : SimpleGraph V} (hG : IsCritical C G)
    (D : Finset G.Subgraph)
    (hc : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition G D) (hcard : D.card = C * G.support.ncard + 1)
    (H₀ : G.Subgraph) (hH₀ : H₀ ∈ D) :
    ∃ f : G.support × Fin C ≃ D.erase H₀,
      ∀ i, i.1.val ∈ (f i).val.verts := by
  obtain ⟨f, hfv, hfavoid⟩ := hG.incident_representatives D hc hd H₀
  let g : G.support × Fin C → D.erase H₀ := fun i =>
    ⟨(f i).val, Finset.mem_erase.mpr ⟨hfavoid i, (f i).property⟩⟩
  have hginj : Function.Injective g := by
    intro i j h
    apply f.injective
    exact Subtype.ext (congrArg (fun z : D.erase H₀ => z.val) h)
  have hcount : Fintype.card (G.support × Fin C) = Fintype.card (D.erase H₀) := by
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_coe,
      Finset.card_erase_of_mem hH₀, hcard]
    simp only [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, Nat.add_sub_cancel, Nat.mul_comm]
  let e := Equiv.ofBijective g
    ((Fintype.bijective_iff_injective_and_card g).mpr ⟨hginj, hcount⟩)
  exact ⟨e, hfv⟩


/-- Every individual cycle belongs to some minimum decomposition. The minimum
may depend on the specified cycle, and simultaneous extension is NOT asserted. -/
def AllCyclesOptimal {V : Type*} [Fintype V] (G : SimpleGraph V) : Prop :=
  ∀ H : G.Subgraph, (H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) →
    ∃ D : Finset G.Subgraph,
      (∀ K ∈ D, K.coe.Connected ∧ K.coe.IsRegularOfDegree 2) ∧
      IsDecomposition G D ∧ H ∈ D ∧
      ∀ E : Finset G.Subgraph,
        (∀ K ∈ E, K.coe.Connected ∧ K.coe.IsRegularOfDegree 2) →
        IsDecomposition G E → D.card ≤ E.card

lemma IsCritical.allCyclesOptimal {V : Type*} [Fintype V]
    {C : ℕ} {G : SimpleGraph V} (hG : IsCritical C G) : AllCyclesOptimal G := by
  intro H hcH
  obtain ⟨D, hcD, hdD, hHD, hcard⟩ := hG.extend_cycle H hcH
  refine ⟨D, hcD, hdD, hHD, ?_⟩
  intro E hcE hdE
  have hbad : C * G.support.ncard < E.card := by
    by_contra! h
    exact hG.2.1 ⟨E, hcE, hdE, h⟩
  omega

universe u
/-- It suffices to rule out critical graphs for one fixed natural constant.
The nonexistence hypothesis is not proved here. -/
lemma conjecture_of_no_critical (C : ℕ)
    (hno : ∀ {V : Type u} [Fintype V] (G : SimpleGraph V), ¬ IsCritical C G) :
    ∃ f : ℕ → ℝ,
      (f =O[Filter.atTop] fun n : ℕ => (n : ℝ)) ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      ∃ D : Finset G.Subgraph,
        (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition G D ∧
        (D.card : ℝ) ≤ f (Fintype.card V) := by
  apply conjecture_iff_even_cycle_bound.mpr
  refine ⟨C, ?_⟩
  intro V _ _ G he
  have hb : HasBound C G := by
    by_contra h
    obtain ⟨H, _, hH⟩ := exists_critical_subgraph C G he h
    exact hno H hH
  obtain ⟨D, hc, hd, hcard⟩ := hb
  refine ⟨D, hc, hd, ?_⟩
  have hs : G.support.ncard ≤ Fintype.card V := by
    simpa using Set.ncard_le_ncard (Set.subset_univ G.support)
  exact_mod_cast hcard.trans (Nat.mul_le_mul_left C hs)

/-- The original problem can be restricted to graphs where every individual
cycle has an optimal extension. A uniform bound for that class is still missing. -/
lemma conjecture_of_all_optimal_bound (C : ℕ)
    (hb : ∀ {V : Type u} [Fintype V] (G : SimpleGraph V),
      (∀ v, Even (G.degree v)) → AllCyclesOptimal G → HasBound C G) :
    ∃ f : ℕ → ℝ,
      (f =O[Filter.atTop] fun n : ℕ => (n : ℝ)) ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      ∃ D : Finset G.Subgraph,
        (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition G D ∧
        (D.card : ℝ) ≤ f (Fintype.card V) := by
  apply conjecture_of_no_critical C
  intro V _ G hG
  exact hG.2.1 (hb G hG.1 hG.allCyclesOptimal)

/-- Another sufficient condition: a uniform upper bound on the minimum positive
degree in graphs with optimal extensions for all cycles. No such degree bound
is established in this file. -/
lemma conjecture_of_low_degree_in_all_optimal (C : ℕ)
    (hlow : ∀ {V : Type u} [Fintype V] (G : SimpleGraph V),
      G ≠ ⊥ → (∀ v, Even (G.degree v)) → AllCyclesOptimal G →
      ∃ v, v ∈ G.support ∧ G.degree v ≤ 2 * C) :
    ∃ f : ℕ → ℝ,
      (f =O[Filter.atTop] fun n : ℕ => (n : ℝ)) ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      ∃ D : Finset G.Subgraph,
        (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition G D ∧
        (D.card : ℝ) ≤ f (Fintype.card V) := by
  apply conjecture_of_no_critical C
  intro V _ G hG
  obtain ⟨v, hv, hd⟩ := hlow G hG.ne_bot hG.1 hG.allCyclesOptimal
  have hdeg := hG.degree_lower v hv
  omega

end MinimalCounterexample
end Erdos184
