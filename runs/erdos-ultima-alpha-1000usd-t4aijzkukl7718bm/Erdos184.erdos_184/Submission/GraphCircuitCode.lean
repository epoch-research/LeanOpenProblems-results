import Submission.RigidityDegree
import Submission.SerialMinimum

/-! The finite circuit system of even subgraphs. This bridges the abstract
serial theory and the graph decomposition definitions, without assuming a
linear bound or rigidity of arbitrary even-minimal graphs. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.GraphCircuitCode
open Critical EvenCore Rigidity MaximumCycles Erdos184Serial
set_option maxHeartbeats 1800000
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Valid words are exactly the edge sets of even subgraphs. -/
noncomputable def code (G : SimpleGraph V) : Code (Sym2 V) where
  valid s := ∃ R : SimpleGraph V, R ≤ G ∧ (∀ v, Even (R.degree v)) ∧ R.edgeFinset = s
  empty := ⟨⊥,bot_le,by
    intro v
    simp only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
    simp,by ext e; simp⟩
  diff := by
    intro s t hs ht hts
    obtain ⟨R,hRG,hR,rfl⟩ := hs
    obtain ⟨T,hTG,hT,rfl⟩ := ht
    have hTR : T ≤ R := SimpleGraph.edgeFinset_subset_edgeFinset.mp hts
    refine ⟨R \ T,sdiff_le.trans hRG,?_,by ext e; simp⟩
    simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
      using sdiff_even hR hTR hT

lemma valid_edgeFinset {G R : SimpleGraph V} (hRG : R ≤ G)
    (hR : ∀ v, Even (R.degree v)) : (code G).valid R.edgeFinset := ⟨R,hRG,hR,rfl⟩

lemma valid_full_iff (G : SimpleGraph V) :
    (code G).valid G.edgeFinset ↔ ∀ v, Even (G.degree v) := by
  constructor
  · rintro ⟨R,_,hR,he⟩
    have hRG : R = G := SimpleGraph.edgeFinset_inj.mp he
    subst R
    exact hR
  · intro hG
    exact valid_edgeFinset le_rfl hG

lemma edgeFinset_nonempty_iff (G : SimpleGraph V) : G.edgeFinset.Nonempty ↔ G ≠ ⊥ := by
  rw [Finset.nonempty_iff_ne_empty]
  constructor
  · intro hne he
    subst G
    exact hne (by simp)
  · intro hne he
    apply hne
    apply SimpleGraph.edgeFinset_inj.mp
    simpa using he

lemma cycle_number_one {G : SimpleGraph V} (H : G.Subgraph)
    (hH : H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) : number H.spanningCoe = 1 := by
  have hcover : (⋃ K ∈ ({H} : Finset G.Subgraph), K.edgeSet) = H.spanningCoe.edgeSet := by
    simp only [Finset.set_biUnion_singleton]
    rfl
  have hp : Set.PairwiseDisjoint (({H} : Finset G.Subgraph) : Set G.Subgraph) (fun K => K.edgeSet) := by
    intro K hK L hL hne
    have hK' : K = H := Finset.mem_singleton.mp hK
    have hL' : L = H := Finset.mem_singleton.mp hL
    exact (hne (hK'.trans hL'.symm)).elim
  have hprop : ∀ K ∈ ({H} : Finset G.Subgraph), IsCycleOrEdge K.coe := by
    intro K hK
    have he := Finset.mem_singleton.mp hK
    subst K
    exact Or.inl (by simpa only [SimpleGraph.IsRegularOfDegree,
      ← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using hH)
  have hdec := Subfamilies.lowerFamily_decomposition {H} hcover hp
  have hprops := Subfamilies.lowerFamily_property IsCycleOrEdge {H} hcover hprop
  have hle := number_le _ hprops hdec
  have hc := Subfamilies.lowerFamily_card {H} hcover
  simp only [Finset.card_singleton] at hc
  have hne : H.spanningCoe ≠ ⊥ := by
    obtain ⟨e,he⟩ := cycle_piece_edgeSet_nonempty H hH
    intro h
    change e ∈ H.spanningCoe.edgeSet at he
    rw [h] at he
    simpa using he
  have hn := mt (StarCharacterization.number_eq_zero_iff H.spanningCoe).mp hne
  omega

lemma circuit_iff_number_one {G R : SimpleGraph V} (hRG : R ≤ G)
    (hR : ∀ v, Even (R.degree v)) :
    Circuit (code G) R.edgeFinset ↔ number R = 1 := by
  constructor
  · intro hc
    have hne : R ≠ ⊥ := (edgeFinset_nonempty_iff R).mp hc.2.1
    obtain ⟨u,p,hp⟩ := exists_cycle_of_even_ne_bot R hR hne
    have hC : (code G).valid p.toSubgraph.spanningCoe.edgeFinset :=
      valid_edgeFinset (p.toSubgraph.spanningCoe_le.trans hRG) (cycle_spanning_even R hp)
    have hCn : p.toSubgraph.spanningCoe.edgeFinset.Nonempty := by
      apply Finset.card_pos.mp
      have he := cycle_edge_count R hp
      have hl := hp.three_le_length
      simp only [SimpleGraph.edgeFinset_card,← Nat.card_eq_fintype_card] at he ⊢
      omega
    have he := hc.2.2 _ (SimpleGraph.edgeFinset_mono p.toSubgraph.spanningCoe_le) hC hCn
    have hgraph : p.toSubgraph.spanningCoe = R := SimpleGraph.edgeFinset_inj.mp he
    rw [← hgraph]
    apply cycle_number_one
    simpa only [SimpleGraph.IsRegularOfDegree,← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] using cycle_coe_regular R hp
  · intro hn
    have hne : R ≠ ⊥ := by intro he; rw [he,number_bot] at hn; omega
    refine ⟨valid_edgeFinset hRG hR,(edgeFinset_nonempty_iff R).mpr hne,?_⟩
    intro t hts ht htne
    obtain ⟨T,hTG,hT,rfl⟩ := ht
    have hTR : T ≤ R := SimpleGraph.edgeFinset_subset_edgeFinset.mp hts
    by_contra he
    have hlt : T.edgeFinset.card < R.edgeFinset.card :=
      Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hts,he⟩)
    have hmin := (rigid_of_number_le_one hR hn.le).evenMinimal hR
    have hnum := hmin T hTR hT hlt
    have hzero : number T = 0 := by omega
    have hbot := (StarCharacterization.number_eq_zero_iff T).mp hzero
    exact (edgeFinset_nonempty_iff T).mp htne hbot

lemma cycle_circuit {G : SimpleGraph V} (H : G.Subgraph)
    (hH : H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) :
    Circuit (code G) H.spanningCoe.edgeFinset := by
  apply (circuit_iff_number_one H.spanningCoe_le (regular_two_spanning_even H hH.2)).mpr
  exact cycle_number_one H hH

lemma circuit_piece {G : SimpleGraph V} {s : Finset (Sym2 V)}
    (hc : Circuit (code G) s) :
    ∃ H : G.Subgraph, (H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧ H.spanningCoe.edgeFinset = s := by
  obtain ⟨R,hRG,hR,rfl⟩ := hc.1
  have hn := (circuit_iff_number_one hRG hR).mp hc
  obtain ⟨D,hD,hdec,hcard⟩ := minimum_cycles hR
  obtain ⟨A,hA,hpA,heA,hcA⟩ := lift_cycle_decomposition_exact hRG D hD hdec
  have hA1 : A.card = 1 := by omega
  obtain ⟨H,rfl⟩ := Finset.card_eq_one.mp hA1
  refine ⟨H,hA H (Finset.mem_singleton_self H),?_⟩
  have he : H.spanningCoe.edgeSet = R.edgeSet := by
    simpa only [Finset.set_biUnion_singleton] using heA
  exact congrArg (fun R : SimpleGraph V => R.edgeFinset) (SimpleGraph.edgeSet_injective he)

#print axioms code
#print axioms circuit_iff_number_one
#print axioms circuit_piece

lemma graph_cycle_partition {G R : SimpleGraph V} (hRG : R ≤ G)
    (D : Finset R.Subgraph)
    (hD : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hdec : IsDecomposition R D) :
    Partition (code G) R.edgeFinset (D.image (fun H => H.spanningCoe.edgeFinset)) ∧
    (D.image (fun H => H.spanningCoe.edgeFinset)).card = D.card := by
  have hinj : Set.InjOn (fun H : R.Subgraph => H.spanningCoe.edgeFinset) (D : Set R.Subgraph) := by
    intro H hH K hK he
    by_contra hn
    obtain ⟨e,heH⟩ := cycle_piece_edgeSet_nonempty H (hD H hH)
    have hsets : H.edgeSet = K.edgeSet := by
      simpa only [SimpleGraph.coe_edgeFinset] using congrArg (fun s : Finset (Sym2 V) => (s : Set (Sym2 V))) he
    have heK : e ∈ K.edgeSet := by rw [← hsets]; exact heH
    exact Set.disjoint_left.mp (hdec.1 hH hK hn) heH heK
  refine ⟨⟨?_,?_,?_⟩,Finset.card_image_of_injOn hinj⟩
  · intro a ha
    obtain ⟨H,hH,rfl⟩ := Finset.mem_image.mp ha
    apply (circuit_iff_number_one (H.spanningCoe_le.trans hRG)
      (regular_two_spanning_even H (hD H hH).2)).mpr
    exact cycle_number_one H (hD H hH)
  · intro a ha b hb hn
    obtain ⟨H,hH,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨K,hK,rfl⟩ := Finset.mem_image.mp hb
    apply Finset.disjoint_left.mpr
    intro e heH heK
    exact Set.disjoint_left.mp (hdec.1 hH hK (fun h => hn (congrArg (fun H => H.spanningCoe.edgeFinset) h)))
      (SimpleGraph.mem_edgeFinset.mp heH) (SimpleGraph.mem_edgeFinset.mp heK)
  · ext e
    simp only [Finset.mem_biUnion,Finset.mem_image,id_eq,SimpleGraph.mem_edgeFinset]
    constructor
    · rintro ⟨a,⟨H,hH,rfl⟩,he⟩
      exact H.edgeSet_subset (SimpleGraph.mem_edgeFinset.mp he)
    · intro he
      rw [← hdec.2] at he
      obtain ⟨H,he⟩ := Set.mem_iUnion.mp he
      obtain ⟨hH,he⟩ := Set.mem_iUnion.mp he
      exact ⟨H.spanningCoe.edgeFinset,⟨H,hH,rfl⟩,SimpleGraph.mem_edgeFinset.mpr he⟩

lemma circuit_partition_graph {G : SimpleGraph V} {s : Finset (Sym2 V)}
    {P : Finset (Finset (Sym2 V))} (hP : Partition (code G) s P) :
    ∃ D : Finset G.Subgraph,
      (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      Set.PairwiseDisjoint (D : Set G.Subgraph) (fun H => H.edgeSet) ∧
      (⋃ H ∈ D, H.edgeSet) = (s : Set (Sym2 V)) ∧ D.card = P.card := by
  have hex : ∀ a : P, ∃ H : G.Subgraph,
      (H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧ H.spanningCoe.edgeFinset = a.val := by
    intro a
    exact circuit_piece (hP.1 a.val a.property)
  choose H hH he using hex
  have hinj : Function.Injective H := by
    intro a b hab
    apply Subtype.ext
    rw [← he a,← he b,hab]
  refine ⟨Finset.univ.image H,?_,?_,?_,?_⟩
  · intro K hK
    obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hK
    exact hH a
  · intro K hK L hL hn
    obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hK
    obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp hL
    apply Set.disjoint_left.mpr
    intro e heA heB
    have ha : e ∈ a.val := by rw [← he a]; exact SimpleGraph.mem_edgeFinset.mpr heA
    have hb : e ∈ b.val := by rw [← he b]; exact SimpleGraph.mem_edgeFinset.mpr heB
    exact Finset.disjoint_left.mp (hP.2.1 a.property b.property
      (fun h => hn (congrArg H (Subtype.ext h)))) ha hb
  · ext e
    simp only [Set.mem_iUnion,Finset.mem_image,Finset.mem_univ,true_and,Finset.mem_coe]
    constructor
    · rintro ⟨K,⟨a,rfl⟩,heK⟩
      apply hP.piece_subset a.property
      rw [← he a]
      exact SimpleGraph.mem_edgeFinset.mpr heK
    · intro hes
      rw [← hP.2.2] at hes
      obtain ⟨a,ha,hea⟩ := Finset.mem_biUnion.mp hes
      let i : P := ⟨a,ha⟩
      have hem : e ∈ (H i).spanningCoe.edgeFinset := by rw [he i]; exact hea
      exact ⟨H i,⟨i,rfl⟩,SimpleGraph.mem_edgeFinset.mp hem⟩
  · rw [Finset.card_image_of_injective _ hinj,Finset.card_univ,Fintype.card_coe]

lemma hasNumber {G R : SimpleGraph V} (hRG : R ≤ G) (hR : ∀ v, Even (R.degree v)) :
    HasNumber (code G) R.edgeFinset (number R) := by
  constructor
  · obtain ⟨D,hD,hdec,hcard⟩ := minimum_cycles hR
    obtain ⟨hP,hcP⟩ := graph_cycle_partition hRG D hD hdec
    exact ⟨_,hP,hcP.trans hcard⟩
  · intro P hP
    obtain ⟨D,hD,hdis,hcover,hcard⟩ := circuit_partition_graph hP
    have he : (⋃ H ∈ D, H.edgeSet) = R.edgeSet := by
      rw [hcover]
      ext e
      exact SimpleGraph.mem_edgeFinset
    have hD' : ∀ H ∈ D, IsCycleOrEdge H.coe := by
      intro H hH
      exact Or.inl (by simpa only [SimpleGraph.IsRegularOfDegree,
        ← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using hD H hH)
    have hp := Subfamilies.lowerFamily_property IsCycleOrEdge D he hD'
    have hd := Subfamilies.lowerFamily_decomposition D he hdis
    have hn := number_le _ hp hd
    rwa [Subfamilies.lowerFamily_card,hcard] at hn

lemma hasNumber_iff {G R : SimpleGraph V} (hRG : R ≤ G)
    (hR : ∀ v, Even (R.degree v)) (k : ℕ) :
    HasNumber (code G) R.edgeFinset k ↔ number R = k := by
  constructor
  · intro hk
    exact (hasNumber hRG hR).unique hk
  · intro hk
    rw [← hk]
    exact hasNumber hRG hR

#print axioms graph_cycle_partition
#print axioms circuit_partition_graph
#print axioms hasNumber_iff

lemma minimalCore_iff {G R : SimpleGraph V} (hRG : R ≤ G)
    (hR : ∀ v, Even (R.degree v)) (k : ℕ) :
    MinimalCore (code G) R.edgeFinset k ↔ EvenMinimal R ∧ number R = k := by
  constructor
  · intro hmin
    have hk := (hasNumber_iff hRG hR k).mp hmin.1
    refine ⟨?_,hk⟩
    intro T hTR hT hlt
    have hsub : T.edgeFinset ⊂ R.edgeFinset := by
      refine Finset.ssubset_iff_subset_ne.mpr ⟨SimpleGraph.edgeFinset_mono hTR,?_⟩
      intro he
      have hc := congrArg Finset.card he
      omega
    obtain ⟨P,hP,hcard⟩ := hmin.2 T.edgeFinset hsub (valid_edgeFinset (hTR.trans hRG) hT)
    have hnum := (hasNumber (hTR.trans hRG) hT).2 P hP
    omega
  · rintro ⟨hmin,hk⟩
    refine ⟨(hasNumber_iff hRG hR k).mpr hk,?_⟩
    intro t hts ht
    obtain ⟨T,hTG,hT,rfl⟩ := ht
    have hTR : T ≤ R := SimpleGraph.edgeFinset_subset_edgeFinset.mp hts.1
    have hn := hmin T hTR hT (Finset.card_lt_card hts)
    obtain ⟨P,hP,hcard⟩ := (hasNumber hTG hT).1
    exact ⟨P,hP,by omega⟩

lemma rigid_iff {G R : SimpleGraph V} (hRG : R ≤ G)
    (hR : ∀ v, Even (R.degree v)) :
    Rigid (code G) R.edgeFinset (number R) ↔ CycleRigid R := by
  constructor
  · intro hr D hD hdec
    obtain ⟨hP,hcard⟩ := graph_cycle_partition hRG D hD hdec
    have hn := hr _ hP
    omega
  · intro hr P hP
    obtain ⟨D,hD,hdis,hcover,hcard⟩ := circuit_partition_graph hP
    have he : (⋃ H ∈ D, H.edgeSet) = R.edgeSet := by
      rw [hcover]
      ext e
      exact SimpleGraph.mem_edgeFinset
    have hp := Subfamilies.lowerFamily_property
      (fun {_} [_] H => H.Connected ∧ H.IsRegularOfDegree 2) D he (by
        intro H hH
        simpa only [SimpleGraph.IsRegularOfDegree,← SimpleGraph.card_neighborSet_eq_degree,
          ← Nat.card_eq_fintype_card] using hD H hH)
    have hd := Subfamilies.lowerFamily_decomposition D he hdis
    have hn := hr (Subfamilies.lowerFamily D he) (by
      simpa only [SimpleGraph.IsRegularOfDegree,← SimpleGraph.card_neighborSet_eq_degree,
        ← Nat.card_eq_fintype_card] using hp) hd
    rwa [Subfamilies.lowerFamily_card,hcard] at hn

/-- Exact agreement of the two notions of a nonrigid minimal core. -/
lemma nonrigid_minimal_iff {G R : SimpleGraph V} (hRG : R ≤ G)
    (hR : ∀ v, Even (R.degree v)) :
    (MinimalCore (code G) R.edgeFinset (number R) ∧
      ¬ Rigid (code G) R.edgeFinset (number R)) ↔
      EvenMinimal R ∧ ¬ CycleRigid R := by
  rw [minimalCore_iff hRG hR,rigid_iff hRG hR]
  simp

#print axioms minimalCore_iff
#print axioms rigid_iff
#print axioms nonrigid_minimal_iff
end Erdos184Work.GraphCircuitCode
