import Submission.NoTwoCyclesTransport

/-! Exact cycle-decomposition transport through vertex embeddings and isolated vertices. -/
open SimpleGraph
open scoped Classical
namespace Erdos184.CycleDecompositionEmbeddings
variable {V W : Type*} [Fintype V] [Fintype W]
set_option maxHeartbeats 1000000

noncomputable def mapHom (G : SimpleGraph V) (f : V ↪ W) : G →g G.map f :=
  ⟨f,fun {u v} h => ⟨u,v,h,rfl,rfl⟩⟩

lemma pull_cycle (G : SimpleGraph V) (f : V ↪ W) (P : (G.map f).Subgraph)
    (hp : P.coe.Connected ∧ P.coe.IsRegularOfDegree 2) :
    (P.comap (mapHom G f)).coe.Connected ∧
      (P.comap (mapHom G f)).coe.IsRegularOfDegree 2 := by
  let F : (P.comap (mapHom G f)).verts → P.verts := fun v => ⟨f v.val,v.property⟩
  have hF : Function.Bijective F := by
    constructor
    · intro u v h
      apply Subtype.ext
      exact f.injective (congrArg Subtype.val h)
    · intro v
      have hP := CriticalOutsideCycles.cycle_verts_in_support P (by
        intro w
        simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using hp.2 w)
      have hs := hP v.property
      rw [support_map] at hs
      obtain ⟨x,hx,hxv⟩ := hs
      refine ⟨⟨x,?_⟩,?_⟩
      · change f x ∈ P.verts
        rw [hxv]
        exact v.property
      · exact Subtype.ext hxv
  let e : (P.comap (mapHom G f)).coe ≃g P.coe :=
    { toEquiv := Equiv.ofBijective F hF
      map_rel_iff' := by
        intro u v
        change P.Adj (f u.val) (f v.val) ↔ G.Adj u.val v.val ∧ P.Adj (f u.val) (f v.val)
        exact ⟨fun h => ⟨map_adj_apply.mp (P.adj_sub h),h⟩,And.right⟩ }
  refine ⟨e.connected_iff.mpr hp.1,?_⟩
  have hh := regular_two_of_iso e.symm (by
    intro v
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using hp.2 v)
  intro v
  simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using hh v

lemma pull_decomposition (G : SimpleGraph V) (f : V ↪ W)
    (D : Finset (G.map f).Subgraph)
    (hc : ∀ P ∈ D, P.coe.Connected ∧ P.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition (G.map f) D) :
    ∃ E : Finset G.Subgraph,
      (∀ P ∈ E, P.coe.Connected ∧ P.coe.IsRegularOfDegree 2) ∧
      IsDecomposition G E ∧ E.card ≤ D.card := by
  let E := D.image (Subgraph.comap (mapHom G f))
  refine ⟨E,?_,⟨?_,?_⟩,Finset.card_image_le⟩
  · intro P hP
    obtain ⟨Q,hQ,rfl⟩ := Finset.mem_image.mp hP
    have hh := pull_cycle G f Q (hc Q hQ)
    refine ⟨hh.1,?_⟩
    intro v
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using hh.2 v
  · intro P hP Q hQ hpq
    obtain ⟨A,hA,rfl⟩ := Finset.mem_image.mp hP
    obtain ⟨B,hB,rfl⟩ := Finset.mem_image.mp hQ
    have hAB : A ≠ B := fun h => hpq (congrArg (Subgraph.comap (mapHom G f)) h)
    apply Set.disjoint_left.mpr
    intro e heA heB
    induction e using Sym2.ind with
    | h x y =>
      have hPA : s(f x,f y) ∈ A.edgeSet := heA.2
      have hPB : s(f x,f y) ∈ B.edgeSet := heB.2
      exact Set.disjoint_left.mp (hd.1 hA hB hAB) hPA hPB
  · ext e
    constructor
    · intro he
      obtain ⟨P,_,heP⟩ := Set.mem_iUnion₂.mp he
      exact P.edgeSet_subset heP
    · intro he
      induction e using Sym2.ind with
      | h x y =>
        have hm : s(f x,f y) ∈ (G.map f).edgeSet := map_adj_apply.mpr he
        rw [← hd.2] at hm
        obtain ⟨P,hP,heP⟩ := Set.mem_iUnion₂.mp hm
        apply Set.mem_iUnion₂.mpr
        exact ⟨P.comap (mapHom G f),Finset.mem_image.mpr ⟨P,hP,rfl⟩,he,heP⟩

lemma map_decomposition (G : SimpleGraph V) (f : V ↪ W)
    (D : Finset G.Subgraph)
    (hc : ∀ P ∈ D, P.coe.Connected ∧ P.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition G D) :
    ∃ E : Finset (G.map f).Subgraph,
      (∀ P ∈ E, P.coe.Connected ∧ P.coe.IsRegularOfDegree 2) ∧
      IsDecomposition (G.map f) E ∧ E.card ≤ D.card := by
  let φ := mapHom G f
  let E := D.image (Subgraph.map φ)
  refine ⟨E,?_,⟨?_,?_⟩,Finset.card_image_le⟩
  · intro P hP
    obtain ⟨Q,hQ,rfl⟩ := Finset.mem_image.mp hP
    have hh := subgraph_image_cycle_of_injective φ f.injective Q (hc Q hQ).1 (by
      intro v
      simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using (hc Q hQ).2 v)
    refine ⟨hh.1,?_⟩
    intro v
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using hh.2 v
  · intro P hP Q hQ hpq
    obtain ⟨A,hA,rfl⟩ := Finset.mem_image.mp hP
    obtain ⟨B,hB,rfl⟩ := Finset.mem_image.mp hQ
    have hAB : A ≠ B := fun h => hpq (congrArg (Subgraph.map φ) h)
    change Disjoint (A.map φ).edgeSet (B.map φ).edgeSet
    rw [Subgraph.edgeSet_map,Subgraph.edgeSet_map]
    exact Set.disjoint_image_of_injective (Sym2.map.injective f.injective) (hd.1 hA hB hAB)
  · ext e
    constructor
    · intro he
      obtain ⟨P,_,heP⟩ := Set.mem_iUnion₂.mp he
      exact P.edgeSet_subset heP
    · intro he
      rw [edgeSet_map] at he
      obtain ⟨a,ha,rfl⟩ := he
      rw [← hd.2] at ha
      obtain ⟨P,hP,heP⟩ := Set.mem_iUnion₂.mp ha
      apply Set.mem_iUnion₂.mpr
      refine ⟨P.map φ,Finset.mem_image.mpr ⟨P,hP,rfl⟩,?_⟩
      rw [Subgraph.edgeSet_map]
      exact ⟨a,heP,rfl⟩

omit [Fintype V] in
lemma map_induce_support (G : SimpleGraph V) :
    (G.induce G.support).map (Function.Embedding.subtype (· ∈ G.support)) = G := by
  ext x y
  constructor
  · rintro ⟨u,v,h,rfl,rfl⟩
    exact h
  · intro h
    exact ⟨⟨x,y,h⟩,⟨y,x,h.symm⟩,h,rfl,rfl⟩

lemma of_support_decomposition (G : SimpleGraph V)
    (D : Finset (G.induce G.support).Subgraph)
    (hc : ∀ P ∈ D, P.coe.Connected ∧ P.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition (G.induce G.support) D) :
    ∃ E : Finset G.Subgraph,
      (∀ P ∈ E, P.coe.Connected ∧ P.coe.IsRegularOfDegree 2) ∧
      IsDecomposition G E ∧ E.card ≤ D.card := by
  have hh := map_decomposition (G.induce G.support) (Function.Embedding.subtype (· ∈ G.support)) D hc hd
  simp only [IsRegularOfDegree,← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hh ⊢
  rwa [map_induce_support] at hh

end Erdos184.CycleDecompositionEmbeddings
