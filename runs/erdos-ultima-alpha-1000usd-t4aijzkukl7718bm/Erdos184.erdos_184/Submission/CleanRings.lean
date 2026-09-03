import Submission.MinimalRings

/-! Excluding clean contact rings by the established clean-chain theorem. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.CycleRings
open RingIndices MaximumCycles Subfamilies LongRing RigidSwitching
set_option maxHeartbeats 1500000
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

lemma rigid_linear_no_core (hrig : Rigidity.CycleRigid G) (heven : ∀ v, Even (G.degree v))
    (D : Finset G.Subgraph)
    (hD : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : Set.PairwiseDisjoint (D : Set G.Subgraph) (fun H => H.edgeSet))
    (hl : LinearIntersections D) (hDne : D.Nonempty) (S : Set V)
    (hcycle : ∀ H ∈ D, ∃ u ∈ S, ∃ v ∈ S, u ≠ v ∧ u ∈ H.verts ∧ v ∈ H.verts)
    (hvertex : ∀ v ∈ S, ∃ H ∈ D, ∃ K ∈ D, H ≠ K ∧ v ∈ H.verts ∧ v ∈ K.verts) : False := by
  let hcover := (subfamilyGraph_edges D).symm
  let E := lowerFamily D hcover
  have hE : ∀ H ∈ E, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2 := by
    intro H hH
    obtain ⟨K,_,rfl⟩ := Finset.mem_image.mp hH
    simpa only [SimpleGraph.IsRegularOfDegree,← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] using hD K.val K.property
  have hvalid : ∀ H ∈ E, IsCycleOrEdge H.coe := by
    intro H hH
    exact Or.inl (by
      simpa only [SimpleGraph.IsRegularOfDegree,← SimpleGraph.card_neighborSet_eq_degree,
        ← Nat.card_eq_fintype_card] using hE H hH)
  have hnum := rigid_subfamily_number hrig heven D hD hd
  have hEcard : E.card = D.card := lowerFamily_card D hcover
  have hmin : ∀ F : Finset (subfamilyGraph D).Subgraph,
      (∀ H ∈ F, IsCycleOrEdge H.coe) → IsDecomposition (subfamilyGraph D) F → E.card ≤ F.card := by
    intro F hF hf
    rw [hEcard,← hnum]
    exact Critical.number_le F hF hf
  have hEne : E.Nonempty := Finset.card_pos.mp (by rw [hEcard]; exact Finset.card_pos.mpr hDne)
  apply minimal_linear_no_core E hvalid (lowerFamily_decomposition D hcover hd) (lowerFamily_linear D hcover hl)
    (fun H hH => regular_cycle_walk_at H (hE H hH).1 (hE H hH).2)
    hmin E S (Finset.Subset.refl _) hEne
  · intro H hH
    obtain ⟨K,_,rfl⟩ := Finset.mem_image.mp hH
    exact hcycle K.val K.property
  · intro v hv
    obtain ⟨H,hH,K,hK,hHK,hvH,hvK⟩ := hvertex v hv
    refine ⟨lowerPiece D hcover ⟨H,hH⟩,Finset.mem_image.mpr ⟨⟨H,hH⟩,Finset.mem_univ _,rfl⟩,
      lowerPiece D hcover ⟨K,hK⟩,Finset.mem_image.mpr ⟨⟨K,hK⟩,Finset.mem_univ _,rfl⟩,?_,hvH,hvK⟩
    intro he
    exact hHK (congrArg Subtype.val (lowerPiece_injective D hcover he))

lemma two_next_ne (n : ℕ) (i : Fin (n+3)) : i+1+1 ≠ i := by
  intro h
  have he := congrArg Fin.val h
  simp only [Fin.val_add_eq_ite,Fin.val_one] at he
  split_ifs at he <;> omega

lemma Ring.piece_injective {n : ℕ} (R : Ring G n) : Function.Injective R.piece := by
  intro i j he
  by_contra hij
  obtain ⟨e,heP⟩ := cycle_piece_edgeSet_nonempty (R.piece i) (R.cycle i)
  have heE := congrArg (fun H : G.Subgraph => H.edgeSet) he
  dsimp only at heE
  exact Set.disjoint_left.mp (R.disjoint i j hij) heP (by rw [← heE]; exact heP)

lemma Ring.Clean.linear {n : ℕ} {R : Ring G n} (hc : R.Clean) :
    LinearIntersections (Finset.univ.image R.piece) := by
  intro H hH K hK hHK x hxH y hyH hxK hyK
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hH
  obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hK
  have hij : i ≠ j := fun he => hHK (congrArg R.piece he)
  rcases hc i j hij x hxH hxK with ⟨hji,hx⟩ | ⟨hij',hx⟩
  · rcases hc i j hij y hyH hyK with ⟨_,hy⟩ | ⟨hij',hy⟩
    · exact hx.trans hy.symm
    · exact (two_next_ne n i (by rw [← hji,← hij'])).elim
  · rcases hc i j hij y hyH hyK with ⟨hji,hy⟩ | ⟨_,hy⟩
    · exact (two_next_ne n i (by rw [← hji,← hij'])).elim
    · exact hx.trans hy.symm

lemma Ring.Clean.impossible {n : ℕ} {R : Ring G n} (hc : R.Clean)
    (hrig : Rigidity.CycleRigid G) (heven : ∀ v, Even (G.degree v)) : False := by
  let D := Finset.univ.image R.piece
  have hmem (i) : R.piece i ∈ D := Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
  have hD : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2 := by
    intro H hH
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hH
    exact R.cycle i
  have hd : Set.PairwiseDisjoint (D : Set G.Subgraph) (fun H => H.edgeSet) := by
    intro H hH K hK hne
    change H ∈ Finset.univ.image R.piece at hH
    change K ∈ Finset.univ.image R.piece at hK
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hH
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hK
    exact R.disjoint i j (fun he => hne (congrArg R.piece he))
  apply rigid_linear_no_core hrig heven D hD hd hc.linear ⟨R.piece 0,hmem 0⟩ (Set.range R.vertex)
  · intro H hH
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hH
    exact ⟨R.vertex i,⟨i,rfl⟩,R.vertex (i+1),⟨i+1,rfl⟩,
      fun he => next_ne n i (R.injective he).symm,R.first_mem i,R.last_mem i⟩
  · rintro v ⟨i,rfl⟩
    refine ⟨R.piece i,hmem i,R.piece (i-1),hmem (i-1),?_,R.first_mem i,?_⟩
    · intro he
      exact next_ne n (i-1) ((sub_add_cancel i 1).trans (R.piece_injective he))
    · simpa only [sub_add_cancel] using R.last_mem (i-1)

lemma no_ring (hrig : Rigidity.CycleRigid G) (heven : ∀ v, Even (G.degree v)) :
    ∀ n, ¬ Nonempty (Ring G n) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rintro ⟨R⟩
    cases n with
    | zero => exact R.no_base hrig heven
    | succ n =>
      have hadj := R.adjacent_intersection hrig heven (ih n (by omega))
      exact (R.clean_of_no_shorter ih hadj).impossible hrig heven

#print axioms Ring.Clean.impossible
#print axioms no_ring
end Erdos184Work.CycleRings
