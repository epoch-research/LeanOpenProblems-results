import Submission.Work

/-! Path pieces, allowing nil pieces, with specified positive endpoint quotas. -/
open SimpleGraph Erdos583Work Erdos583Work.PendantCompletion
open Erdos583Work.TrailNormalization
namespace Erdos583EndpointQuotaDevelopment
open scoped Classical
set_option maxHeartbeats 1200000
universe u

structure PieceFamily {V : Type u} (G : SimpleGraph V) where
  Index : Type u
  finiteIndex : Finite Index
  start : Index → V
  finish : Index → V
  walk : ∀ i, G.Walk (start i) (finish i)
  isPath : ∀ i, (walk i).IsPath
  disjoint : Pairwise fun i j ↦ Disjoint (walk i).toSubgraph.edgeSet (walk j).toSubgraph.edgeSet
  cover : ∀ e, e ∈ G.edgeSet ↔ ∃ i, e ∈ (walk i).toSubgraph.edgeSet

attribute [instance] PieceFamily.finiteIndex

def PieceFamily.endpoint {V : Type u} {G : SimpleGraph V} (T : PieceFamily G)
    (x : T.Index × Bool) : V := if x.2 then T.start x.1 else T.finish x.1

noncomputable def PieceFamily.quota {V : Type u} {G : SimpleGraph V}
    (T : PieceFamily G) (v : V) : ℕ := Nat.card {x : T.Index × Bool // T.endpoint x=v}

lemma exists_minimum_quota_pieces {V : Type u} [Fintype V] (G : SimpleGraph V) :
    ∃ T : PieceFamily G, ∀ v, T.quota v=1+if Even (G.degree v) then 1 else 0 := by
  classical
  let S : Set V := {v | Even (Nat.card (G.neighborSet v))}
  let H := leafCompletion G S
  have ho (x : V ⊕ S) : Odd (H.degree x) := by
    simpa only [Nat.card_eq_fintype_card,card_neighborSet_eq_degree] using leafCompletion_odd G x
  obtain ⟨k,_,⟨R⟩⟩ := all_odd_normal_trail_system H ho
  obtain ⟨R,hR⟩ := R.exists_max_score
  have hpR := max_score_isPath R hR
  let T : PieceFamily G :=
    { Index := ULift.{u} (Fin k)
      finiteIndex := inferInstance
      start := fun i ↦ root (R.start i.down)
      finish := fun i ↦ root (R.finish i.down)
      walk := fun i ↦ projectWalk (R.walk i.down)
      isPath := fun i ↦ (project_path_support _ (hpR i.down)).1
      disjoint := by
        intro i j hij
        apply Set.disjoint_left.mpr
        intro e he hf
        exact Set.disjoint_left.mp (R.disjoint (fun hh ↦ hij (ULift.ext _ _ hh)))
          ((project_edgeSet _ e).mp he) ((project_edgeSet _ e).mp hf)
      cover := by
        intro e
        constructor
        · intro he
          have heH : Sym2.map Sum.inl e ∈ H.edgeSet := by
            induction e using Sym2.ind with
            | h a b => exact he
          obtain ⟨i,hi⟩ := (R.cover _).mp heH
          exact ⟨⟨i⟩,(project_edgeSet _ e).mpr hi⟩
        · rintro ⟨i,hi⟩
          exact (projectWalk (R.walk i.down)).toSubgraph.edgeSet_subset hi }
  refine ⟨T,?_⟩
  intro v
  let e : T.Index × Bool ≃ V ⊕ S :=
    (Equiv.prodCongr (Equiv.ulift) (Equiv.refl Bool)).trans R.endpointEquiv
  have he (x : T.Index × Bool) : root (e x)=T.endpoint x := by
    rcases x with ⟨i,b⟩
    cases b <;> rfl
  have hc : T.quota v=Nat.card {x : V ⊕ S // root x=v} := by
    apply Nat.card_congr
    exact Equiv.subtypeEquiv e (fun x ↦ by rw [he x])
  rw [hc,root_fiber_card]
  simp only [S,Set.mem_setOf_eq,Nat.card_eq_fintype_card,card_neighborSet_eq_degree]

noncomputable def PieceFamily.addNil {V : Type u} [Fintype V] {G : SimpleGraph V}
    (T : PieceFamily G) (extra : V → ℕ) : PieceFamily G :=
  { Index := T.Index ⊕ (Σ v, Fin (extra v))
    finiteIndex := inferInstance
    start := Sum.elim T.start Sigma.fst
    finish := Sum.elim T.finish Sigma.fst
    walk := fun i ↦ match i with
      | .inl j => T.walk j
      | .inr ⟨_,_⟩ => Walk.nil
    isPath := by rintro (j|⟨v,j⟩); exact T.isPath j; exact Walk.IsPath.nil
    disjoint := by
      rintro (i|⟨v,i⟩) (j|⟨w,j⟩) hij
      · exact T.disjoint (fun hh ↦ hij (congrArg Sum.inl hh))
      · simp
      · simp
      · simp
    cover := by
      intro e
      constructor
      · intro he
        obtain ⟨i,hi⟩ := (T.cover e).mp he
        exact ⟨Sum.inl i,hi⟩
      · rintro ⟨i,hi⟩
        rcases i with i | ⟨v,i⟩
        · exact (T.cover e).mpr ⟨i,hi⟩
        · simp at hi }

lemma PieceFamily.quota_addNil {V : Type u} [Fintype V] {G : SimpleGraph V}
    (T : PieceFamily G) (extra : V → ℕ) (v : V) :
    (T.addNil extra).quota v=T.quota v+2*extra v := by
  classical
  let E₀ := {x : T.Index × Bool // T.endpoint x=v}
  let E₁ := {x : (Σ w, Fin (extra w)) × Bool // x.1.1=v}
  let e : {x : (T.addNil extra).Index × Bool // (T.addNil extra).endpoint x=v} ≃ E₀ ⊕ E₁ :=
    { toFun := by
        rintro ⟨⟨i,b⟩,hi⟩
        rcases i with i | ⟨w,i⟩
        · exact Sum.inl ⟨(i,b),hi⟩
        · exact Sum.inr ⟨(⟨w,i⟩,b),by simpa only [PieceFamily.endpoint,PieceFamily.addNil,Sum.elim_inr,ite_self] using hi⟩
      invFun := by
        rintro (⟨⟨i,b⟩,hi⟩|⟨⟨⟨w,i⟩,b⟩,hi⟩)
        · exact ⟨(Sum.inl i,b),hi⟩
        · exact ⟨(Sum.inr ⟨w,i⟩,b),by simpa only [PieceFamily.endpoint,PieceFamily.addNil,Sum.elim_inr,ite_self] using hi⟩
      left_inv := by rintro ⟨⟨i,b⟩,hi⟩; cases i <;> rfl
      right_inv := by rintro (⟨⟨i,b⟩,hi⟩|⟨⟨⟨w,i⟩,b⟩,hi⟩) <;> rfl }
  let f : E₁ ≃ Fin (extra v) × Bool :=
    { toFun := fun ⟨⟨⟨w,i⟩,b⟩,hi⟩ ↦ (Fin.cast (congrArg extra hi) i,b)
      invFun := fun ⟨i,b⟩ ↦ ⟨(⟨v,i⟩,b),rfl⟩
      left_inv := by rintro ⟨⟨⟨w,i⟩,b⟩,hi⟩; dsimp at hi; subst w; rfl
      right_inv := by rintro ⟨i,b⟩; rfl }
  change Nat.card {x : (T.addNil extra).Index × Bool // (T.addNil extra).endpoint x=v} = _
  rw [Nat.card_congr e,Nat.card_sum,Nat.card_congr f,Nat.card_prod,Nat.card_fin]
  simp only [Nat.card_eq_fintype_card,Fintype.card_bool]
  change T.quota v+extra v*2=T.quota v+2*extra v
  omega

/-- Any everywhere-positive endpoint quota with the correct degree parity can
be realized by edge-disjoint simple path pieces, allowing nil pieces. -/
lemma exists_positive_quota_pieces {V : Type u} [Fintype V] (G : SimpleGraph V)
    (q : V → ℕ) (hpos : ∀ v, 0 < q v) (hparity : ∀ v, q v % 2=G.degree v % 2) :
    ∃ T : PieceFamily G, ∀ v, T.quota v=q v := by
  classical
  obtain ⟨T,hT⟩ := exists_minimum_quota_pieces G
  let extra (v : V) := (q v-T.quota v)/2
  refine ⟨T.addNil extra,?_⟩
  intro v
  rw [T.quota_addNil]
  have hp := hpos v
  have hm := hparity v
  have ht := hT v
  dsimp [extra]
  by_cases he : Even (G.degree v)
  · rw [if_pos he] at ht
    have hd := Nat.even_iff.mp he
    omega
  · rw [if_neg he] at ht
    have hd := Nat.odd_iff.mp (Nat.not_even_iff_odd.mp he)
    omega

/-- Assign the two endpoints of every path piece bijectively to prescribed
ports at those vertices. Quotas are the cardinalities of the label fibers. -/
lemma exists_port_assigned_pieces {V : Type u} [Fintype V] (G : SimpleGraph V)
    {P : Type*} [Fintype P] (label : P → V)
    (hpos : ∀ v, 0 < Nat.card {p : P // label p=v})
    (hparity : ∀ v, Nat.card {p : P // label p=v} % 2=G.degree v % 2) :
    ∃ T : PieceFamily G, ∃ e : T.Index × Bool ≃ P,
      ∀ x, label (e x)=T.endpoint x := by
  classical
  obtain ⟨T,hT⟩ := exists_positive_quota_pieces G
    (fun v ↦ Nat.card {p : P // label p=v}) hpos hparity
  letI : Fintype T.Index := Fintype.ofFinite T.Index
  let E (v : V) : {x : T.Index × Bool // T.endpoint x=v} ≃ {p : P // label p=v} :=
    Fintype.equivOfCardEq (by simpa only [PieceFamily.quota,Nat.card_eq_fintype_card] using hT v)
  exact ⟨T,Equiv.ofFiberEquiv E,Equiv.ofFiberEquiv_map E⟩

noncomputable def PieceFamily.parts {V : Type u} {G : SimpleGraph V}
    (T : PieceFamily G) : Finset G.Subgraph := by
  classical
  letI : Fintype T.Index := Fintype.ofFinite T.Index
  exact Finset.univ.image (fun i ↦ (T.walk i).toSubgraph)

lemma PieceFamily.parts_good {V : Type u} {G : SimpleGraph V}
    (T : PieceFamily G) : GoodDecomposition G T.parts := by
  classical
  letI : Fintype T.Index := Fintype.ofFinite T.Index
  constructor
  · intro K hK
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hK
    exact ⟨T.start i,T.finish i,T.walk i,T.isPath i,rfl⟩
  constructor
  · intro K hK L hL hKL
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hK
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hL
    exact T.disjoint (fun hh ↦ hKL (congrArg (fun i ↦ (T.walk i).toSubgraph) hh))
  · ext d
    simp only [PieceFamily.parts,Set.mem_iUnion,Finset.mem_image,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨K,⟨i,rfl⟩,hd⟩
      exact (T.cover d).mpr ⟨i,hd⟩
    · intro hd
      obtain ⟨i,hi⟩ := (T.cover d).mp hd
      exact ⟨(T.walk i).toSubgraph,⟨i,rfl⟩,hi⟩

lemma PieceFamily.parts_card_le {V : Type u} {G : SimpleGraph V}
    (T : PieceFamily G) : T.parts.card ≤ Nat.card T.Index := by
  classical
  letI : Fintype T.Index := Fintype.ofFinite T.Index
  exact Finset.card_image_le.trans_eq (by simp [Nat.card_eq_fintype_card])

end Erdos583EndpointQuotaDevelopment
