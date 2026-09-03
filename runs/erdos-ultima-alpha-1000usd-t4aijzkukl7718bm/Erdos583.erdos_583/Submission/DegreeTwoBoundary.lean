import Submission.EndpointQuota
import Submission.PortPairing

/-! Pairing path pieces across an independent degree-two boundary. -/
open SimpleGraph Erdos583Work Erdos583Work.PendantCompletion
open Erdos583EndpointQuotaDevelopment Erdos583PortPairingDevelopment
namespace Erdos583DegreeTwoBoundaryDevelopment
open scoped Classical
set_option maxHeartbeats 1200000

/-- Attach each boundary vertex to its two labelled core neighbors. -/
def pairedExtension {A B : Type*} (H : SimpleGraph A) (label : B × Bool → A) :
    SimpleGraph (A ⊕ B) where
  Adj x y := match x,y with
    | .inl a,.inl c => H.Adj a c
    | .inl a,.inr b => ∃ t : Bool, label (b,t)=a
    | .inr b,.inl a => ∃ t : Bool, label (b,t)=a
    | .inr _,.inr _ => False
  symm := by rintro (a|b) (c|d) h; exact h.symm; exact h; exact h; exact h
  loopless := by rintro (a|b); exact H.loopless a; simp

def coreInclusion {A B : Type*} (H : SimpleGraph A) (label : B × Bool → A) :
    H →g pairedExtension H label where
  toFun := Sum.inl
  map_rel' h := h

def portEdge {A B : Type*} (label : B × Bool → A) (p : B × Bool) : Sym2 (A ⊕ B) :=
  s(Sum.inl (label p),Sum.inr p.1)

lemma portEdge_injective {A B : Type*} (label : B × Bool → A)
    (hlabel : ∀ b, label (b,true) ≠ label (b,false)) : Function.Injective (portEdge label) := by
  rintro ⟨b,t⟩ ⟨c,u⟩ he
  rcases Sym2.eq_iff.mp he with he | he
  · have hbc : b=c := Sum.inr.inj he.2
    subst c
    have htu : t=u := by
      have hh := Sum.inl.inj he.1
      cases t <;> cases u
      · rfl
      · exact (hlabel b hh.symm).elim
      · exact (hlabel b hh).elim
      · rfl
    subst u
    rfl
  · exact (Sum.inl_ne_inr he.1).elim

lemma portEdge_ne_core {A B : Type*} (label : B × Bool → A) (p : B × Bool) (e : Sym2 A) :
    portEdge label p ≠ Sym2.map (Sum.inl : A → A ⊕ B) e := by
  induction e using Sym2.ind with
  | h a c => simp [portEdge]

lemma portEdge_mem {A B : Type*} (H : SimpleGraph A) (label : B × Bool → A) (p : B × Bool) :
    portEdge label p ∈ (pairedExtension H label).edgeSet := by
  exact ⟨p.2,rfl⟩

def boundaryWalk {A B : Type*} {H : SimpleGraph A} {label : B × Bool → A}
    (p q : B × Bool) (w : H.Walk (label p) (label q)) :
    (pairedExtension H label).Walk (Sum.inr p.1) (Sum.inr q.1) :=
  Walk.cons (show (pairedExtension H label).Adj (Sum.inr p.1) (Sum.inl (label p)) from ⟨p.2,rfl⟩)
    ((w.map (coreInclusion H label)).concat
      (show (pairedExtension H label).Adj (Sum.inl (label q)) (Sum.inr q.1) from ⟨q.2,rfl⟩))

lemma boundaryWalk_isPath {A B : Type*} {H : SimpleGraph A} {label : B × Bool → A}
    (p q : B × Bool) (w : H.Walk (label p) (label q)) (hw : w.IsPath) (hpq : p.1 ≠ q.1) :
    (boundaryWalk p q w).IsPath := by
  have hwmap : (w.map (coreInclusion H label)).IsPath :=
    Walk.map_isPath_of_injective (f := coreInclusion H label) Sum.inl_injective hw
  apply (Walk.cons_isPath_iff _ _).mpr
  constructor
  · apply hwmap.concat
    simp [Walk.support_map,coreInclusion]
  · simp [Walk.support_concat,Walk.support_map,coreInclusion,hpq]

lemma boundaryWalk_edges {A B : Type*} {H : SimpleGraph A} {label : B × Bool → A}
    (p q : B × Bool) (w : H.Walk (label p) (label q)) (e : Sym2 (A ⊕ B)) :
    e ∈ (boundaryWalk p q w).toSubgraph.edgeSet ↔
      e=portEdge label p ∨ e=portEdge label q ∨
        ∃ d ∈ w.toSubgraph.edgeSet, Sym2.map Sum.inl d=e := by
  simp only [Walk.mem_edges_toSubgraph,boundaryWalk,Walk.edges_cons,Walk.edges_concat,
    Walk.edges_map,List.mem_cons,List.concat_eq_append,List.mem_append,List.not_mem_nil,or_false,
    List.mem_map,coreInclusion,portEdge]
  change (e=s(Sum.inr p.1,Sum.inl (label p)) ∨
    (∃ d ∈ w.edges,Sym2.map Sum.inl d=e) ∨ e=s(Sum.inl (label q),Sum.inr q.1)) ↔ _
  rw [Sym2.eq_swap (a := Sum.inr p.1)]
  exact or_congr Iff.rfl or_comm

/-- The fixed pairing of the two ports belonging to the same object. -/
def portFlip (X : Type*) : Equiv.Perm (X × Bool) :=
  Equiv.prodCongr (Equiv.refl X) Equiv.boolNot

lemma portFlip_involutive (X : Type*) : Function.Involutive (portFlip X) := by
  rintro ⟨x,b⟩; cases b <;> rfl

lemma portFlip_ne (X : Type*) (p : X × Bool) : portFlip X p ≠ p := by
  rcases p with ⟨x,b⟩; cases b <;> simp [portFlip]

/-- Reassign endpoint slots without changing their core labels, so that the two
slots of any piece belong to different boundary vertices. -/
lemma separate_endpoint_assignment {A B I : Type*} [Fintype B]
    (label : B × Bool → A) (hlabel : ∀ b, label (b,true) ≠ label (b,false))
    (endpoint : I × Bool → A) (e : I × Bool ≃ B × Bool)
    (he : ∀ x, label (e x)=endpoint x)
    (m : A → B) (hm : Function.Injective m)
    (hincident : ∀ a, ∃ t, label (m a,t)=a) :
    ∃ f : I × Bool ≃ B × Bool,
      (∀ x, label (f x)=endpoint x) ∧ ∀ i, (f (i,true)).1 ≠ (f (i,false)).1 := by
  classical
  let J : Equiv.Perm (B × Bool) := (e.symm.trans (portFlip I)).trans e
  have hJ : Function.Involutive J := by
    intro p
    change e (portFlip I (e.symm (e (portFlip I (e.symm p)))) )=p
    rw [Equiv.symm_apply_apply,portFlip_involutive,Equiv.apply_symm_apply]
  have hJn (p) : J p ≠ p := by
    intro h
    have hh := congrArg e.symm h
    change e.symm (e (portFlip I (e.symm p)))=e.symm p at hh
    rw [Equiv.symm_apply_apply] at hh
    exact portFlip_ne I _ hh
  have hlabels (p : B × Bool) : label (portFlip B p) ≠ label p := by
    rcases p with ⟨b,t⟩
    cases t
    · exact hlabel b
    · exact (hlabel b).symm
  obtain ⟨σ,hσ,hsep⟩ := separate_pairings_of_matching
    (portFlip B) J (portFlip_involutive B) hJ (portFlip_ne B) hJn
    label Prod.fst (fun _ ↦ rfl) hlabels m hm (by
      intro a; obtain ⟨t,ht⟩ := hincident a; exact ⟨(m a,t),rfl,ht⟩)
  refine ⟨e.trans σ,fun x ↦ (hσ (e x)).trans (he x),?_⟩
  intro i hi
  have hpq : σ (e (i,true)) ≠ σ (e (i,false)) := by
    intro hh
    have hh := e.injective (σ.injective hh)
    exact Bool.noConfusion (congrArg Prod.snd hh)
  have hf : portFlip B (σ (e (i,true)))=σ (e (i,false)) := by
    change (σ (e (i,true))).1=(σ (e (i,false))).1 at hi
    generalize σ (e (i,true))=p, σ (e (i,false))=q at *
    rcases p with ⟨b,t⟩; rcases q with ⟨c,u⟩
    dsimp at hi; subst c
    cases t <;> cases u <;> simp_all [portFlip]
  apply hsep (σ (e (i,true)))
  change σ (e (portFlip I (e.symm (σ.symm (σ (e (i,true)))))))=_
  rw [Equiv.symm_apply_apply,Equiv.symm_apply_apply]
  exact hf.symm

universe u

/-- Lift all core pieces through a separated bijective port assignment. -/
lemma lift_piece_family {A B : Type u} {H : SimpleGraph A}
    {label : B × Bool → A} (hlabel : ∀ b, label (b,true) ≠ label (b,false))
    (T : PieceFamily H) (f : T.Index × Bool ≃ B × Bool)
    (hf : ∀ x, label (f x)=T.endpoint x)
    (hsep : ∀ i, (f (i,true)).1 ≠ (f (i,false)).1) :
    ∃ U : PieceFamily (pairedExtension H label),
      Nat.card U.Index=Nat.card B ∧
      (∀ i, ∃ b, U.start i=Sum.inr b) ∧ (∀ i, ∃ b, U.finish i=Sum.inr b) := by
  classical
  let W (i : T.Index) := boundaryWalk (f (i,true)) (f (i,false))
    ((T.walk i).copy (hf (i,true)).symm (hf (i,false)).symm)
  have hpW (i) : (W i).IsPath := by
    apply boundaryWalk_isPath _ _ _ _ (hsep i)
    simpa only [Walk.isPath_copy] using T.isPath i
  have hedge (i) (d : Sym2 (A ⊕ B)) : d ∈ (W i).toSubgraph.edgeSet ↔
      (∃ t, d=portEdge label (f (i,t))) ∨
      ∃ e ∈ (T.walk i).toSubgraph.edgeSet, Sym2.map Sum.inl e=d := by
    dsimp only [W]
    rw [boundaryWalk_edges,NormalTrailSystem.walk_copy_subgraph]
    constructor
    · rintro (h|h|h)
      · exact Or.inl ⟨true,h⟩
      · exact Or.inl ⟨false,h⟩
      · exact Or.inr h
    · rintro (⟨t,ht⟩|h)
      · cases t
        · exact Or.inr (Or.inl ht)
        · exact Or.inl ht
      · exact Or.inr (Or.inr h)
  have hdis : Pairwise fun i j ↦ Disjoint (W i).toSubgraph.edgeSet (W j).toSubgraph.edgeSet := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro d hi hj
    rcases (hedge i d).mp hi with ⟨s,hs⟩ | ⟨e,he,hed⟩
    · rcases (hedge j d).mp hj with ⟨t,ht⟩ | ⟨e,he,hed⟩
      · exact hij (congrArg Prod.fst (f.injective (portEdge_injective label hlabel (hs.symm.trans ht))))
      · exact portEdge_ne_core label _ e (hs.symm.trans hed.symm)
    · rcases (hedge j d).mp hj with ⟨t,ht⟩ | ⟨e',he',he'd⟩
      · exact portEdge_ne_core label _ e (ht.symm.trans hed.symm)
      · have hee' : e=e' := Sym2.map.injective Sum.inl_injective (hed.trans he'd.symm)
        exact Set.disjoint_left.mp (T.disjoint hij) he (hee'.symm ▸ he')
  have hport (p : B × Bool) : ∃ i, portEdge label p ∈ (W i).toSubgraph.edgeSet := by
    obtain ⟨⟨i,t⟩,hp⟩ := f.surjective p
    exact ⟨i,(hedge i _).mpr (Or.inl ⟨t,congrArg (portEdge label) hp.symm⟩)⟩
  have hcover (d) : d ∈ (pairedExtension H label).edgeSet ↔ ∃ i, d ∈ (W i).toSubgraph.edgeSet := by
    constructor
    · induction d using Sym2.ind with
      | h x y =>
        rcases x with a | b <;> rcases y with c | d
        · intro h
          obtain ⟨i,hi⟩ := (T.cover s(a,c)).mp h
          exact ⟨i,(hedge i _).mpr (Or.inr ⟨s(a,c),hi,rfl⟩)⟩
        · rintro ⟨t,ht⟩
          simpa only [portEdge,ht] using hport (d,t)
        · rintro ⟨t,ht⟩
          simpa only [portEdge,ht,Sym2.eq_swap] using hport (b,t)
        · exact False.elim
    · rintro ⟨i,hi⟩
      exact (W i).toSubgraph.edgeSet_subset hi
  let U : PieceFamily (pairedExtension H label) :=
    { Index := T.Index
      finiteIndex := inferInstance
      start := fun i ↦ Sum.inr (f (i,true)).1
      finish := fun i ↦ Sum.inr (f (i,false)).1
      walk := W
      isPath := hpW
      disjoint := hdis
      cover := hcover }
  refine ⟨U,?_,fun i ↦ ⟨_,rfl⟩,fun i ↦ ⟨_,rfl⟩⟩
  have hc := Nat.card_congr f
  simp only [Nat.card_prod,Nat.card_eq_fintype_card,Fintype.card_bool] at hc
  change Nat.card T.Index=Nat.card B
  omega

/-- Independent degree-two boundary case: an incident matching saturating the
core allows a path decomposition with at most one member per boundary vertex. -/
lemma pairedExtension_path_partition {A B : Type u} [Fintype A] [Fintype B]
    (H : SimpleGraph A) (label : B × Bool → A)
    (hlabel : ∀ b, label (b,true) ≠ label (b,false))
    (hparity : ∀ a, Nat.card {p : B × Bool // label p=a} % 2=H.degree a % 2)
    (m : A → B) (hm : Function.Injective m)
    (hincident : ∀ a, ∃ t, label (m a,t)=a) :
    ∃ D : Finset (pairedExtension H label).Subgraph,
      GoodDecomposition (pairedExtension H label) D ∧ D.card ≤ Fintype.card B := by
  classical
  have hpos (a) : 0 < Nat.card {p : B × Bool // label p=a} := by
    obtain ⟨t,ht⟩ := hincident a
    haveI : Nonempty {p : B × Bool // label p=a} := ⟨⟨(m a,t),ht⟩⟩
    exact Nat.card_pos
  obtain ⟨T,e,he⟩ := exists_port_assigned_pieces H label hpos hparity
  obtain ⟨f,hf,hsep⟩ := separate_endpoint_assignment label hlabel T.endpoint e he m hm hincident
  obtain ⟨U,hU,_,_⟩ := lift_piece_family hlabel T f hf hsep
  refine ⟨U.parts,U.parts_good,?_⟩
  exact U.parts_card_le.trans_eq (hU.trans (Nat.card_eq_fintype_card))

end Erdos583DegreeTwoBoundaryDevelopment
