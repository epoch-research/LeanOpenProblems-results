import Submission.NoPrismRightCover
import Submission.ArcTwoCover
import Submission.CountableBadEdgeFilter

/-! Cover transfer for the right adjoint of a Cartesian product with K₂.
This is an auxiliary result, not a settlement of the main conjecture. -/
set_option autoImplicit false
open SimpleGraph Set
namespace Erdos595CartesianBoolRight
open Erdos595Work Erdos595ArcAdjoint Erdos595MatchingBundle
variable {V : Type*} (H : SimpleGraph V)

def prism : SimpleGraph (V × Bool) where
  Adj a b := (a.2 = b.2 ∧ H.Adj a.1 b.1) ∨ (a.1 = b.1 ∧ a.2 ≠ b.2)
  symm := fun _ _ h => h.elim (fun h => Or.inl ⟨h.1.symm,h.2.symm⟩)
    (fun h => Or.inr ⟨h.1.symm,h.2.symm⟩)
  loopless := fun _ h => h.elim (fun h => h.2.ne rfl) (fun h => h.2 rfl)

lemma same_layer {a b : V × Bool} (h : (prism H).Adj a b) (he : a.2 = b.2) :
    H.Adj a.1 b.1 := h.elim And.right (fun h => (h.2 he).elim)

lemma other_layer {a b : V × Bool} (h : (prism H).Adj a b) (he : a.2 ≠ b.2) :
    a.1 = b.1 := h.elim (fun h => (he h.1).elim) And.left

lemma triangle_layer {a b c : V × Bool}
    (hab : (prism H).Adj a b) (hac : (prism H).Adj a c) (hbc : (prism H).Adj b c) :
    a.2 = b.2 ∧ a.2 = c.2 := by
  have aux {a b c : V × Bool}
      (hab : (prism H).Adj a b) (hac : (prism H).Adj a c) (hbc : (prism H).Adj b c) :
      a.2 = b.2 := by
    by_contra hn
    have he := other_layer H hab hn
    have hc : c.2 = a.2 ∨ c.2 = b.2 := by
      cases ha : a.2 <;> cases hb : b.2 <;> cases hc : c.2 <;> simp_all
    rcases hc with hc | hc
    · have hca := same_layer H hac hc.symm
      have hcb := other_layer H hbc (fun h => hn (hc.symm.trans h.symm))
      exact hca.ne (he.trans hcb)
    · have hcb := same_layer H hbc hc.symm
      have hca := other_layer H hac (fun h => hn (h.trans hc))
      exact hcb.ne (he.symm.trans hca)
  exact ⟨aux hab hac hbc,aux hac hab hbc.symm⟩

def layer (p : Biclique (prism H)) (b : Bool) : Biclique H :=
  ⟨({v | (v,b) ∈ Left (prism H) p},{v | (v,b) ∈ Right (prism H) p}),
    fun _ hx _ hy => same_layer H (p.property _ hx _ hy) rfl⟩

def Good (p q : Biclique (prism H)) : Prop :=
  ∃ b, (right H).Adj (layer H p b) (layer H q b)

def Mixed (p : Biclique (prism H)) : Prop :=
  (∀ b : Bool, ∃ a, (a,b) ∈ Left (prism H) p) ∧
  (∀ b : Bool, ∃ a, (a,b) ∈ Right (prism H) p)

lemma meets_layers (S : Set (V × Bool)) {a b : V × Bool}
    (ha : a ∈ S) (hb : b ∈ S) (hne : a.2 ≠ b.2) :
    ∀ c : Bool, ∃ v, (v,c) ∈ S := by
  intro c
  have he : c = a.2 ∨ c = b.2 := by
    cases ha : a.2 <;> cases hb : b.2 <;> cases c <;> simp_all
  rcases he with rfl | rfl
  · exact ⟨a.1,ha⟩
  · exact ⟨b.1,hb⟩

lemma bad_triangle_mixed {p q r : Biclique (prism H)}
    (hpq : (right (prism H)).Adj p q) (hpr : (right (prism H)).Adj p r)
    (hqr : (right (prism H)).Adj q r) (hn : ¬Good H p q) : Mixed H p := by
  let s := six (prism H) hpq hpr hqr
  have ht := s.tri (prism H)
  have ht' := s.tri' (prism H)
  have hb := triangle_layer H ht.1 ht.2.1 ht.2.2
  have hb' := triangle_layer H ht'.1 ht'.2.1 ht'.2.2
  have hne : s.x.2 ≠ s.x'.2 := by
    intro he
    apply hn
    refine ⟨s.x.2,⟨s.x.1,s.hx⟩,s.x'.1,?_⟩
    simpa only [layer,he] using s.hx'
  exact ⟨meets_layers _ s.hz.2 s.hx'.2 (hb.2 ▸ hne),
    meets_layers _ s.hx.1 s.hz'.1 (hb'.2 ▸ hne)⟩

def rect (e : Arc H) : Biclique (prism H) :=
  ⟨({(e.val.1,false),(e.val.2,true)}, {(e.val.2,false),(e.val.1,true)}),by
    intro a ha b hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact Or.inl ⟨rfl,e.property⟩
    · exact Or.inr ⟨rfl,by simp⟩
    · exact Or.inr ⟨rfl,by simp⟩
    · exact Or.inl ⟨rfl,e.property.symm⟩⟩

lemma mixed_rect {p : Biclique (prism H)} (hp : Mixed H p) :
    ∃ e : Arc H, p = rect H e := by
  obtain ⟨a,ha⟩ := hp.1 false
  obtain ⟨b,hb⟩ := hp.1 true
  obtain ⟨c,hc⟩ := hp.2 false
  obtain ⟨d,hd⟩ := hp.2 true
  have had : a = d := other_layer H (p.property _ ha _ hd) (by simp)
  have hbc : b = c := other_layer H (p.property _ hb _ hc) (by simp)
  subst c; subst d
  have hab : H.Adj a b := same_layer H (p.property _ ha _ hc) rfl
  refine ⟨⟨(a,b),hab⟩,Subtype.ext (Prod.ext ?_ ?_)⟩
  · ext v
    change v ∈ Left (prism H) p ↔ v = (a,false) ∨ v = (b,true)
    constructor
    · intro hv
      cases he : v.2
      · have hvv := other_layer H (p.property _ hv _ hd) (by simp [he])
        exact Or.inl (Prod.ext hvv he)
      · have hvv := other_layer H (p.property _ hv _ hc) (by simp [he])
        exact Or.inr (Prod.ext hvv he)
    · rintro (rfl | rfl) <;> assumption
  · ext v
    change v ∈ Right (prism H) p ↔ v = (b,false) ∨ v = (a,true)
    constructor
    · intro hv
      cases he : v.2
      · have hvv := other_layer H (p.property _ hb _ hv).symm (by simp [he])
        exact Or.inl (Prod.ext hvv he)
      · have hvv := other_layer H (p.property _ ha _ hv).symm (by simp [he])
        exact Or.inr (Prod.ext hvv he)
    · rintro (rfl | rfl) <;> assumption

lemma rect_adj {e f : Arc H} (hef : (right (prism H)).Adj (rect H e) (rect H f)) :
    (arcGraph H).Adj e f := by
  obtain ⟨v,hv,hv'⟩ := hef.1
  change (v = (e.val.2,false) ∨ v = (e.val.1,true)) at hv
  change (v = (f.val.1,false) ∨ v = (f.val.2,true)) at hv'
  rcases hv with rfl | rfl <;> rcases hv' with he | he
  · exact Or.inl (congrArg Prod.fst he)
  · exact (Bool.false_ne_true (congrArg Prod.snd he)).elim
  · exact Bool.noConfusion (congrArg Prod.snd he)
  · exact Or.inr (congrArg Prod.fst he).symm


def bad : SimpleGraph (Biclique (prism H)) where
  Adj p q := (right (prism H)).Adj p q ∧ ¬Good H p q
  symm := fun _ _ h => ⟨h.1.symm,fun ⟨b,hb⟩ => h.2 ⟨b,hb.symm⟩⟩
  loopless := fun _ h => (right (prism H)).loopless _ h.1

noncomputable def rectangleArc (p : Biclique (prism H)) (hp : Mixed H p) : Arc H :=
  (mixed_rect H hp).choose

lemma rectangleArc_spec (p : Biclique (prism H)) (hp : Mixed H p) :
    p = rect H (rectangleArc H p hp) := (mixed_rect H hp).choose_spec

lemma rectangleArc_adj {p q : Biclique (prism H)} (hp : Mixed H p) (hq : Mixed H q)
    (hpq : (right (prism H)).Adj p q) :
    (arcGraph H).Adj (rectangleArc H p hp) (rectangleArc H q hq) := by
  apply rect_adj H
  simpa only [← rectangleArc_spec] using hpq

lemma arc_cover : IsCountableUnionOfTriangleFree (arcGraph H) := by
  obtain ⟨J,K,hJ,hK,hcov⟩ := arc_two_cover H
  apply Erdos595CountableBadEdge.cover_of_countable_family (arcGraph H)
    (fun b : Bool => if b then J else K)
  · intro b
    cases b <;> simp only [Bool.false_eq_true,↓reduceIte] <;> assumption
  · intro a b hab
    rw [hcov,SimpleGraph.sup_adj] at hab
    rcases hab with h | h
    · exact ⟨true,h⟩
    · exact ⟨false,h⟩

lemma bad_cover : IsCountableUnionOfTriangleFree (bad H) := by
  classical
  obtain ⟨c,hc⟩ := (countable_union_iff_edge_coloring _).mp (arc_cover H)
  letI : LinearOrder (Biclique (prism H)) := IsWellOrder.linearOrder WellOrderingRel
  let code (p q : Biclique (prism H)) : ℕ :=
    if hp : Mixed H p then if hq : Mixed H q then
      c s(rectangleArc H p hp,rectangleArc H q hq) else 0 else 0
  apply Erdos595NegativeInner.cover_of_ordered_patterns (bad H) code
  intro p q r _ _ hpq hpr hqr hm
  have hp := bad_triangle_mixed H hpq.1 hpr.1 hqr.1 hpq.2
  have hq := bad_triangle_mixed H hpq.1.symm hqr.1 hpr.1
    (fun ⟨b,hb⟩ => hpq.2 ⟨b,hb.symm⟩)
  have hr := bad_triangle_mixed H hpr.1.symm hqr.1.symm hpq.1
    (fun ⟨b,hb⟩ => hpr.2 ⟨b,hb.symm⟩)
  simp only [code,dif_pos hp,dif_pos hq,dif_pos hr] at hm
  exact hc _ _ _ (rectangleArc_adj H hp hq hpq.1)
    (rectangleArc_adj H hp hr hpr.1) (rectangleArc_adj H hq hr hqr.1) hm

/-- No clique hypothesis is needed for this transfer. -/
theorem right_cover (hc : IsCountableUnionOfTriangleFree (right H)) :
    IsCountableUnionOfTriangleFree (right (prism H)) := by
  classical
  obtain ⟨J,hJ,hcov⟩ := hc
  obtain ⟨K,hK,hbad⟩ := bad_cover H
  let pieces : (Bool × ℕ) ⊕ ℕ → SimpleGraph (Biclique (prism H)) := fun i =>
    match i with
    | .inl (b,n) => (J n).comap (fun p => layer H p b)
    | .inr n => K n
  apply Erdos595CountableBadEdge.cover_of_countable_family _ pieces
  · intro i
    cases i with
    | inl i =>
      intro t ht
      obtain ⟨p,q,r,hpq,hpr,hqr,_⟩ := SimpleGraph.is3Clique_iff.mp ht
      exact hJ i.2 _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨hpq,hpr,hqr⟩)
    | inr n => exact hK n
  · intro p q hpq
    by_cases hg : Good H p q
    · obtain ⟨b,hb⟩ := hg
      rw [hcov,SimpleGraph.iSup_adj] at hb
      obtain ⟨n,hn⟩ := hb
      exact ⟨.inl (b,n),hn⟩
    · have hb : (bad H).Adj p q := ⟨hpq,hg⟩
      rw [hbad,SimpleGraph.iSup_adj] at hb
      obtain ⟨n,hn⟩ := hb
      exact ⟨.inr n,hn⟩

#print axioms triangle_layer
#print axioms mixed_rect
#print axioms bad_triangle_mixed
#print axioms bad_cover
#print axioms right_cover
end Erdos595CartesianBoolRight
