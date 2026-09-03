import Submission.FiniteTransversalRightCover

/-! An exclusion for partial matching candidates with separated third vertices.
This does not settle Erdős 595. -/
set_option autoImplicit false
open SimpleGraph Set
namespace Erdos595SplitTriangleRight
open Erdos595ArcAdjoint Erdos595Work Erdos595RightProperTransversal
variable {I : Type*} (D : I → I → Prop) (R : SimpleGraph I)

/-- Arbitrary A--B edges, a private A_i B_i C_i triangle, and R on the C vertices. -/
def graph : SimpleGraph (I × Fin 3) where
  Adj x y :=
    match x.2,y.2 with
    | 0,0 => False
    | 0,1 => x.1 = y.1 ∨ D x.1 y.1
    | 0,2 => x.1 = y.1
    | 1,0 => x.1 = y.1 ∨ D y.1 x.1
    | 1,1 => False
    | 1,2 => x.1 = y.1
    | 2,0 => x.1 = y.1
    | 2,1 => x.1 = y.1
    | 2,2 => R.Adj x.1 y.1
  symm := by
    rintro ⟨i,a⟩ ⟨j,b⟩ h
    fin_cases a <;> fin_cases b <;> simp_all [eq_comm, R.adj_comm]
  loopless := by
    rintro ⟨i,a⟩ h
    fin_cases a <;> simp_all

abbrev P := Biclique (graph D R)

def side (p : P D R) (b : Bool) : Set (I × Fin 3) :=
  if b then p.val.1 else p.val.2

def Good (p : P D R) (k : Bool × Bool) : Prop :=
  (side D R p k.1).Nonempty ∧
    ∀ x ∈ side D R p k.1, x.2 = if k.2 then 1 else 0

def Selected (p : P D R) : Prop := ∃ k, Good D R p k

lemma same_first {i j : I} (b : Bool) :
    ¬(graph D R).Adj (i,if b then 1 else 0) (j,if b then 1 else 0) := by
  cases b <;> simp [graph]

lemma good_independent (p q : P D R) (k : Bool × Bool)
    (hp : Good D R p k) (hq : Good D R q k) : ¬(right (graph D R)).Adj p q := by
  intro hpq
  rcases k with ⟨s,t⟩
  cases s
  · obtain ⟨a,ha⟩ := hp.1
    obtain ⟨b,hbq,hbp⟩ := hpq.2
    have ha' := hp.2 a ha
    have hb' := hq.2 b hbq
    have hh := p.property b hbp a ha
    obtain ⟨i,a⟩ := a
    obtain ⟨j,b⟩ := b
    change a = _ at ha'
    change b = _ at hb'
    subst a; subst b
    exact same_first D R t hh
  · obtain ⟨a,ha⟩ := hp.1
    obtain ⟨b,hbp,hbq⟩ := hpq.1
    have ha' := hp.2 a ha
    have hb' := hq.2 b hbq
    have hh := p.property a ha b hbp
    obtain ⟨i,a⟩ := a
    obtain ⟨j,b⟩ := b
    change a = _ at ha'
    change b = _ at hb'
    subst a; subst b
    exact same_first D R t hh

noncomputable def selectedColor :
    ((right (graph D R)).induce (Selected D R)).Coloring (Bool × Bool) :=
  SimpleGraph.Coloring.mk (fun p => p.property.choose) (by
    intro p q hpq he
    apply good_independent D R p.val q.val p.property.choose p.property.choose_spec
    · change p.property.choose = q.property.choose at he
      rw [he]
      exact q.property.choose_spec
    · exact hpq)

lemma left_shape (p : P D R) (i : I) (hb : (i,1) ∈ p.val.2)
    {x : I × Fin 3} (hx : x ∈ p.val.1) : x.2 = 0 ∨ x = (i,2) := by
  have h := p.property x hx (i,1) hb
  obtain ⟨j,a⟩ := x
  fin_cases a <;> simp_all [graph]

lemma right_shape (p : P D R) (i : I) (ha : (i,0) ∈ p.val.1)
    {x : I × Fin 3} (hx : x ∈ p.val.2) : x.2 = 1 ∨ x = (i,2) := by
  have h := p.property (i,0) ha x hx
  obtain ⟨j,a⟩ := x
  fin_cases a <;> simp_all [graph]

lemma selected_of_AB (p : P D R) (i : I)
    (ha : (i,0) ∈ p.val.1) (hb : (i,1) ∈ p.val.2) : Selected D R p := by
  classical
  by_cases hc : (i,2) ∈ p.val.1
  · refine ⟨(false,true),⟨⟨(i,1),hb⟩,?_⟩⟩
    intro x hx
    rcases right_shape D R p i ha hx with he | he
    · exact he
    · subst x
      exact ((p.property (i,2) hc (i,2) hx).ne rfl).elim
  · refine ⟨(true,false),⟨⟨(i,0),ha⟩,?_⟩⟩
    intro x hx
    rcases left_shape D R p i hb hx with he | he
    · exact he
    · exact (hc (he ▸ hx)).elim

lemma selected_of_BA (p : P D R) (i : I)
    (hb : (i,1) ∈ p.val.1) (ha : (i,0) ∈ p.val.2) : Selected D R p := by
  let q : P D R := ⟨(p.val.2,p.val.1),fun _ hx _ hy => (p.property _ hy _ hx).symm⟩
  obtain ⟨⟨s,t⟩,hq⟩ := selected_of_AB D R q i ha hb
  refine ⟨(!s,t),?_⟩
  cases s <;> exact hq

lemma triangle_AB (hR : R.CliqueFree 3) {x y z : I × Fin 3}
    (hxy : (graph D R).Adj x y) (hxz : (graph D R).Adj x z)
    (hyz : (graph D R).Adj y z) :
    (∃ i, x = (i,0) ∧ y = (i,1)) ∨
    (∃ i, x = (i,1) ∧ y = (i,0)) ∨
    (∃ i, x = (i,0) ∧ z = (i,1)) ∨
    (∃ i, x = (i,1) ∧ z = (i,0)) ∨
    (∃ i, y = (i,0) ∧ z = (i,1)) ∨
    (∃ i, y = (i,1) ∧ z = (i,0)) := by
  classical
  obtain ⟨i,a⟩ := x
  obtain ⟨j,b⟩ := y
  obtain ⟨k,c⟩ := z
  fin_cases a <;> fin_cases b <;> fin_cases c <;> simp_all [graph]
  all_goals first
    | aesop
    | exact (hR _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨hxy,hxz,hyz⟩)).elim

lemma selected_transversal (hR : R.CliqueFree 3) :
    ((right (graph D R)).induce (Selected D R)ᶜ).CliqueFree 3 := by
  classical
  intro t ht
  obtain ⟨p,q,r,hpq,hpr,hqr,_⟩ := SimpleGraph.is3Clique_iff.mp ht
  obtain ⟨x,hxp,hxq⟩ := hpq.1
  obtain ⟨y,hyq,hyr⟩ := hqr.1
  obtain ⟨z,hzr,hzp⟩ := hpr.2
  have hxy := q.val.property x hxq y hyq
  have hxz := (p.val.property z hzp x hxp).symm
  have hyz := r.val.property y hyr z hzr
  rcases triangle_AB D R hR hxy hxz hyz with
    ⟨i,rfl,rfl⟩ | ⟨i,rfl,rfl⟩ | ⟨i,rfl,rfl⟩ |
    ⟨i,rfl,rfl⟩ | ⟨i,rfl,rfl⟩ | ⟨i,rfl,rfl⟩
  · exact q.property (selected_of_AB D R q.val i hxq hyq)
  · exact q.property (selected_of_BA D R q.val i hxq hyq)
  · exact p.property (selected_of_BA D R p.val i hzp hxp)
  · exact p.property (selected_of_AB D R p.val i hzp hxp)
  · exact r.property (selected_of_AB D R r.val i hyr hzr)
  · exact r.property (selected_of_BA D R r.val i hyr hzr)

/-- No K4 hypothesis is required on either right stage. -/
theorem five_cover (hR : R.CliqueFree 3) :
    Erdos595CompleteFilterEdgeCover.CoversWith (right (right (graph D R))) 5 := by
  classical
  let e : (Bool × Bool) ≃ Fin 4 := (Fintype.equivFin _).trans (finCongr (by decide))
  let c := ((right (graph D R)).induce (Selected D R)).recolorOfEquiv e (selectedColor D R)
  exact Erdos595FiniteTransversalRight.finite_cover (right (graph D R))
    (Selected D R) (selected_transversal D R hR) c

theorem countable_cover (hR : R.CliqueFree 3) :
    IsCountableUnionOfTriangleFree (right (right (graph D R))) :=
  Erdos595RightProperTransversal.countable_cover (right (graph D R))
    (Selected D R) (selected_transversal D R hR) (selectedColor D R)

#print axioms five_cover
#print axioms countable_cover
end Erdos595SplitTriangleRight
