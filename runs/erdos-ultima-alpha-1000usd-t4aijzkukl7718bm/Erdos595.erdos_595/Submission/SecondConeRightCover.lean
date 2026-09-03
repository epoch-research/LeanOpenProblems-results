import Submission.RightProperTransversal

/-!
The second biclique right adjoint of a cone over a graph without closed
five-step walks is countably triangle-free edge-coverable. This is a
candidate exclusion, not a resolution of Erdős 595.
-/
set_option autoImplicit false
open Set SimpleGraph
namespace Erdos595SecondConeRight
open Erdos595Work Erdos595ArcAdjoint
variable {V : Type*} (G : SimpleGraph V)

/-- A homomorphic image of the five-cycle, with repetitions permitted. -/
def NoFive : Prop := ∀ a b c d e : V,
  G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d e → G.Adj e a → False

lemma triangleFree (h : NoFive G) : G.CliqueFree 3 := by
  classical
  intro s hs
  obtain ⟨a,b,c,hab,hac,hbc,_⟩ := SimpleGraph.is3Clique_iff.mp hs
  exact h a b a b c hab hab.symm hab hbc hac.symm

abbrev P := Biclique (coneGraph G)
def Pure (p : P G) : Prop := p.val.1 = {none} ∨ p.val.2 = {none}

def swap (p : P G) : P G := ⟨(p.val.2,p.val.1),fun _ ha _ hb => (p.property _ hb _ ha).symm⟩

lemma apex_of_triangle (h : NoFive G) {a b c : Option V}
    (hab : (coneGraph G).Adj a b) (hac : (coneGraph G).Adj a c)
    (hbc : (coneGraph G).Adj b c) : a = none ∨ b = none ∨ c = none := by
  cases a with
  | none => exact Or.inl rfl
  | some a =>
    cases b with
    | none => exact Or.inr (Or.inl rfl)
    | some b =>
      cases c with
      | none => exact Or.inr (Or.inr rfl)
      | some c => exact (h a b a b c hab hab.symm hab hbc hac.symm).elim

lemma extra {A : Set (Option V)} (ha : none ∈ A) (hn : A ≠ {none}) :
    ∃ a : V, some a ∈ A := by
  classical
  by_contra hh
  push_neg at hh
  apply hn
  ext x
  cases x <;> simp_all

/-- Normalize one of the two witness triangles to have its apex at p -> q. -/
lemma no_triangle_apex (h : NoFive G) (p q r : P G)
    (hp : ¬Pure G p) (hq : ¬Pure G q)
    (hpq : (right (coneGraph G)).Adj p q)
    (hpr : (right (coneGraph G)).Adj p r)
    (hqr : (right (coneGraph G)).Adj q r)
    (hpa : none ∈ p.val.2) (hqa : none ∈ q.val.1) : False := by
  obtain ⟨x,hxq,hxp⟩ := hpq.2
  obtain ⟨y,hyq,hyr⟩ := hqr.1
  obtain ⟨z,hzr,hzp⟩ := hpr.2
  obtain ⟨u,hur,huq⟩ := hqr.2
  obtain ⟨v,hvp,hvr⟩ := hpr.1
  have hxu : (coneGraph G).Adj x u := (q.property u huq x hxq).symm
  have hxv : (coneGraph G).Adj x v := p.property x hxp v hvp
  have huv : (coneGraph G).Adj u v := (r.property v hvr u hur).symm
  have hxn : x ≠ none := by
    intro he; subst x
    exact p.property none hxp none hpa
  have hyn : y ≠ none := by
    intro he; subst y
    exact q.property none hqa none hyq
  have hzn : z ≠ none := by
    intro he; subst z
    exact p.property none hzp none hpa
  rcases apex_of_triangle G h hxu hxv huv with hx | hu | hv
  · exact hxn hx
  · subst u
    obtain ⟨b,hb⟩ := extra hqa (fun he => hq (Or.inl he))
    have hvn : v ≠ none := by
      intro he; subst v
      exact r.property none hvr none hur
    cases x with
    | none => exact hxn rfl
    | some x =>
      cases y with
      | none => exact hyn rfl
      | some y =>
        cases z with
        | none => exact hzn rfl
        | some z =>
          cases v with
          | none => exact hvn rfl
          | some v =>
            exact h y z v x b (r.property _ hyr _ hzr)
              (p.property _ hzp _ hvp) hxv.symm
              (q.property _ hb _ hxq).symm (q.property _ hb _ hyq)
  · subst v
    obtain ⟨b,hb⟩ := extra hpa (fun he => hp (Or.inr he))
    have hun : u ≠ none := by
      intro he; subst u
      exact r.property none hvr none hur
    cases x with
    | none => exact hxn rfl
    | some x =>
      cases y with
      | none => exact hyn rfl
      | some y =>
        cases z with
        | none => exact hzn rfl
        | some z =>
          cases u with
          | none => exact hun rfl
          | some u =>
            exact h b x u y z (p.property _ hxp _ hb).symm hxu
              (q.property _ huq _ hyq) (r.property _ hyr _ hzr)
              (p.property _ hzp _ hb)

lemma pure_transversal (h : NoFive G) :
    ((right (coneGraph G)).induce {p | ¬Pure G p}).CliqueFree 3 := by
  classical
  intro s hs
  obtain ⟨p,q,r,hpq,hpr,hqr,_⟩ := SimpleGraph.is3Clique_iff.mp hs
  obtain ⟨x,hxp,hxq⟩ := hpq.1
  obtain ⟨y,hyq,hyr⟩ := hqr.1
  obtain ⟨z,hzr,hzp⟩ := hpr.2
  have hxy := q.val.property x hxq y hyq
  have hxz := (p.val.property z hzp x hxp).symm
  have hyz := r.val.property y hyr z hzr
  rcases apex_of_triangle G h hxy hxz hyz with hx | hy | hz
  · subst x
    exact no_triangle_apex G h p q r p.property q.property hpq hpr hqr hxp hxq
  · subst y
    exact no_triangle_apex G h q r p q.property r.property hqr hpq.symm hpr.symm hyq hyr
  · subst z
    exact no_triangle_apex G h r p q r.property p.property hpr.symm hqr.symm hpq hzr hzp

noncomputable def pureColor :
    ((right (coneGraph G)).induce {p | Pure G p}).Coloring Bool := by
  classical
  let c : {p // Pure G p} → Bool := fun p => decide (p.val.val.1 = {none})
  refine SimpleGraph.Coloring.mk c ?_
  intro p q hpq he
  change (right (coneGraph G)).Adj p.val q.val at hpq
  have heq : p.val.val.1 = {none} ↔ q.val.val.1 = {none} := decide_eq_decide.mp he
  obtain ⟨x,hxp,hxq⟩ := hpq.1
  by_cases hp : p.val.val.1 = {none}
  · have hq := heq.mp hp
    have hx : x = none := by simpa only [hq,Set.mem_singleton_iff] using hxq
    subst x
    have hpa : none ∈ p.val.val.1 := by simp [hp]
    exact p.val.property none hpa none hxp
  · have hq : q.val.val.1 ≠ {none} := fun h => hp (heq.mpr h)
    have hpB := p.property.resolve_left hp
    have hqB := q.property.resolve_left hq
    have hx : x = none := by simpa only [hpB,Set.mem_singleton_iff] using hxp
    subst x
    have hqb : none ∈ q.val.val.2 := by simp [hqB]
    exact q.val.property none hxq none hqb

/-- No cardinality bound on the base is required. -/
theorem countable_cover (h : NoFive G) :
    IsCountableUnionOfTriangleFree (right (right (coneGraph G))) := by
  apply Erdos595RightProperTransversal.countable_cover
    (C := Bool) (right (coneGraph G)) {p | Pure G p}
  · exact pure_transversal G h
  · exact pureColor G

#print axioms pure_transversal
#print axioms pureColor
#print axioms countable_cover
end Erdos595SecondConeRight
