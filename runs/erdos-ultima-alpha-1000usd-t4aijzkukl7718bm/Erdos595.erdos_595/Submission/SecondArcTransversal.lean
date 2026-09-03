import Submission.RightProperTransversal

/-!
An independent set meets every triangle of every second arc graph. This
therefore maps the second arc graph into a single cone over a triangle-free
base, but that base can have a five-cycle even for a K4-free source.
-/
set_option autoImplicit false
open Set SimpleGraph
namespace Erdos595SecondArcTransversal
open Erdos595ArcAdjoint Erdos595Work
variable {V : Type*} [LinearOrder V] (G : SimpleGraph V)

/-- Select a forward local minimum or a backward local maximum. -/
def Selected (p : Arc (arcGraph G)) : Prop :=
  (p.val.1.val.2 = p.val.2.val.1 ∧ p.val.1.val.2 < p.val.1.val.1 ∧
    p.val.1.val.2 < p.val.2.val.2) ∨
  (p.val.2.val.2 = p.val.1.val.1 ∧ p.val.2.val.2 > p.val.1.val.2 ∧
    p.val.2.val.2 > p.val.2.val.1)

lemma independent {p q : Arc (arcGraph G)} (hp : Selected G p) (hq : Selected G q) :
    ¬(arcGraph (arcGraph G)).Adj p q := by
  intro hpq
  rcases hpq with he | he
  all_goals
    have h₁ := congrArg (fun e : Arc G => e.val.1) he
    have h₂ := congrArg (fun e : Arc G => e.val.2) he
    rcases hp with ⟨hp₁,hp₂,hp₃⟩ | ⟨hp₁,hp₂,hp₃⟩ <;>
      rcases hq with ⟨hq₁,hq₂,hq₃⟩ | ⟨hq₁,hq₂,hq₃⟩ <;> order

lemma cycle_selected (e f g : Arc G)
    (hef : (arcGraph G).Adj e f) (heg : (arcGraph G).Adj e g)
    (hfg : (arcGraph G).Adj f g) :
    Selected G ⟨(e,f),hef⟩ ∨ Selected G ⟨(f,g),hfg⟩ ∨ Selected G ⟨(g,e),heg.symm⟩ := by
  have he := e.property.ne
  have hf := f.property.ne
  have hg := g.property.ne
  rcases arc_triangle hef heg hfg with ⟨h₁,h₂,h₃⟩ | ⟨h₁,h₂,h₃⟩
  all_goals
    simp only [Selected]
    rcases lt_or_gt_of_ne he with he | he <;>
      rcases lt_or_gt_of_ne hf with hf | hf <;>
      rcases lt_or_gt_of_ne hg with hg | hg <;> aesop (add safe (by order))

lemma triangle_hit {p q r : Arc (arcGraph G)}
    (hpq : (arcGraph (arcGraph G)).Adj p q)
    (hpr : (arcGraph (arcGraph G)).Adj p r)
    (hqr : (arcGraph (arcGraph G)).Adj q r) :
    Selected G p ∨ Selected G q ∨ Selected G r := by
  rcases arc_triangle hpq hpr hqr with ⟨h₁,h₂,h₃⟩ | ⟨h₁,h₂,h₃⟩
  · have he : (arcGraph G).Adj p.val.1 p.val.2 := p.property
    have hf : (arcGraph G).Adj p.val.2 q.val.2 := h₁.symm ▸ q.property
    have hg : (arcGraph G).Adj q.val.2 p.val.1 := h₂.symm ▸ h₃ ▸ r.property
    have hh := cycle_selected G p.val.1 p.val.2 q.val.2 he hg.symm hf
    have eqQ : (⟨(p.val.2,q.val.2),hf⟩ : Arc (arcGraph G)) = q :=
      Subtype.ext (Prod.ext h₁ rfl)
    have eqR : (⟨(q.val.2,p.val.1),hg⟩ : Arc (arcGraph G)) = r :=
      Subtype.ext (Prod.ext h₂ h₃.symm)
    simpa only [eqQ,eqR] using hh
  · have he : (arcGraph G).Adj q.val.1 q.val.2 := q.property
    have hf : (arcGraph G).Adj q.val.2 p.val.2 := h₁.symm ▸ p.property
    have hg : (arcGraph G).Adj p.val.2 q.val.1 := h₂.symm ▸ h₃ ▸ r.property
    have hh := cycle_selected G q.val.1 q.val.2 p.val.2 he hg.symm hf
    have eqP : (⟨(q.val.2,p.val.2),hf⟩ : Arc (arcGraph G)) = p :=
      Subtype.ext (Prod.ext h₁ rfl)
    have eqR : (⟨(p.val.2,q.val.1),hg⟩ : Arc (arcGraph G)) = r :=
      Subtype.ext (Prod.ext h₂ h₃.symm)
    rw [eqP,eqR] at hh
    tauto

abbrev Base := (arcGraph (arcGraph G)).induce {p | ¬Selected G p}
lemma base_triangleFree : (Base G).CliqueFree 3 := by
  classical
  intro s hs
  obtain ⟨p,q,r,hpq,hpr,hqr,_⟩ := SimpleGraph.is3Clique_iff.mp hs
  exact (triangle_hit G hpq hpr hqr).elim p.property (fun h => h.elim q.property r.property)

noncomputable def intoCone : arcGraph (arcGraph G) →g coneGraph (Base G) := by
  classical
  refine ⟨fun p => if hp : Selected G p then none else some ⟨p,hp⟩,?_⟩
  intro p q hpq
  dsimp only
  split_ifs with hp hq
  · exact (independent G hp hq hpq).elim
  · trivial
  · trivial
  · exact hpq

/-- Every graph maps to the second right adjoint of SOME single cone.
No K4-freeness assertion about that full right adjoint follows. -/
noncomputable def intoSecondRight : G →g right (right (coneGraph (Base G))) :=
  toRight (toRight (intoCone G))

/-- The first right adjoint of a second arc graph has a TWO-piece edge
cover, uniformly in the source graph and without a clique hypothesis. -/
theorem right_second_arc_two_cover :
    ∃ K L : SimpleGraph (Biclique (arcGraph (arcGraph G))),
      K.CliqueFree 3 ∧ L.CliqueFree 3 ∧ right (arcGraph (arcGraph G)) = K ⊔ L := by
  apply Erdos595RightProperTransversal.independent_two_cover
    (arcGraph (arcGraph G)) {p | Selected G p}
  · exact base_triangleFree G
  · intro p hp q hq
    exact independent G hp hq

#print axioms right_second_arc_two_cover
#print axioms independent
#print axioms triangle_hit
#print axioms base_triangleFree
#print axioms intoSecondRight
end Erdos595SecondArcTransversal
