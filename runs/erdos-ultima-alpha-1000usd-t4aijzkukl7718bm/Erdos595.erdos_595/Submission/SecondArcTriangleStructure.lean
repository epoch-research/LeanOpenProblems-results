import Submission.SecondArcReflection

/-!
Triangles of a second symmetrized arc graph are vertex-disjoint. Combined
with the exact two-step K4 reflection, this restricts the base graphs needed
in the second-right-adjoint normal form of Erdős 595.
-/
set_option autoImplicit false
open SimpleGraph Set
namespace Erdos595SecondArcTriangleStructure
open Erdos595ArcAdjoint Erdos595ArcRoundTrip

variable {V : Type*} (G : SimpleGraph V)

/-- Any two triangles through a vertex have the same two other vertices. -/
def VertexDisjointTriangles : Prop :=
  ∀ ⦃a b c d e : V⦄, G.Adj a b → G.Adj a c → G.Adj b c →
    G.Adj a d → G.Adj a e → G.Adj d e →
    (b = d ∧ c = e) ∨ (b = e ∧ c = d)

private lemma triangle_form {p q r : Arc G} (hpq : (arcGraph G).Adj p q)
    (hpr : (arcGraph G).Adj p r) (hqr : (arcGraph G).Adj q r) :
    ∃ w, G.Adj p.val.1 w ∧ G.Adj p.val.2 w ∧
      ((q.val.1 = p.val.2 ∧ q.val.2 = w ∧ r.val.1 = w ∧ r.val.2 = p.val.1) ∨
       (q.val.1 = w ∧ q.val.2 = p.val.1 ∧ r.val.1 = p.val.2 ∧ r.val.2 = w)) := by
  rcases arc_triangle hpq hpr hqr with ⟨h₁,h₂,h₃⟩ | ⟨h₁,h₂,h₃⟩
  · refine ⟨q.val.2,?_,?_,Or.inl ⟨h₁.symm,rfl,h₂.symm,h₃⟩⟩
    · exact h₃ ▸ h₂.symm ▸ r.property.symm
    · exact h₁.symm ▸ q.property
  · refine ⟨q.val.1,?_,?_,Or.inr ⟨rfl,h₁,h₂.symm,h₃⟩⟩
    · exact h₁ ▸ q.property.symm
    · exact h₂.symm ▸ h₃ ▸ r.property

/-- At the next arc stage, uniqueness through an edge becomes uniqueness
through a vertex. -/
theorem arc_vertex_disjoint (hG : UniqueTriangleEdge G) :
    VertexDisjointTriangles (arcGraph G) := by
  intro p q r s t hpq hpr hqr hps hpt hst
  obtain ⟨w,hw₁,hw₂,hw⟩ := triangle_form G hpq hpr hqr
  obtain ⟨z,hz₁,hz₂,hz⟩ := triangle_form G hps hpt hst
  have hwz := hG p.property hw₁ hw₂ hz₁ hz₂
  subst z
  rcases hw with ⟨hq₁,hq₂,hr₁,hr₂⟩ | ⟨hq₁,hq₂,hr₁,hr₂⟩ <;>
    rcases hz with ⟨hs₁,hs₂,ht₁,ht₂⟩ | ⟨hs₁,hs₂,ht₁,ht₂⟩
  · exact Or.inl ⟨Subtype.ext (Prod.ext (hq₁.trans hs₁.symm) (hq₂.trans hs₂.symm)),
      Subtype.ext (Prod.ext (hr₁.trans ht₁.symm) (hr₂.trans ht₂.symm))⟩
  · exact Or.inr ⟨Subtype.ext (Prod.ext (hq₁.trans ht₁.symm) (hq₂.trans ht₂.symm)),
      Subtype.ext (Prod.ext (hr₁.trans hs₁.symm) (hr₂.trans hs₂.symm))⟩
  · exact Or.inr ⟨Subtype.ext (Prod.ext (hq₁.trans ht₁.symm) (hq₂.trans ht₂.symm)),
      Subtype.ext (Prod.ext (hr₁.trans hs₁.symm) (hr₂.trans hs₂.symm))⟩
  · exact Or.inl ⟨Subtype.ext (Prod.ext (hq₁.trans hs₁.symm) (hq₂.trans hs₂.symm)),
      Subtype.ext (Prod.ext (hr₁.trans ht₁.symm) (hr₂.trans ht₂.symm))⟩

theorem second_arc_vertex_disjoint :
    VertexDisjointTriangles (arcGraph (arcGraph G)) :=
  arc_vertex_disjoint (arcGraph G) (arc_unique_triangle_edge G)

#print axioms arc_vertex_disjoint
#print axioms second_arc_vertex_disjoint
end Erdos595SecondArcTriangleStructure
