import Submission.OrderedQuadShapes
import Submission.NoPrismFinitePalette

/-!
A uniform finite triangle-avoiding edge palette for the ordered-quadruple
right adjoint. This excludes this candidate as a witness to Erdős 595.
-/
set_option autoImplicit false
open SimpleGraph Set
namespace Erdos595OrderedQuadRight
open Erdos595ArcAdjoint Erdos595MatchingBundle
variable {A : Type*} [LinearOrder A]

def FirstStar (p : Biclique (graph A)) : Prop :=
  (∀ a ∈ p.val.1, ∀ b ∈ p.val.1, a 0 = b 0) ∨
  (∀ a ∈ p.val.2, ∀ b ∈ p.val.2, a 0 = b 0)

theorem mixed_firstStar {p q r : Biclique (graph A)}
    (s : Six (graph A) p q r) (k : Fin 6)
    (h : Pattern k s.x s.x') (j : Pattern k s.z' s.z)
    (l : Pattern k s.y s.y') :
    ¬FirstStar q ∧ (FirstStar p ∨ FirstStar r) := by
  let v : Fin 6 → Quad A := ![s.x,s.y,s.z,s.x',s.y',s.z']
  have t := s.tri (graph A)
  have u := s.tri' (graph A)
  obtain ⟨hne,hne',hs⟩ := mono_shape v k
    (triangle_options t.1 t.2.1 t.2.2) (triangle_options u.1 u.2.1 u.2.2) h j l
  constructor
  · rintro (hc | hc)
    · exact hne (hc s.x s.hx.2 s.y' s.hy'.2)
    · exact hne' (hc s.y s.hy.1 s.x' s.hx'.1)
  · rcases hs with hs | hs | hs | hs
    · right; right
      intro a ha b hb
      exact (slide_common_first hs (r.property _ s.hy.2 _ ha)
        (r.property _ s.hz'.2 _ ha)).trans
        (slide_common_first hs (r.property _ s.hy.2 _ hb)
          (r.property _ s.hz'.2 _ hb)).symm
    · right; left
      intro a ha b hb
      exact (slide_common_first hs (r.property _ ha _ s.hy'.1).symm
        (r.property _ ha _ s.hz.1).symm).trans
        (slide_common_first hs (r.property _ hb _ s.hy'.1).symm
          (r.property _ hb _ s.hz.1).symm).symm
    · left; left
      intro a ha b hb
      exact (slide_common_first hs (p.property _ ha _ s.hx.1).symm
        (p.property _ ha _ s.hz'.1).symm).trans
        (slide_common_first hs (p.property _ hb _ s.hx.1).symm
          (p.property _ hb _ s.hz'.1).symm).symm
    · left; right
      intro a ha b hb
      exact (slide_common_first hs (p.property _ s.hx'.2 _ ha)
        (p.property _ s.hz.2 _ ha)).trans
        (slide_common_first hs (p.property _ s.hx'.2 _ hb)
          (p.property _ s.hz.2 _ hb)).symm

abbrev Palette := (Fin 6 → Bool) × Bool × Bool

theorem palette_card : Fintype.card Palette = 256 := by simp [Palette]

noncomputable def edgeCode (p q : Biclique (graph A)) : Palette := by
  classical
  exact if h : (right (graph A)).Adj p q then
    (fun k => decide (Pattern k h.1.choose h.2.choose),
      decide (FirstStar p),decide (FirstStar q))
    else (fun _ => false,false,false)

/-- The same finite palette works over every linearly ordered carrier. -/
theorem right_finite_cover : Erdos595FinitePalette.HasColoring (right (graph A)) Palette := by
  classical
  letI : LinearOrder (Biclique (graph A)) := IsWellOrder.linearOrder WellOrderingRel
  apply Erdos595SmallMarkedFinitePalette.of_ordered_patterns (right (graph A)) edgeCode
  intro p q r _ _ hpq hpr hqr he
  simp only [edgeCode,dif_pos hpq,dif_pos hpr,dif_pos hqr] at he
  have hcode₁ := congrArg Prod.fst he.1
  have hcode₂ := congrArg Prod.fst he.2
  have hpqFlag := congrArg (fun z : Palette => z.2.1) he.2
  have hqrFlag := congrArg (fun z : Palette => z.2.2) he.1
  have hx : Adj hpq.1.choose hpq.2.choose :=
    q.property _ hpq.1.choose_spec.2 _ hpq.2.choose_spec.1
  obtain ⟨k,hk⟩ := pattern_exists hx
  have hj : Pattern k hpr.1.choose hpr.2.choose :=
    of_decide_eq_true ((congrFun hcode₁ k).symm.trans (decide_eq_true hk))
  have hl : Pattern k hqr.1.choose hqr.2.choose :=
    of_decide_eq_true ((congrFun hcode₂ k).symm.trans (decide_eq_true hk))
  obtain ⟨hn,hp | hr⟩ := mixed_firstStar (six (graph A) hpq hpr hqr) k hk hj hl
  · exact hn ((decide_eq_decide.mp hpqFlag).mp hp)
  · exact hn ((decide_eq_decide.mp hqrFlag).mpr hr)

theorem right_countable_cover : Erdos595Work.IsCountableUnionOfTriangleFree (right (graph A)) :=
  right_finite_cover.countable_cover

/-- A fixed finite Folkman obstruction rules out universality of this
entire ordered-template family, not merely one chosen carrier. -/
theorem finite_representation_failure :
    ∃ (V : Type) (_ : Finite V) (G : SimpleGraph V), G.CliqueFree 4 ∧
      ∀ (A : Type) (_ : LinearOrder A),
        ¬Nonempty (arcGraph G →g graph A) := by
  obtain ⟨V,hV,G,hG,hbad⟩ := Erdos595FiniteFolkman.finite_folkman Palette
  refine ⟨V,hV,G,hG,?_⟩
  intro A oA hf
  letI : LinearOrder A := oA
  obtain ⟨f⟩ := hf
  exact hbad (right_finite_cover.comap (toRight f))

#print axioms finite_representation_failure
#print axioms mixed_firstStar
#print axioms right_finite_cover
#print axioms right_countable_cover
end Erdos595OrderedQuadRight
