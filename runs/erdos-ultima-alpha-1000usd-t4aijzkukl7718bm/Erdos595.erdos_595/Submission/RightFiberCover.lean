import Submission.TriangleFiberAdjoint
import Submission.NegativeInner
import Submission.ArcRoundTrip

/-!
Triangle-confined fibers preserve countable covering under the right adjoint,
even for arbitrarily many fibers. This closes the proposed cross-fiber gluing
route; it does not settle Erdős 595.
-/

open SimpleGraph Set
namespace Erdos595RightFiber
open Erdos595Work Erdos595ArcAdjoint Erdos595TriangleFiber

variable {V I : Type*}

/-- Restrict both biclique sides to one fiber, retaining an honest biclique
of the induced fiber graph. -/
def restrict (G : SimpleGraph V) (f : V → I) (i : I) (p : Biclique G) :
    Biclique (G.induce {a | f a = i}) :=
  ⟨({a | a.val ∈ p.1.1},{a | a.val ∈ p.1.2}), fun _ ha _ hb => p.2 _ ha _ hb⟩

lemma restrict_adj (G : SimpleGraph V) (f : V → I) (i : I)
    {p q : Biclique G} (h : (right G).Adj p q)
    (h₁ : f h.1.choose = i) (h₂ : f h.2.choose = i) :
    (right (G.induce {a | f a = i})).Adj (restrict G f i p) (restrict G f i q) :=
  ⟨⟨⟨h.1.choose,h₁⟩,h.1.choose_spec⟩,⟨⟨h.2.choose,h₂⟩,h.2.choose_spec⟩⟩

/-- The six witnesses around a right-adjoint triangle form two base triangles,
so their fiber labels occur in two consistently oriented triples. -/
lemma witness_fibers (G : SimpleGraph V) (f : V → I) (hf : TrianglesInFibers G f)
    {p q r : Biclique G} (hpq : (right G).Adj p q) (hpr : (right G).Adj p r)
    (hqr : (right G).Adj q r) :
    (f hpq.1.choose = f hpr.2.choose ∧ f hpq.1.choose = f hqr.1.choose) ∧
    (f hpq.2.choose = f hpr.1.choose ∧ f hpq.2.choose = f hqr.2.choose) := by
  have h₁ := hpq.1.choose_spec
  have h₂ := hpq.2.choose_spec
  have h₃ := hpr.1.choose_spec
  have h₄ := hpr.2.choose_spec
  have h₅ := hqr.1.choose_spec
  have h₆ := hqr.2.choose_spec
  exact ⟨hf _ _ _ (p.2 _ h₄.2 _ h₁.1).symm
      (q.2 _ h₁.2 _ h₅.1) (r.2 _ h₅.2 _ h₄.1).symm,
    hf _ _ _ (p.2 _ h₂.2 _ h₃.1)
      (q.2 _ h₆.2 _ h₂.1).symm (r.2 _ h₃.2 _ h₆.1)⟩

/-- No bound on the number of fibers is needed. Covers of their right
adjoints combine into a countable cover of the whole right adjoint. -/
theorem cover_of_fibers (G : SimpleGraph V) (f : V → I)
    (hf : TrianglesInFibers G f)
    (hG : ∀ i, IsCountableUnionOfTriangleFree (right (G.induce {a | f a = i}))) :
    IsCountableUnionOfTriangleFree (right G) := by
  classical
  letI : LinearOrder I := IsWellOrder.linearOrder WellOrderingRel
  letI : LinearOrder (Biclique G) := IsWellOrder.linearOrder WellOrderingRel
  choose col hcol using fun i => (countable_union_iff_edge_coloring _).mp (hG i)
  let code (p q : Biclique G) : ℕ ⊕ Bool :=
    if h : (right G).Adj p q then
      if f h.1.choose = f h.2.choose then
        Sum.inl (col (f h.1.choose)
          s(restrict G f (f h.1.choose) p,restrict G f (f h.1.choose) q))
      else Sum.inr (decide (f h.1.choose < f h.2.choose))
    else Sum.inr false
  apply Erdos595NegativeInner.cover_of_ordered_patterns (right G) code
  intro p q r _ _ hpq hpr hqr he
  obtain ⟨⟨h₁,h₂⟩,⟨h₃,h₄⟩⟩ := witness_fibers G f hf hpq hpr hqr
  simp only [code, dif_pos hpq, dif_pos hpr, dif_pos hqr] at he
  rw [← h₁, ← h₂, ← h₃, ← h₄] at he
  by_cases hab : f hpq.1.choose = f hpq.2.choose
  · rw [← hab] at he
    simp only [ite_true, Sum.inl.injEq] at he
    apply hcol (f hpq.1.choose) (restrict G f _ p) (restrict G f _ q) (restrict G f _ r)
      (restrict_adj G f _ hpq rfl hab.symm)
      (restrict_adj G f _ hpr (h₃.symm.trans hab.symm) h₁.symm)
      (restrict_adj G f _ hqr h₂.symm (h₄.symm.trans hab.symm))
    exact he
  · have hba : f hpq.2.choose ≠ f hpq.1.choose := Ne.symm hab
    rcases lt_or_gt_of_ne hab with hlt | hgt
    · simp [hab, hba, hlt, not_lt_of_gt hlt] at he
    · simp [hab, hba, hgt, not_lt_of_gt hgt] at he

/-- A local copy of right-adjoint functoriality. -/
noncomputable def rightHom {W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (F : G →g H) : right G →g right H :=
  toRight (F.comp (fromRight (SimpleGraph.Hom.id)))

/-- Consequently the cross-fiber gluing construction cannot destroy
coverability of the right adjoint. -/
theorem right_glue_cover {C : Type*} (H : SimpleGraph V) (B : SimpleGraph I) (c : V → C)
    (hc : ∀ a b, H.Adj a b → c a ≠ c b) (hB : B.CliqueFree 3)
    (hH : IsCountableUnionOfTriangleFree (right H)) :
    IsCountableUnionOfTriangleFree (right (glue H B c)) := by
  apply cover_of_fibers _ Prod.snd (glue_triangles H B c hc hB)
  intro i
  let F : (glue H B c).induce {p | p.2 = i} →g H :=
    { toFun p := p.1.1
      map_rel' := by
        intro p q hpq
        exact glue_same_fiber H B c (p.2.trans q.2.symm) hpq }
  exact countable_union_of_hom (rightHom F) hH

/-- In particular, gluing arc graphs by source color gives no amplification
of a coverable original graph, regardless of the size of the triangle-free
index graph B or its ordinary chromatic number. -/
theorem right_arcSourceGlue_cover (R : SimpleGraph V) (B : SimpleGraph I)
    (hB : B.CliqueFree 3) (hR : IsCountableUnionOfTriangleFree R) :
    IsCountableUnionOfTriangleFree (right (arcSourceGlue R B)) :=
  right_glue_cover _ B _ (fun _ _ h => ((sourceHom R).map_adj h).ne) hB
    (Erdos595ArcRoundTrip.right_arc_cover R hR)

theorem right_arcSourceGlue_shift_cover (A : Type*) [LinearOrder A]
    (B : SimpleGraph I) (hB : B.CliqueFree 3) :
    IsCountableUnionOfTriangleFree
      (right (arcSourceGlue (Erdos595MiddleCorner.graph A) B)) :=
  right_arcSourceGlue_cover _ B hB (Erdos595MiddleCorner.graph_cover A)

#print axioms right_arcSourceGlue_cover
#print axioms right_arcSourceGlue_shift_cover
#print axioms witness_fibers
#print axioms cover_of_fibers
#print axioms right_glue_cover
end Erdos595RightFiber
