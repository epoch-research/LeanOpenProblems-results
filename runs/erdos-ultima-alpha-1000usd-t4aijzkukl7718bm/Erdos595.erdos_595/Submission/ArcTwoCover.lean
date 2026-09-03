import Submission.ArcAdjoint

/-!
The arc construction is K4-free, but always has a two-piece triangle-free
edge cover. This prevents treating the arc graph alone as a witness.
-/
set_option autoImplicit false
open SimpleGraph Set
namespace Erdos595ArcAdjoint
variable {V : Type*}

private theorem triangle_orientation [LinearOrder V] (G : SimpleGraph V)
    (p q r : Arc G) (hpq : (arcGraph G).Adj p q)
    (hpr : (arcGraph G).Adj p r) (hqr : (arcGraph G).Adj q r) :
    ¬((decide (p.1.1 < p.1.2) = decide (q.1.1 < q.1.2)) ∧
      (decide (p.1.1 < p.1.2) = decide (r.1.1 < r.1.2))) := by
  intro he
  have hpne := p.2.ne
  have hqne := q.2.ne
  have hrne := r.2.ne
  have ht := arc_triangle hpq hpr hqr
  by_cases hp : p.1.1 < p.1.2 <;>
    by_cases hq : q.1.1 < q.1.2 <;>
    by_cases hr : r.1.1 < r.1.2 <;>
    simp only [hp, hq, hr, decide_true, decide_false, Bool.true_eq_false,
      Bool.false_eq_true, false_and, and_false] at he
  all_goals rcases ht with ⟨h1,h2,h3⟩ | ⟨h1,h2,h3⟩ <;> order

/-- Orienting arcs by any vertex order splits their triangles between two
vertex classes; cut edges form one piece and within-class edges the other. -/
theorem arc_two_cover (G : SimpleGraph V) :
    ∃ H K : SimpleGraph (Arc G), H.CliqueFree 3 ∧ K.CliqueFree 3 ∧
      arcGraph G = H ⊔ K := by
  classical
  letI : LinearOrder V := IsWellOrder.linearOrder WellOrderingRel
  let c : Arc G → Bool := fun p => decide (p.1.1 < p.1.2)
  let H : SimpleGraph (Arc G) :=
    { Adj p q := (arcGraph G).Adj p q ∧ c p ≠ c q
      symm := fun _ _ h => ⟨h.1.symm, h.2.symm⟩
      loopless := fun _ h => h.2 rfl }
  let K : SimpleGraph (Arc G) :=
    { Adj p q := (arcGraph G).Adj p q ∧ c p = c q
      symm := fun _ _ h => ⟨h.1.symm, h.2.symm⟩
      loopless := fun p h => (arcGraph G).loopless p h.1 }
  refine ⟨H, K, ?_, ?_, ?_⟩
  · have hc : H.Colorable 2 := by
      have cf : H.Coloring Bool := SimpleGraph.Coloring.mk c (fun h => h.2)
      simpa using cf.colorable
    exact hc.cliqueFree (by omega)
  · intro t ht
    obtain ⟨p,q,r,hpq,hpr,hqr,_⟩ := SimpleGraph.is3Clique_iff.mp ht
    exact triangle_orientation G p q r hpq.1 hpr.1 hqr.1 ⟨hpq.2,hpr.2⟩
  · ext p q
    change (arcGraph G).Adj p q ↔
      ((arcGraph G).Adj p q ∧ c p ≠ c q) ∨ ((arcGraph G).Adj p q ∧ c p = c q)
    by_cases h : c p = c q <;> simp [h]

#print axioms arc_two_cover
end Erdos595ArcAdjoint
