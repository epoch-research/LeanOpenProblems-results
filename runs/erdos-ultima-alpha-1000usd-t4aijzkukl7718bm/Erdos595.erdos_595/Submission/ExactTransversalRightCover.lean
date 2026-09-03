import Submission.ArcAdjoint
import Submission.CompleteFilterEdgeCover

/-! An exact-one vertex transversal of triangles gives a two-piece edge
cover of the biclique right adjoint, even if the transversal is not independent. -/
set_option autoImplicit false
open SimpleGraph Set
namespace Erdos595ExactTransversalRight
open Erdos595ArcAdjoint Erdos595CompleteFilterEdgeCover
variable {V : Type*}

/-- Exactly one of the three vertices of each triangle is marked. -/
def ExactTransversal (G : SimpleGraph V) (m : V → Bool) : Prop :=
  ∀ a b c, G.Adj a b → G.Adj a c → G.Adj b c →
    (m a).toNat + (m b).toNat + (m c).toNat = 1

private lemma six_bits : ∀ a b c a' b' c' : Bool,
    a.toNat + b.toNat + c.toNat = 1 →
    a'.toNat + b'.toNat + c'.toNat = 1 →
    ¬((a || a') = (c || c') ∧ (a || a') = (b || b')) := by
  decide +kernel

/-- No independence hypothesis is needed on the marked vertices: only their
exact-one incidence with each triangle is used. -/
theorem two_cover (G : SimpleGraph V) (m : V → Bool) (hm : ExactTransversal G m) :
    CoversWith (right G) 2 := by
  classical
  let col : Sym2 (Biclique G) → Bool := Sym2.lift
    ⟨fun p q => if h : (right G).Adj p q then m h.1.choose || m h.2.choose else false, by
      intro p q
      by_cases h : (right G).Adj p q
      · simp only [dif_pos h,dif_pos h.symm,Bool.or_comm]
      · simp only [dif_neg h,dif_neg (fun h' : (right G).Adj q p => h h'.symm)]⟩
  have ce (p q : Biclique G) (h : (right G).Adj p q) :
      col s(p,q) = (m h.1.choose || m h.2.choose) := by
    simp only [col,Sym2.lift_mk,dif_pos h]
  have valid (p q r : Biclique G) (hpq : (right G).Adj p q)
      (hpr : (right G).Adj p r) (hqr : (right G).Adj q r) :
      ¬(col s(p,q) = col s(p,r) ∧ col s(p,q) = col s(q,r)) := by
    have a := hpq.1.choose_spec
    have b := hqr.1.choose_spec
    have c := hpr.2.choose_spec
    have a' := hpq.2.choose_spec
    have b' := hqr.2.choose_spec
    have c' := hpr.1.choose_spec
    have h₁ := hm hpq.1.choose hqr.1.choose hpr.2.choose
      (q.property _ a.2 _ b.1) (p.property _ c.2 _ a.1).symm (r.property _ b.2 _ c.1)
    have h₂ := hm hpq.2.choose hqr.2.choose hpr.1.choose
      (q.property _ b'.2 _ a'.1).symm (p.property _ a'.2 _ c'.1)
      (r.property _ c'.2 _ b'.1).symm
    simpa only [ce p q hpq,ce p r hpr,ce q r hqr,Bool.or_comm] using
      six_bits _ _ _ _ _ _ h₁ h₂
  let H (i : Fin 2) : SimpleGraph (Biclique G) :=
    { Adj p q := (right G).Adj p q ∧ col s(p,q) = decide (i = 1)
      symm := fun _ _ h => ⟨h.1.symm,by simpa only [Sym2.eq_swap] using h.2⟩
      loopless := fun _ h => h.1.ne rfl }
  refine ⟨H,?_,?_⟩
  · intro i t ht
    obtain ⟨p,q,r,hpq,hpr,hqr,_⟩ := SimpleGraph.is3Clique_iff.mp ht
    exact valid p q r hpq.1 hpr.1 hqr.1
      ⟨hpq.2.trans hpr.2.symm,hpq.2.trans hqr.2.symm⟩
  · intro p q hpq
    cases hc : col s(p,q)
    · exact ⟨0,hpq,hc⟩
    · exact ⟨1,hpq,hc⟩

/-- A three-valued vertex label that is rainbow on all triangles suffices. -/
theorem two_cover_of_rainbow (G : SimpleGraph V) (c : V → Fin 3)
    (hc : ∀ a b d, G.Adj a b → G.Adj a d → G.Adj b d →
      c a ≠ c b ∧ c a ≠ c d ∧ c b ≠ c d) : CoversWith (right G) 2 := by
  classical
  apply two_cover G (fun v => decide (c v = 0))
  intro a b d hab had hbd
  obtain ⟨h₁,h₂,h₃⟩ := hc a b d hab had hbd
  change (decide (c a = 0)).toNat + (decide (c b = 0)).toNat + (decide (c d = 0)).toNat = 1
  generalize c a = x at h₁ h₂ ⊢
  generalize c b = y at h₁ h₃ ⊢
  generalize c d = z at h₂ h₃ ⊢
  fin_cases x <;> fin_cases y <;> fin_cases z <;> simp_all

#print axioms two_cover
#print axioms two_cover_of_rainbow
end Erdos595ExactTransversalRight
