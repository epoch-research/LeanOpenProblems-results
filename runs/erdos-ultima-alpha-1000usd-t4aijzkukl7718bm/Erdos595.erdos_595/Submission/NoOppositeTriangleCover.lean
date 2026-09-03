import Submission.ArcAdjoint

/-! A finite/countable vertex palette with no complementary bichromatic
triangle patterns gives an edge cover of the biclique right adjoint. -/
set_option autoImplicit false
open SimpleGraph Set
namespace Erdos595NoOppositeTriangle
open Erdos595ArcAdjoint Erdos595Work
variable {V C : Type*} (G : SimpleGraph V) (c : V → C)

/-- Excludes the simultaneous patterns A,A,B and B,B,A. Taking A=B also
excludes a monochromatic triangle. -/
def NoOpposite : Prop :=
  ∀ a b d x y z, G.Adj a b → G.Adj a d → G.Adj b d →
    G.Adj x y → G.Adj x z → G.Adj y z →
    c a = c b → c x = c y → c a = c z → c d = c x → False

lemma six_labels (h : NoOpposite G c) {a b d x y z : V}
    (hab : G.Adj a b) (had : G.Adj a d) (hbd : G.Adj b d)
    (hxy : G.Adj x y) (hxz : G.Adj x z) (hyz : G.Adj y z)
    (he₁ : s(c a,c x) = s(c b,c y)) (he₂ : s(c a,c x) = s(c d,c z)) : False := by
  rcases Sym2.eq_iff.mp he₁ with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩ <;>
    rcases Sym2.eq_iff.mp he₂ with ⟨h₃,h₄⟩ | ⟨h₃,h₄⟩
  · exact h a b d a b d hab had hbd hab had hbd h₁ h₁ h₃ h₃.symm
  · exact h a b d x y z hab had hbd hxy hxz hyz h₁ h₂ h₃ h₄.symm
  · exact h a d b x z y had hab hbd.symm hxz hxy hyz.symm h₃ h₄ h₁ h₂.symm
  · exact h b d a y z x hbd hab.symm had.symm hyz hxy.symm hxz.symm
      (h₂.symm.trans h₄) (h₁.symm.trans h₃) h₂.symm h₁

/-- Only the unordered pair of witness labels is needed. -/
theorem right_cover [Countable C] (h : NoOpposite G c) :
    IsCountableUnionOfTriangleFree (right G) := by
  classical
  obtain ⟨enc,henc⟩ := exists_injective_nat (Sym2 C)
  let col : Sym2 (Biclique G) → ℕ := Sym2.lift
    ⟨fun p q => if h : (right G).Adj p q then
      enc s(c h.1.choose,c h.2.choose) else 0,by
      intro p q
      dsimp only
      by_cases h : (right G).Adj p q
      · rw [dif_pos h,dif_pos h.symm]
        exact congrArg enc (Sym2.eq_swap)
      · rw [dif_neg h,dif_neg (fun h' => h h'.symm)]⟩
  have hc (p q : Biclique G) (h : (right G).Adj p q) :
      col s(p,q) = enc s(c h.1.choose,c h.2.choose) := by
    simp only [col,Sym2.lift_mk,dif_pos h]
  apply (countable_union_iff_edge_coloring (right G)).mpr
  refine ⟨col,?_⟩
  intro p q r hpq hpr hqr he
  have h₁ := hpq.1.choose_spec
  have h₂ := hpq.2.choose_spec
  have h₃ := hpr.1.choose_spec
  have h₄ := hpr.2.choose_spec
  have h₅ := hqr.1.choose_spec
  have h₆ := hqr.2.choose_spec
  apply six_labels G c h
    (q.property _ h₁.2 _ h₅.1) (p.property _ h₄.2 _ h₁.1).symm
    (r.property _ h₅.2 _ h₄.1)
    (q.property _ h₆.2 _ h₂.1).symm (p.property _ h₂.2 _ h₃.1)
    (r.property _ h₃.2 _ h₆.1).symm
  · exact henc (by simpa only [hc p q hpq,hc q r hqr] using he.2)
  · have hh := henc (by simpa only [hc p q hpq,hc p r hpr] using he.1)
    exact hh.trans Sym2.eq_swap

#print axioms six_labels
#print axioms right_cover
end Erdos595NoOppositeTriangle
