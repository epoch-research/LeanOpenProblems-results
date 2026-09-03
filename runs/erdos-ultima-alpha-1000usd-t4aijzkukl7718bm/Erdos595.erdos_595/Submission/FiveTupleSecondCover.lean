import Submission.FiveTupleIterationObstruction
import Submission.NegativeInner

/-!
A finite witness-type obstruction for the first right adjoint of H2.
Auxiliary work toward Erdős 595, not a settlement of that conjecture.
-/

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 0
open SimpleGraph Set
open Erdos595ArcAdjoint Erdos595Work Erdos595FiveIteration
namespace Erdos595FiveSecond
variable {A : Type*} [LinearOrder A]
abbrev Point := Fin 5 → A

def T (x y z : Point (A := A)) : Prop := P21 x y ∧ P20 x z ∧ P21 y z

def typeRel (k : Bool) (x y : Point (A := A)) : Prop := if k then P21 x y else P20 x y

private theorem label_ne {x y : Point (A := A)} (h : H2.Adj x y) : x 0 ≠ y 0 := by
  intro he
  rcases h with (h | h) | (h | h) <;>
    simp only [P20, P21] at h <;>
    rcases h with ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9⟩ <;> order

private theorem forward {x y : Point (A := A)} (h : H2.Adj x y) (hxy : x 0 < y 0) :
    P20 x y ∨ P21 x y := by
  rcases h with h | (h | h)
  · exact h
  all_goals
    simp only [P20,P21] at h
    rcases h with ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9⟩
    order

private theorem triangle_ordered (x y z : Point (A := A))
    (hxy : x 0 < y 0) (hyz : y 0 < z 0)
    (h₁ : H2.Adj x y) (h₂ : H2.Adj x z) (h₃ : H2.Adj y z) : T x y z := by
  have f₁ := forward h₁ hxy
  have f₂ := forward h₂ (hxy.trans hyz)
  have f₃ := forward h₃ hyz
  rcases f₁ with f₁ | f₁ <;> rcases f₂ with f₂ | f₂ <;> rcases f₃ with f₃ | f₃
  all_goals first
    | exact ⟨f₁,f₂,f₃⟩
    | (exfalso
       simp only [P20,P21] at f₁ f₂ f₃
       rcases f₁ with ⟨h11,h12,h13,h14,h15,h16,h17,h18,h19⟩
       rcases f₂ with ⟨h21,h22,h23,h24,h25,h26,h27,h28,h29⟩
       rcases f₃ with ⟨h31,h32,h33,h34,h35,h36,h37,h38,h39⟩
       order)

private theorem triangle_cases (x y z : Point (A := A))
    (h₁ : H2.Adj x y) (h₂ : H2.Adj x z) (h₃ : H2.Adj y z) :
    T x y z ∨ T x z y ∨ T y x z ∨ T y z x ∨ T z x y ∨ T z y x := by
  rcases lt_or_gt_of_ne (label_ne h₁) with hxy | hyx
  · rcases lt_or_gt_of_ne (label_ne h₃) with hyz | hzy
    · exact Or.inl (triangle_ordered x y z hxy hyz h₁ h₂ h₃)
    · rcases lt_or_gt_of_ne (label_ne h₂) with hxz | hzx
      · exact Or.inr (Or.inl (triangle_ordered x z y hxz hzy h₂ h₁ h₃.symm))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          (triangle_ordered z x y hzx hxy h₂.symm h₃.symm h₁)))))
  · rcases lt_or_gt_of_ne (label_ne h₂) with hxz | hzx
    · exact Or.inr (Or.inr (Or.inl (triangle_ordered y x z hyx hxz h₁.symm h₃ h₂)))
    · rcases lt_or_gt_of_ne (label_ne h₃) with hyz | hzy
      · exact Or.inr (Or.inr (Or.inr (Or.inl
          (triangle_ordered y z x hyz hzx h₃ h₁.symm h₂.symm))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (triangle_ordered z y x hzy hyx h₃.symm h₂.symm h₁.symm)))))

/-- The two cyclic witness triangles have only two possible orders when
all three reverse-pair edges have one fixed positive type. -/
private theorem uniform_triangle (k : Bool)
    (ab ba ac ca bc cb : Point (A := A))
    (hab : typeRel k ab ba) (hac : typeRel k ac ca) (hbc : typeRel k bc cb)
    (h₁ : H2.Adj ab bc) (h₂ : H2.Adj ab ca) (h₃ : H2.Adj bc ca)
    (h₄ : H2.Adj ac cb) (h₅ : H2.Adj ac ba) (h₆ : H2.Adj cb ba) :
    (T ab bc ca ∧ T ac ba cb) ∨ (T bc ab ca ∧ T ac cb ba) := by
  have t₁ := triangle_cases ab bc ca h₁ h₂ h₃
  have t₂ := triangle_cases ac cb ba h₄ h₅ h₆
  cases k
  · rcases t₁ with t₁ | t₁ | t₁ | t₁ | t₁ | t₁ <;>
      rcases t₂ with t₂ | t₂ | t₂ | t₂ | t₂ | t₂
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.1).trans ((t₁.1.2.2.2.2.2.1).trans ((hbc.2.2.1).trans (t₂.2.2.1)))))
    · exact Or.inl ⟨t₁,t₂⟩
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.1).trans ((t₁.1.2.2.2.2.2.1).trans ((hbc.2.2.1).trans ((t₂.1.1).trans (t₂.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.1).trans ((t₁.1.2.2.2.2.2.1).trans ((hbc.2.2.1).trans (t₂.1.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.2.2.1).trans ((t₂.2.1.2.2.1).trans ((hbc.2.2.2.1).trans (t₁.1.2.2.2.2.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.1).trans ((t₂.1.2.2.1).trans ((hab.2.2.2.2.2.2.2.1).trans ((hab.2.2.2.2.2.2.2.2).trans ((t₂.2.1.2.2.2.2.2.2.1).trans ((hac.2.2.1).trans (t₁.2.1.2.2.2.1))))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.1).trans ((t₁.2.1.2.2.2.2.1).trans ((hbc.2.1).trans ((hbc.2.2.1).trans (t₂.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.1).trans ((t₂.1.2.2.2.2.1).trans ((hac.2.2.2.2.1).trans (t₁.1.2.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.1).trans ((t₂.2.2.2.2.2.2.1).trans ((hac.2.2.2.2.1).trans (t₁.1.2.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.1).trans ((t₁.2.1.2.2.2.2.1).trans ((hbc.2.1).trans ((hbc.2.2.1).trans (t₂.1.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.1).trans ((hab.2.2.1).trans ((t₂.1.1).trans ((hac.1).trans ((hac.2.1).trans ((hac.2.2.1).trans (t₁.1.2.1))))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.2.1).trans ((t₁.2.1.2.2.2.2.2.2.1).trans ((hbc.2.2.1).trans (t₂.1.2.1)))))
    · exact Or.inr ⟨t₁,t₂⟩
    · exact False.elim ((lt_irrefl _) ((hab.2.2.1).trans ((t₂.2.2.1).trans ((hbc.2.2.2.1).trans (t₁.1.2.2.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.1).trans ((t₁.1.2.2.2.2.2.2.2.1).trans ((hbc.2.2.2.2.2.2.1).trans (t₂.2.1.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.1).trans ((hab.2.2.1).trans ((t₂.2.2.1).trans ((hac.1).trans ((hac.2.1).trans ((hac.2.2.1).trans (t₁.2.2.2.1))))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.1).trans ((t₂.1.1).trans ((t₂.2.2.1).trans ((hbc.2.2.2.1).trans (t₁.1.2.2.2.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.1).trans ((t₂.1.1).trans ((hbc.2.2.2.1).trans (t₁.1.2.2.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.1).trans ((t₂.2.2.2.1).trans ((hbc.2.2.2.2.2.1).trans (t₁.2.1.2.2.2.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.1).trans ((hab.2.2.1).trans ((t₂.2.2.1).trans ((hbc.2.2.2.1).trans (t₁.2.1.2.2.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.1).trans ((hab.2.1).trans ((hab.2.2.1).trans ((t₂.2.1.2.2.2.1).trans ((t₂.1.2.2.2.2.2.1).trans ((hac.2.2.1).trans (t₁.2.2.1))))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.1).trans ((t₂.1.2.1).trans ((hbc.2.2.2.2.2.1).trans (t₁.2.1.2.2.2.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hac.2.2.2.2.1).trans ((t₁.1.2.2.2.2.1).trans ((hbc.2.2.2.2.1).trans (t₂.2.2.2.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.1).trans ((hab.2.2.1).trans ((t₂.1.1).trans ((hbc.2.2.2.1).trans (t₁.2.1.2.2.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.1).trans ((t₁.2.2.2.2.2.2.2.1).trans ((hbc.2.2.1).trans (t₂.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.1).trans ((hab.2.1).trans ((hab.2.2.1).trans ((t₂.1.2.1).trans ((hac.2.1).trans ((hac.2.2.1).trans (t₁.1.1))))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.1).trans ((t₁.2.2.2.2.2.2.2.1).trans ((hbc.2.2.1).trans ((t₂.1.1).trans (t₂.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.1).trans ((t₁.2.2.2.2.2.2.2.1).trans ((hbc.2.2.1).trans (t₂.1.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.2.2.1).trans ((t₂.2.1.2.2.1).trans ((hbc.2.2.2.1).trans (t₁.2.2.2.2.2.2.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.1).trans ((hab.2.1).trans ((hab.2.2.1).trans ((t₂.1.1).trans ((t₂.2.2.1).trans ((hac.1).trans ((hac.2.1).trans ((hac.2.2.1).trans (t₁.1.1))))))))))
    · exact False.elim ((lt_irrefl _) ((hab.1).trans ((hab.2.1).trans ((hab.2.2.1).trans ((t₂.2.1.2.2.2.1).trans ((hac.2.2.2.2.1).trans ((t₁.1.2.2.1).trans (t₁.2.1.2.2.1))))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.1).trans ((t₂.2.2.1).trans ((hbc.2.2.2.1).trans (t₁.2.2.2.2.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.1).trans ((t₁.2.2.2.2.2.2.2.2.2.1).trans ((hbc.2.2.2.2.2.2.1).trans (t₂.2.1.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.1).trans ((hab.2.1).trans ((hab.2.2.1).trans ((t₂.2.2.1).trans ((hac.1).trans ((hac.2.1).trans ((hac.2.2.1).trans ((t₁.1.1).trans (t₁.2.2.1))))))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.1).trans ((t₂.1.1).trans ((t₂.2.2.1).trans ((hbc.2.2.2.1).trans (t₁.2.2.2.2.2.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.1).trans ((t₂.1.1).trans ((hbc.2.2.2.1).trans (t₁.2.2.2.2.2.2.2.1)))))
  · rcases t₁ with t₁ | t₁ | t₁ | t₁ | t₁ | t₁ <;>
      rcases t₂ with t₂ | t₂ | t₂ | t₂ | t₂ | t₂
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.1).trans ((t₁.2.1.2.2.2.2.1).trans ((hac.2.2.2.2.1).trans (t₂.2.1.2.2.2.2.1)))))
    · exact Or.inl ⟨t₁,t₂⟩
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.2.2.1).trans ((hab.2.2.2.2.2.2.2.1).trans ((t₁.1.2.2.2.2.2.2.2.2).trans ((hbc.2.2.2.2.2.2.2.2).trans (t₂.2.1.2.2.2.2.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.1).trans ((t₁.1.2.2.2.2.2.1).trans ((hbc.2.2.2.1).trans ((t₂.1.2.2.1).trans (t₂.1.2.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.2.1).trans ((t₂.2.1.2.2.1).trans ((hbc.2.1).trans (t₁.1.2.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.2.1).trans ((t₂.2.1.2.2.1).trans ((hac.1).trans (t₁.2.1.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.1).trans ((hab.2.2.1).trans ((t₁.2.1.2.2.1).trans ((hbc.1).trans (t₂.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.2.2.2.1).trans ((t₁.2.1.2.2.2.2.2.2.1).trans ((hbc.2.2.2.1).trans (t₂.2.2.2.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hac.1).trans ((t₁.2.2.1).trans ((hbc.1).trans (t₂.1.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.1).trans ((hab.2.2.1).trans ((t₁.2.1.2.2.1).trans ((hbc.1).trans (t₂.1.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.2.1).trans ((hab.2.2.2.2.2.2.1).trans ((t₂.1.2.2.2.2.2.1).trans ((hac.2.2.2.1).trans (t₁.1.2.2.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.2.2.2.1).trans ((t₁.2.1.2.2.2.2.2.2.1).trans ((hbc.2.2.2.1).trans (t₂.1.2.2.2.2.1)))))
    · exact Or.inr ⟨t₁,t₂⟩
    · exact False.elim ((lt_irrefl _) ((hac.2.2.2.2.1).trans ((t₂.2.1.2.2.2.2.1).trans ((hbc.2.2.2.2.1).trans (t₁.2.1.2.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.1).trans ((t₁.1.2.2.2.2.1).trans ((hbc.2.2.2.2.2.1).trans (t₂.2.1.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hac.1).trans ((t₁.2.1.2.2.2.1).trans ((hbc.2.2.2.2.2.1).trans (t₂.2.1.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.2.1).trans ((hab.2.2.2.2.2.2.1).trans ((t₂.1.2.2.2.2.2.1).trans ((hac.2.2.2.1).trans (t₁.2.2.2.2.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.1).trans ((t₂.1.2.2.1).trans ((t₂.1.2.2.2.1).trans ((hbc.2.2.2.2.1).trans (t₁.1.2.2.2.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.1).trans ((t₂.2.2.2.2.2.2.1).trans ((hbc.2.2.2.2.2.2.2.1).trans (t₁.2.1.2.2.2.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.1).trans ((t₂.2.2.1).trans ((hbc.2.1).trans ((hbc.2.2.1).trans (t₁.2.1.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.1).trans ((hab.2.2.2.1).trans ((t₂.2.2.2.2.2.2.1).trans ((hac.2.2.2.2.2.1).trans (t₁.2.2.2.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.1).trans ((t₂.2.2.1).trans ((hac.1).trans (t₁.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.1).trans ((t₂.1.1).trans ((hac.1).trans (t₁.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.1).trans ((t₂.1.1).trans ((hbc.2.1).trans ((hbc.2.2.1).trans (t₁.2.1.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.1).trans ((t₁.2.2.2.2.2.2.2.1).trans ((hbc.2.2.2.1).trans ((t₂.1.2.2.2.2.1).trans (t₂.2.1.2.2.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hac.2.2.2.2.2.1).trans ((t₁.2.1.2.2.1).trans ((hbc.1).trans (t₂.2.1.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.1).trans ((hab.2.2.2.1).trans ((t₂.2.2.2.2.2.2.1).trans ((hac.2.2.2.2.2.1).trans (t₁.1.2.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.1).trans ((t₂.2.2.1).trans ((hac.1).trans (t₁.1.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.1).trans ((t₂.1.1).trans ((hac.1).trans (t₁.1.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.1).trans ((t₂.1.1).trans ((t₂.2.2.1).trans ((hac.1).trans (t₁.1.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.1).trans ((t₂.2.1.2.2.2.1).trans ((hac.2.2.2.2.2.1).trans (t₁.2.1.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.1).trans ((t₂.2.2.1).trans ((t₂.2.1.2.2.2.1).trans ((hac.2.2.2.2.2.1).trans (t₁.2.1.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.1).trans ((t₁.2.2.2.2.2.2.1).trans ((hbc.2.2.2.2.2.1).trans (t₂.2.1.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.1).trans ((t₂.2.2.1).trans ((hac.1).trans ((t₁.1.1).trans (t₁.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.1).trans ((t₂.1.1).trans ((hac.1).trans ((t₁.1.1).trans (t₁.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hac.1).trans ((t₁.1.1).trans ((hbc.1).trans (t₂.2.2.1)))))

#print axioms uniform_triangle

/-- A monochromatic witness-type diamond is impossible. -/
private theorem uniform_diamond {W : Type*} (F : SimpleGraph W)
    (f : arcGraph F →g H2 (A := A)) (k : Bool) (a b c d : W)
    (hab : F.Adj a b) (hac : F.Adj a c) (hbc : F.Adj b c)
    (had : F.Adj a d) (hcd : F.Adj c d)
    (habt : typeRel k (f ⟨(a,b),hab⟩) (f ⟨(b,a),hab.symm⟩))
    (hact : typeRel k (f ⟨(a,c),hac⟩) (f ⟨(c,a),hac.symm⟩))
    (hbct : typeRel k (f ⟨(b,c),hbc⟩) (f ⟨(c,b),hbc.symm⟩))
    (hadt : typeRel k (f ⟨(a,d),had⟩) (f ⟨(d,a),had.symm⟩))
    (hcdt : typeRel k (f ⟨(c,d),hcd⟩) (f ⟨(d,c),hcd.symm⟩)) : False := by
  have t₁ := uniform_triangle k
    (f ⟨(a,b),hab⟩) (f ⟨(b,a),hab.symm⟩)
    (f ⟨(a,c),hac⟩) (f ⟨(c,a),hac.symm⟩)
    (f ⟨(b,c),hbc⟩) (f ⟨(c,b),hbc.symm⟩) habt hact hbct
    (f.map_adj (Or.inl rfl)) (f.map_adj (Or.inr rfl)) (f.map_adj (Or.inl rfl))
    (f.map_adj (Or.inl rfl)) (f.map_adj (Or.inr rfl)) (f.map_adj (Or.inl rfl))
  have t₂ := uniform_triangle k
    (f ⟨(a,c),hac⟩) (f ⟨(c,a),hac.symm⟩)
    (f ⟨(a,d),had⟩) (f ⟨(d,a),had.symm⟩)
    (f ⟨(c,d),hcd⟩) (f ⟨(d,c),hcd.symm⟩) hact hadt hcdt
    (f.map_adj (Or.inl rfl)) (f.map_adj (Or.inr rfl)) (f.map_adj (Or.inl rfl))
    (f.map_adj (Or.inl rfl)) (f.map_adj (Or.inr rfl)) (f.map_adj (Or.inl rfl))
  have hfwd : H2.Adj (f ⟨(b,c),hbc⟩) (f ⟨(c,d),hcd⟩) := f.map_adj (Or.inl rfl)
  have hrev : H2.Adj (f ⟨(c,b),hbc.symm⟩) (f ⟨(d,c),hcd.symm⟩) := f.map_adj (Or.inr rfl)
  cases k
  · rcases t₁ with t₁ | t₁ <;> rcases t₂ with t₂ | t₂
    · rcases hfwd with (h | h) | (h | h)
      · exact (lt_irrefl _) ((hact.2.2.2.2.1).trans ((t₁.1.2.2.2.2.2.2.1).trans ((h.2.2.2.2.1).trans (t₂.1.1.2.2.2.2.1))))
      · exact (lt_irrefl _) ((hcdt.2.2.1).trans ((t₂.2.2.2.2.1).trans ((t₁.1.2.2.2.2.2.2.1).trans (h.2.2.2.2.2.1))))
      · exact (lt_irrefl _) ((hact.2.2.2.1).trans ((t₂.1.1.2.2.2.2.2.1).trans ((h.2.2.1).trans (t₁.1.2.2.1))))
      · exact (lt_irrefl _) ((habt.2.2.2.2.1).trans ((t₁.2.1.2.2.2.2.1).trans ((t₂.1.1.2.2.2.2.2.1).trans ((h.2.2.2.1).trans (t₁.1.1.2.2.2.2.1)))))
    · rcases hfwd with (h | h) | (h | h)
      · exact (lt_irrefl _) ((habt.2.2.2.1).trans ((t₁.1.1.2.2.2.2.2.1).trans ((h.2.2.1).trans ((t₂.1.1.1).trans (t₁.2.1.1)))))
      · exact (lt_irrefl _) ((hact.2.1).trans ((t₁.2.2.1.2.2.1).trans ((hbct.2.2.2.1).trans ((h.2.2.2.2.2.1).trans (t₂.1.1.2.2.2.1)))))
      · exact (lt_irrefl _) ((hbct.2.2.1).trans ((t₁.2.2.1.2.2.2.1).trans ((t₂.1.1.2.2.2.2.2.2.2.1).trans (h.2.2.2.2.2.2.1))))
      · exact (lt_irrefl _) ((hact.2.2.1).trans ((t₁.1.2.2.2.1).trans ((h.2.2.2.2.1).trans (t₂.1.1.2.2.2.2.2.1))))
    · rcases hrev with (h | h) | (h | h)
      · exact (lt_irrefl _) ((hbct.2.2.2.2.2.2.1).trans ((h.2.2.1).trans ((t₂.2.2.2.2.1).trans (t₁.1.2.1.2.2.2.2.2.1))))
      · exact (lt_irrefl _) ((hact.2.2.2.2.2.2.1).trans ((t₂.2.2.2.2.2.2.1).trans ((h.2.2.2.2.1).trans (t₁.2.1.2.2.2.2.2.2.2.1))))
      · exact (lt_irrefl _) ((habt.2.2.2.2.2.1).trans ((t₁.1.2.2.2.2.2.2.2.2.2.2).trans ((t₂.2.2.2.2.2.2.2.2.2.2.2).trans ((h.2.2.2.2.2.2.1).trans (t₁.2.2.2.2.2.2.1)))))
      · exact (lt_irrefl _) ((hact.2.1).trans ((hact.2.2.1).trans ((t₂.2.2.2.1).trans ((h.1).trans (t₁.2.1.2.1)))))
    · rcases hfwd with (h | h) | (h | h)
      · exact (lt_irrefl _) ((hact.2.1).trans ((t₁.2.1.2.2.2.1).trans ((hbct.2.2.2.2.2.1).trans ((h.2.2.2.2.2.2.1).trans (t₂.1.1.2.2.2.1)))))
      · exact (lt_irrefl _) ((hcdt.2.2.1).trans ((t₂.2.2.2.1).trans ((t₁.1.2.1.2.2.2.1).trans (h.2.2.2.2.2.1))))
      · exact (lt_irrefl _) ((hact.2.2.2.1).trans ((t₂.1.1.2.2.2.2.2.2.2.1).trans ((h.2.2.2.2.2.2.1).trans (t₁.1.2.1.2.2.1))))
      · exact (lt_irrefl _) ((hbct.2.2.1).trans ((t₁.2.1.2.1).trans ((t₂.1.1.2.2.2.2.1).trans (h.2.2.2.2.2.1))))
  · rcases t₁ with t₁ | t₁ <;> rcases t₂ with t₂ | t₂
    · rcases hrev with (h | h) | (h | h)
      · exact (lt_irrefl _) ((hbct.2.2.2.2.2.1).trans ((h.2.2.1).trans ((t₂.2.2.2.2.1).trans (t₁.1.2.2.2.2.2.2.1))))
      · exact (lt_irrefl _) ((hact.2.2.2.2.2.2.2.1).trans ((t₁.2.2.1.2.2.2.2.2.2.1).trans ((h.2.2.2.1).trans (t₂.2.2.2.2.2.2.2.1))))
      · exact (lt_irrefl _) ((hact.2.2.2.2.2.1).trans ((hact.2.2.2.2.2.2.1).trans ((t₂.2.2.2.2.2.2.2.2.1).trans ((h.2.2.1).trans (t₁.2.2.1.2.2.2.1)))))
      · exact (lt_irrefl _) ((hact.2.2.2.2.2.2.1).trans ((t₂.2.2.2.2.2.2.2.2.1).trans ((h.2.2.2.1).trans ((hbct.2.2.2.2.1).trans (t₁.1.2.2.2.2.2.2.2.1)))))
    · rcases hfwd with (h | h) | (h | h)
      · exact (lt_irrefl _) ((hact.1).trans ((t₁.1.2.1.2.2.2.1).trans ((t₁.1.1.2.2.2.2.2.1).trans ((h.2.2.1).trans (t₂.1.1.1)))))
      · exact (lt_irrefl _) ((hact.2.2.1).trans ((hact.2.2.2.1).trans ((t₁.1.2.2.2.2.2.2.1).trans ((h.2.2.2.2.2.1).trans (t₂.1.1.2.2.2.1)))))
      · exact (lt_irrefl _) ((hact.2.2.2.2.1).trans ((t₂.1.1.2.2.2.2.2.2.2.1).trans ((h.2.2.2.2.2.2.1).trans (t₁.1.2.2.2.2.2.1))))
      · exact (lt_irrefl _) ((hbct.2.1).trans ((h.2.2.2.2.1).trans ((t₂.1.1.2.2.2.2.2.1).trans (t₁.2.2.1.2.2.1))))
    · rcases hrev with (h | h) | (h | h)
      · exact (lt_irrefl _) ((hact.2.2.2.2.1).trans ((t₁.2.1.2.2.2.2.2.1).trans ((h.2.2.1).trans (t₂.2.2.2.2.1))))
      · exact (lt_irrefl _) ((hbct.2.2.2.2.2.2.2.1).trans ((t₁.1.2.1.2.2.2.2.2.2.1).trans ((t₂.2.2.2.2.2.2.1).trans (h.2.2.2.2.1))))
      · exact (lt_irrefl _) ((hact.2.2.2.2.2.2.2.2).trans ((t₂.2.2.2.2.2.2.2.2.2.2.2).trans ((h.2.2.2.2.2.2.1).trans ((hbct.2.2.2.2.2.2.1).trans (t₁.2.1.2.2.2.2.2.2.2.1)))))
      · exact (lt_irrefl _) ((hact.2.2.2.2.2.1).trans ((hact.2.2.2.2.2.2.1).trans ((t₂.2.2.2.2.2.2.2.2.1).trans ((h.2.2.2.1).trans (t₁.2.1.2.2.2.2.1)))))
    · rcases hfwd with (h | h) | (h | h)
      · exact (lt_irrefl _) ((hact.2.2.1).trans ((hact.2.2.2.1).trans ((t₁.1.2.1.2.2.2.2.2.1).trans ((h.2.2.2.2.2.2.1).trans (t₂.1.1.2.2.2.1)))))
      · exact (lt_irrefl _) ((hact.2.2.1).trans ((t₁.2.1.2.2.2.1).trans ((hbct.2.2.2.2.1).trans ((h.2.2.2.2.2.1).trans (t₂.1.1.2.2.2.1)))))
      · exact (lt_irrefl _) ((hbct.2.2.2.1).trans ((t₁.2.1.2.2.2.2.1).trans ((t₂.1.1.2.2.2.2.2.2.2.1).trans (h.2.2.2.2.2.2.1))))
      · exact (lt_irrefl _) ((hact.2.1).trans ((t₂.1.1.2.2.2.2.1).trans ((h.2.2.2.2.2.1).trans (t₁.1.2.1.2.2.1))))

section Flag
variable {W C : Type*} [LinearOrder W] [Countable C]

private def Later (F : SimpleGraph W) (col : W → W → C) (a b : W) : Prop :=
  ∃ c, b < c ∧ F.Adj a c ∧ F.Adj b c ∧ col a c = col a b ∧ col b c = col a b

/-- One extension bit converts a finite homogeneous-diamond exclusion
into a triangle-free edge coloring. -/
private theorem cover_of_no_diamond (F : SimpleGraph W) (col : W → W → C)
    (hn : ∀ a b c d, a < b → b < c → c < d →
      F.Adj a b → F.Adj a c → F.Adj b c → F.Adj a d → F.Adj c d →
      col a b = col a c → col a b = col b c →
      col a b = col a d → col a b = col c d → False) :
    IsCountableUnionOfTriangleFree F := by
  classical
  let code (a b : W) := (col a b,decide (Later F col a b))
  apply Erdos595NegativeInner.cover_of_ordered_patterns F code
  intro a b c hab hbc aab aac abc he
  have h₁ : col a b = col a c := congrArg Prod.fst he.1
  have h₂ : col a b = col b c := congrArg Prod.fst he.2
  have hl : Later F col a b := ⟨c,hbc,aac,abc,h₁.symm,h₂.symm⟩
  have hl' : Later F col a c := by
    have hh : decide (Later F col a b) = decide (Later F col a c) := congrArg Prod.snd he.1
    exact of_decide_eq_true (hh.symm.trans (decide_eq_true hl))
  obtain ⟨d,hcd,aad,acd,h₃,h₄⟩ := hl'
  exact hn a b c d hab hbc hcd aab aac abc aad acd h₁ h₂
    (h₁.trans h₃.symm) (h₁.trans h₄.symm)
end Flag

noncomputable def typeCode (x y : Point (A := A)) : Bool × Bool := by
  classical
  exact if P20 x y then (false,false)
    else if P21 x y then (false,true)
    else if P20 y x then (true,false) else (true,true)

private theorem typeCode_spec (x y : Point (A := A)) (h : H2.Adj x y) :
    typeRel (typeCode x y).2
      (if (typeCode x y).1 then y else x)
      (if (typeCode x y).1 then x else y) := by
  classical
  by_cases h₀ : P20 x y
  · simpa only [typeCode, if_pos h₀, typeRel, Bool.false_eq_true, if_false] using h₀
  by_cases h₁ : P21 x y
  · simpa only [typeCode, if_neg h₀, if_pos h₁, typeRel,
      Bool.false_eq_true, if_false, if_true] using h₁
  by_cases h₂ : P20 y x
  · simpa only [typeCode, if_neg h₀, if_neg h₁, if_pos h₂, typeRel,
      Bool.false_eq_true, if_false, if_true] using h₂
  have h₃ : P21 y x := by
    rcases h with (h | h) | (h | h)
    · exact (h₀ h).elim
    · exact (h₁ h).elim
    · exact (h₂ h).elim
    · exact h
  simpa only [typeCode, if_neg h₀, if_neg h₁, if_neg h₂, typeRel, if_true] using h₃

section Pullback
variable {W : Type*} (F : SimpleGraph W) (f : arcGraph F →g H2 (A := A))

private def reverse : arcGraph F →g arcGraph F where
  toFun e := ⟨(e.1.2,e.1.1),e.2.symm⟩
  map_rel' := by
    intro e d h
    exact h.elim (fun h => Or.inr h.symm) (fun h => Or.inl h.symm)

private def oriented (s : Bool) : arcGraph F →g H2 (A := A) :=
  if s then f.comp (reverse F) else f

private noncomputable def color (a b : W) : Bool × Bool := by
  classical
  exact if h : F.Adj a b then typeCode (f ⟨(a,b),h⟩) (f ⟨(b,a),h.symm⟩)
    else (false,false)

private theorem pair_type {a b : W} (h : F.Adj a b) :
    typeRel (color F f a b).2
      ((oriented F f (color F f a b).1) ⟨(a,b),h⟩)
      ((oriented F f (color F f a b).1) ⟨(b,a),h.symm⟩) := by
  classical
  have ht := typeCode_spec (f ⟨(a,b),h⟩) (f ⟨(b,a),h.symm⟩)
    (f.map_adj (Or.inl rfl))
  simp only [color, dif_pos h, oriented]
  split_ifs with hs
  · simpa only [hs, if_true] using ht
  · simpa only [hs, if_false] using ht

include f in
/-- Any graph whose arc graph maps into H2 has a finite witness-type
coloring after adding one extension bit. -/
theorem arc_source_cover : IsCountableUnionOfTriangleFree F := by
  classical
  letI : LinearOrder W := IsWellOrder.linearOrder WellOrderingRel
  apply cover_of_no_diamond F (color F f)
  intro a b c d _ _ _ hab hac hbc had hcd h₁ h₂ h₃ h₄
  let k := color F f a b
  have ht (p q : W) (h : F.Adj p q) (he : color F f p q = k) :
      typeRel k.2 ((oriented F f k.1) ⟨(p,q),h⟩)
        ((oriented F f k.1) ⟨(q,p),h.symm⟩) := by
    have h' := pair_type F f h
    rw [he] at h'
    exact h'
  exact uniform_diamond F (oriented F f k.1) k.2 a b c d hab hac hbc had hcd
    (ht a b hab rfl) (ht a c hac h₁.symm) (ht b c hbc h₂.symm)
    (ht a d had h₃.symm) (ht c d hcd h₄.symm)
end Pullback

/-- The first right adjoint of H2 is also ruled out. -/
theorem first_right_cover : IsCountableUnionOfTriangleFree (right (H2 (A := A))) :=
  arc_source_cover (right H2) (fromRight SimpleGraph.Hom.id)

#print axioms uniform_triangle
#print axioms uniform_diamond
#print axioms cover_of_no_diamond
#print axioms arc_source_cover
#print axioms first_right_cover
end Erdos595FiveSecond
