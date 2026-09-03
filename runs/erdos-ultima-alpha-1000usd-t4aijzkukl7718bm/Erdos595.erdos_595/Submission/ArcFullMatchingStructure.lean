import Submission.SecondArcTriangleStructure

/-! Full matchings between disjoint triangle fibers of an arc graph with
unique triangles through edges pair opposite orientations of the SAME triangle.
This restricts the normal form but does not prove a covering theorem. -/
set_option autoImplicit false
open SimpleGraph Set
namespace Erdos595ArcFullMatching
open Erdos595ArcAdjoint Erdos595ArcRoundTrip
variable {V : Type*} (H : SimpleGraph V)

private lemma same_cycle {u v w x y z : V} (huv : u ≠ v) (hvw : v ≠ w) (hwu : w ≠ u)
    (h₁ : v = x ∨ y = u) (h₂ : w = y ∨ z = v) (h₃ : u = z ∨ x = w) :
    (u = x ∧ v = y) ∨ (u = y ∧ v = z) ∨ (u = z ∧ v = x) := by
  rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂ <;> rcases h₃ with h₃ | h₃ <;>
    subst_vars <;> simp_all

private lemma reverse_cycle (hH : UniqueTriangleEdge H) {u v w x y z : V}
    (huv : H.Adj u v) (hvw : H.Adj v w) (hwu : H.Adj w u)
    (hxy : H.Adj x y) (hyz : H.Adj y z) (hzx : H.Adj z x)
    (h₁ : v = x ∨ y = u) (h₂ : w = z ∨ x = v) (h₃ : u = y ∨ z = w) :
    x = v ∧ y = u ∧ z = w := by
  rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂ <;> rcases h₃ with h₃ | h₃ <;>
    subst_vars <;> simp_all only [true_and, and_true]
  all_goals first
    | exact hH hvw hxy hyz.symm huv.symm hwu
    | exact hH hxy hzx.symm hyz hvw hwu.symm
    | exact hH hyz hxy.symm hzx huv hvw.symm

def reverse (p : Arc H) : Arc H := ⟨(p.val.2,p.val.1),p.property.symm⟩

private theorem first_reversed (hH : UniqueTriangleEdge H) {p q r a b c : Arc H}
    (hpq : (arcGraph H).Adj p q) (hpr : (arcGraph H).Adj p r)
    (hqr : (arcGraph H).Adj q r)
    (hab : (arcGraph H).Adj a b) (hac : (arcGraph H).Adj a c)
    (hbc : (arcGraph H).Adj b c)
    (hpa : (arcGraph H).Adj p a) (hqb : (arcGraph H).Adj q b)
    (hrc : (arcGraph H).Adj r c)
    (h₁ : p ≠ a) (h₂ : p ≠ b) (h₃ : p ≠ c) : a = reverse H p := by
  have ht := arc_triangle hpq hpr hqr
  have hs := arc_triangle hab hac hbc
  rcases p with ⟨⟨u,v⟩,huv⟩
  rcases q with ⟨⟨v',w⟩,hvw⟩
  rcases r with ⟨⟨w',u'⟩,hwu⟩
  rcases a with ⟨⟨x,y⟩,hxy⟩
  rcases b with ⟨⟨y',z⟩,hyz⟩
  rcases c with ⟨⟨z',x'⟩,hzx⟩
  simp only [arcGraph] at hpa hqb hrc
  simp only [reverse,Subtype.mk.injEq,Prod.mk.injEq] at h₁ h₂ h₃ ⊢
  rcases ht with ⟨ht₁,ht₂,ht₃⟩ | ⟨ht₁,ht₂,ht₃⟩ <;>
    rcases hs with ⟨hs₁,hs₂,hs₃⟩ | ⟨hs₁,hs₂,hs₃⟩ <;>
    dsimp at ht₁ ht₂ ht₃ hs₁ hs₂ hs₃ <;> subst_vars
  · rcases same_cycle huv.ne hvw.ne hwu.ne hpa hqb hrc with he | he | he
    · exact (h₁ (Subtype.ext (Prod.ext he.1 he.2))).elim
    · exact (h₂ (Subtype.ext (Prod.ext he.1 he.2))).elim
    · exact (h₃ (Subtype.ext (Prod.ext he.1 he.2))).elim
  · have he := reverse_cycle H hH huv hvw hwu hxy hzx hyz hpa hqb hrc
    exact ⟨he.1,he.2.1⟩
  · have he := reverse_cycle H hH huv hwu hvw hxy hyz hzx hpa hrc hqb
    exact ⟨he.1,he.2.1⟩
  · rcases same_cycle huv.ne hwu.ne hvw.ne hpa hrc hqb with he | he | he
    · exact (h₁ (Subtype.ext (Prod.ext he.1 he.2))).elim
    · exact (h₃ (Subtype.ext (Prod.ext he.1 he.2))).elim
    · exact (h₂ (Subtype.ext (Prod.ext he.1 he.2))).elim

/-- A full matching between disjoint arc-triangles is exactly reversal.
The source graph needs uniqueness of the triangle through each edge. -/
theorem full_matching_reversal (hH : UniqueTriangleEdge H) {p q r a b c : Arc H}
    (hpq : (arcGraph H).Adj p q) (hpr : (arcGraph H).Adj p r)
    (hqr : (arcGraph H).Adj q r)
    (hab : (arcGraph H).Adj a b) (hac : (arcGraph H).Adj a c)
    (hbc : (arcGraph H).Adj b c)
    (hpa : (arcGraph H).Adj p a) (hqb : (arcGraph H).Adj q b)
    (hrc : (arcGraph H).Adj r c)
    (hd : Disjoint ({p,q,r} : Set (Arc H)) {a,b,c}) :
    a = reverse H p ∧ b = reverse H q ∧ c = reverse H r := by
  have hne : ∀ x ∈ ({p,q,r} : Set (Arc H)), ∀ y ∈ ({a,b,c} : Set (Arc H)), x ≠ y := by
    intro x hx y hy he
    exact Set.disjoint_left.mp hd hx (he ▸ hy)
  exact ⟨first_reversed H hH hpq hpr hqr hab hac hbc hpa hqb hrc
      (hne _ (by simp) _ (by simp)) (hne _ (by simp) _ (by simp))
      (hne _ (by simp) _ (by simp)),
    first_reversed H hH hqr hpq.symm hpr.symm hbc hab.symm hac.symm hqb hrc hpa
      (hne _ (by simp) _ (by simp)) (hne _ (by simp) _ (by simp))
      (hne _ (by simp) _ (by simp)),
    first_reversed H hH hpr.symm hqr.symm hpq hac.symm hbc.symm hab hrc hpa hqb
      (hne _ (by simp) _ (by simp)) (hne _ (by simp) _ (by simp))
      (hne _ (by simp) _ (by simp))⟩

/-- In particular, every disjoint full-matching partner of a second-arc
triangle is determined by that triangle. This is not an edge-cover theorem. -/
theorem second_arc_full_matching_reversal {p q r a b c : Arc (arcGraph H)}
    (hpq : (arcGraph (arcGraph H)).Adj p q)
    (hpr : (arcGraph (arcGraph H)).Adj p r)
    (hqr : (arcGraph (arcGraph H)).Adj q r)
    (hab : (arcGraph (arcGraph H)).Adj a b)
    (hac : (arcGraph (arcGraph H)).Adj a c)
    (hbc : (arcGraph (arcGraph H)).Adj b c)
    (hpa : (arcGraph (arcGraph H)).Adj p a)
    (hqb : (arcGraph (arcGraph H)).Adj q b)
    (hrc : (arcGraph (arcGraph H)).Adj r c)
    (hd : Disjoint ({p,q,r} : Set (Arc (arcGraph H))) {a,b,c}) :
    a = reverse (arcGraph H) p ∧ b = reverse (arcGraph H) q ∧
      c = reverse (arcGraph H) r :=
  full_matching_reversal (arcGraph H) (arc_unique_triangle_edge H)
    hpq hpr hqr hab hac hbc hpa hqb hrc hd

#print axioms full_matching_reversal
#print axioms second_arc_full_matching_reversal
end Erdos595ArcFullMatching
