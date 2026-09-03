import FormalConjecturesUtil
import Submission.C6
import Submission.ThetaC4DeletionObstruction

/-! Two-slope grids in the four-coordinate Wenger incidence construction.
Arbitrary retained incidences are allowed. This is not a C8-free construction. -/
open SimpleGraph Finset
open scoped Classical
namespace Erdos713WengerRestriction
variable {K : Type*} [Field K]
set_option maxHeartbeats 2000000
abbrev Point (K : Type*) := Fin 4 → K

def lineThrough (p : Point K) (a : K) : Point K :=
  ![a,p 1-a*p 0,p 2-a^2*p 0,p 3-a^3*p 0]

def Rel (A : Point K → K → Prop) (p l : Point K) : Prop :=
  l = lineThrough p (l 0) ∧ A p (l 0)

abbrev graph (A : Point K → K → Prop) := Erdos713C6.bipGraph (Rel A)

def coef (a b : K) := a^2+a*b+b^2

def planeCoords (a b : K) (p : Point K) : (K × K) × (K × K) :=
  ((p 2-(a+b)*p 1+a*b*p 0,p 3-coef a b*p 1+a*b*(a+b)*p 0),
    (p 1-a*p 0,p 1-b*p 0))

def point (a b : K) (r : K × K) (u v : K) : Point K :=
  let x := (v-u)/(a-b)
  ![x,u+a*x,(a+b)*u+r.1+a^2*x,coef a b*u+r.2+a^3*x]

def axisLine (a b : K) (r : K × K) (u : K) : Point K :=
  ![a,u,(a+b)*u+r.1,coef a b*u+r.2]

lemma plane_point (a b : K) (hab : a ≠ b) (r : K × K) (u v : K) :
    planeCoords a b (point a b r u v) = (r,(u,v)) := by
  have hn := sub_ne_zero.mpr hab
  apply Prod.ext <;> apply Prod.ext <;>
    dsimp [planeCoords,point,coef] <;> field_simp <;> ring

lemma point_plane (a b : K) (hab : a ≠ b) (p : Point K) :
    point a b (planeCoords a b p).1 (planeCoords a b p).2.1 (planeCoords a b p).2.2 = p := by
  have hn := sub_ne_zero.mpr hab
  funext i
  fin_cases i <;> dsimp [point,planeCoords,coef] <;> field_simp <;> ring

def planeEquiv (a b : K) (hab : a ≠ b) : Point K ≃ (K × K) × (K × K) where
  toFun := planeCoords a b
  invFun := fun z => point a b z.1 z.2.1 z.2.2
  left_inv := point_plane a b hab
  right_inv := fun z => plane_point a b hab z.1 z.2.1 z.2.2

lemma point_inj (a b : K) (hab : a ≠ b) (r : K × K) {u v x y : K}
    (hh : point a b r u v = point a b r x y) : u = x ∧ v = y := by
  have he := congrArg (planeCoords a b) hh
  rw [plane_point a b hab,plane_point a b hab] at he
  exact Prod.mk.inj (Prod.mk.inj he).2

lemma line_point_left (a b : K) (r : K × K) (u v : K) :
    lineThrough (point a b r u v) a = axisLine a b r u := by
  funext i
  fin_cases i <;> dsimp [lineThrough,point,axisLine] <;> ring

lemma line_point_right (a b : K) (hab : a ≠ b) (r : K × K) (u v : K) :
    lineThrough (point a b r u v) b = axisLine b a r v := by
  have hn := sub_ne_zero.mpr hab
  funext i
  fin_cases i <;> dsimp [lineThrough,point,axisLine,coef] <;> field_simp <;> ring

lemma edge_left (A : Point K → K → Prop) (a b : K) (r : K × K) (u v : K)
    (h : A (point a b r u v) a) : Rel A (point a b r u v) (axisLine a b r u) := by
  exact ⟨(line_point_left a b r u v).symm,h⟩

lemma edge_right (A : Point K → K → Prop) (a b : K) (hab : a ≠ b) (r : K × K) (u v : K)
    (h : A (point a b r u v) b) : Rel A (point a b r u v) (axisLine b a r v) := by
  exact ⟨(line_point_right a b hab r u v).symm,h⟩

lemma contains_of_octagon {P L : Type*} (R : P → L → Prop)
    (p : Fin 4 → P) (l : Fin 4 → L) (hp : Function.Injective p) (hl : Function.Injective l)
    (hA : ∀ i, R (p i) (l i)) (hB : ∀ i, R (p (i+1)) (l i)) :
    cycleGraph 8 ⊑ Erdos713C6.bipGraph R := by
  let c : Fin 8 → P ⊕ L :=
    ![Sum.inl (p 0), Sum.inr (l 0), Sum.inl (p 1), Sum.inr (l 1),
      Sum.inl (p 2), Sum.inr (l 2), Sum.inl (p 3), Sum.inr (l 3)]
  have hA0 := hA 0; have hA1 := hA 1; have hA2 := hA 2; have hA3 := hA 3
  have hB0 := hB 0; have hB1 := hB 1; have hB2 := hB 2; have hB3 := hB 3
  refine ⟨⟨⟨c,?_⟩,?_⟩⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      first | exact absurd hij (by decide) |
        simpa [c, Erdos713C6.bipGraph] using hA0 |
        simpa [c, Erdos713C6.bipGraph] using hA1 |
        simpa [c, Erdos713C6.bipGraph] using hA2 |
        simpa [c, Erdos713C6.bipGraph] using hA3 |
        simpa [c, Erdos713C6.bipGraph] using hB0 |
        simpa [c, Erdos713C6.bipGraph] using hB1 |
        simpa [c, Erdos713C6.bipGraph] using hB2 |
        simpa [c, Erdos713C6.bipGraph] using hB3
  · intro i j hij
    change c i = c j at hij
    fin_cases i <;> fin_cases j <;> simp_all [c, hp.eq_iff, hl.eq_iff]


def grid (A : Point K → K → Prop) (a b : K) (r : K × K) (u v : K) : Prop :=
  A (point a b r u v) a ∧ A (point a b r u v) b

lemma grid_four_free (A : Point K → K → Prop) (hf : (cycleGraph 8).Free (graph A))
    (a b : K) (hab : a ≠ b) (r : K × K) : Erdos713ThetaC4Deletion.FourFree (grid A a b r) := by
  intro u x v y h00 h01 h10 h11
  by_contra hne
  push_neg at hne
  obtain ⟨hux,hvy⟩ := hne
  let p : Fin 4 → Point K := ![point a b r u v,point a b r u y,point a b r x y,point a b r x v]
  let l : Fin 4 → Point K := ![axisLine a b r u,axisLine b a r y,axisLine a b r x,axisLine b a r v]
  have hp : Function.Injective p := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> try rfl
    all_goals
      have hh := point_inj a b hab r hij
      simp_all
  have hl : Function.Injective l := by
    intro i j hij
    have h0 := congrFun hij 0
    have h1 := congrFun hij 1
    fin_cases i <;> fin_cases j <;> simp_all [l,axisLine]
  apply hf (contains_of_octagon (Rel A) p l hp hl ?_ ?_)
  · intro i
    fin_cases i
    · exact edge_left A a b r u v h00.1
    · exact edge_right A a b hab r u y h01.2
    · exact edge_left A a b r x y h11.1
    · exact edge_right A a b hab r x v h10.2
  · intro i
    fin_cases i
    · exact edge_left A a b r u y h01.1
    · exact edge_right A a b hab r x y h11.2
    · exact edge_left A a b r x v h10.1
    · exact edge_right A a b hab r u v h00.2

#print axioms grid_four_free
end Erdos713WengerRestriction
