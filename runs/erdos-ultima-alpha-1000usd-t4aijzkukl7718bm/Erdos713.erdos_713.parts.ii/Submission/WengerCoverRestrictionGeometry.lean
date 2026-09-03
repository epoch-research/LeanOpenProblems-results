import FormalConjecturesUtil
import Submission.WengerCoverGeometry

/-! Two-slope grids in arbitrary edge restrictions of permutation lifts.
This is auxiliary construction analysis, not a solution of Erdős 713. -/
open SimpleGraph
namespace Erdos713WengerCoverRestriction
open Erdos713WengerRestriction
variable {K S : Type*} [Field K]
set_option maxHeartbeats 2000000

def Rel (sigma : Point K → K → Equiv.Perm S) (A : (Point K × S) → K → Prop)
    (p l : Point K × S) : Prop :=
  Erdos713WengerCover.Rel sigma p l ∧ A p (l.1 0)

abbrev graph (sigma : Point K → K → Equiv.Perm S) (A : (Point K × S) → K → Prop) :=
  Erdos713C6.bipGraph (Rel sigma A)

def pointLift (sigma : Point K → K → Equiv.Perm S)
    (a b : K) (r : K × K) (u : K × S) (v : K) : Point K × S :=
  (point a b r u.1 v,(sigma (point a b r u.1 v) a).symm u.2)

def grid (sigma : Point K → K → Equiv.Perm S) (A : (Point K × S) → K → Prop)
    (a b : K) (r : K × K) (u v : K × S) : Prop :=
  v.2=sigma (point a b r u.1 v.1) b (pointLift sigma a b r u v.1).2 ∧
    A (pointLift sigma a b r u v.1) a ∧ A (pointLift sigma a b r u v.1) b

lemma pointLift_endpoints (sigma : Point K → K → Equiv.Perm S)
    (A : (Point K × S) → K → Prop) (a b : K) (hab : a ≠ b) (r : K × K)
    {u v x y : K × S} (huv : grid sigma A a b r u v) (hxy : grid sigma A a b r x y)
    (he : pointLift sigma a b r u v.1=pointLift sigma a b r x y.1) : u=x ∧ v=y := by
  obtain ⟨hu,hv⟩ := point_inj a b hab r (congrArg Prod.fst he)
  have hp : point a b r u.1 v.1=point a b r x.1 y.1 := by rw [hu,hv]
  have hi := congrArg Prod.snd he
  change (sigma (point a b r u.1 v.1) a).symm u.2 =
    (sigma (point a b r x.1 y.1) a).symm x.2 at hi
  rw [hp] at hi
  have hs : u.2=x.2 := (sigma (point a b r x.1 y.1) a).symm.injective hi
  refine ⟨Prod.ext hu hs,Prod.ext hv ?_⟩
  calc
    v.2 = sigma (point a b r u.1 v.1) b (pointLift sigma a b r u v.1).2 := huv.1
    _ = sigma (point a b r x.1 y.1) b (pointLift sigma a b r x y.1).2 := by rw [hp,he]
    _ = y.2 := hxy.1.symm

lemma grid_edge_left (sigma : Point K → K → Equiv.Perm S)
    (A : (Point K × S) → K → Prop) (a b : K) (r : K × K)
    {u v : K × S} (h : grid sigma A a b r u v) :
    Rel sigma A (pointLift sigma a b r u v.1) (axisLine a b r u.1,u.2) := by
  refine ⟨⟨(line_point_left a b r u.1 v.1).symm,?_⟩,h.2.1⟩
  simp [pointLift,axisLine]

lemma grid_edge_right (sigma : Point K → K → Equiv.Perm S)
    (A : (Point K × S) → K → Prop) (a b : K) (hab : a ≠ b) (r : K × K)
    {u v : K × S} (h : grid sigma A a b r u v) :
    Rel sigma A (pointLift sigma a b r u v.1) (axisLine b a r v.1,v.2) :=
  ⟨⟨(line_point_right a b hab r u.1 v.1).symm,h.1⟩,h.2.2⟩

/-- Repeated base coordinates are allowed: distinct lifted line vertices
still give four distinct lifted intersection points. -/
theorem grid_four_free (sigma : Point K → K → Equiv.Perm S)
    (A : (Point K × S) → K → Prop) (hf : (cycleGraph 8).Free (graph sigma A))
    (a b : K) (hab : a ≠ b) (r : K × K) :
    Erdos713ThetaC4Deletion.FourFree (grid sigma A a b r) := by
  intro u x v y h00 h01 h10 h11
  by_contra hne
  push_neg at hne
  obtain ⟨hux,hvy⟩ := hne
  let p : Fin 4 → Point K × S :=
    ![pointLift sigma a b r u v.1,pointLift sigma a b r u y.1,
      pointLift sigma a b r x y.1,pointLift sigma a b r x v.1]
  let l : Fin 4 → Point K × S :=
    ![(axisLine a b r u.1,u.2),(axisLine b a r y.1,y.2),
      (axisLine a b r x.1,x.2),(axisLine b a r v.1,v.2)]
  have hp : Function.Injective p := by
    intro j k he
    fin_cases j <;> fin_cases k <;> try rfl
    all_goals
      have hh := pointLift_endpoints sigma A a b hab r (by assumption) (by assumption) he
      simp_all
  have hl : Function.Injective l := by
    intro j k he
    have h0 := congrArg (fun z : Point K × S => z.1 0) he
    have h1 := congrArg (fun z : Point K × S => z.1 1) he
    have h2 := congrArg Prod.snd he
    fin_cases j <;> fin_cases k <;> simp_all [l,axisLine,Prod.ext_iff]
  apply hf (Erdos713WengerRestriction.contains_of_octagon (Rel sigma A) p l hp hl ?_ ?_)
  · intro j
    fin_cases j
    · exact grid_edge_left sigma A a b r h00
    · exact grid_edge_right sigma A a b hab r h01
    · exact grid_edge_left sigma A a b r h11
    · exact grid_edge_right sigma A a b hab r h10
  · intro j
    fin_cases j
    · exact grid_edge_left sigma A a b r h01
    · exact grid_edge_right sigma A a b hab r h11
    · exact grid_edge_left sigma A a b r h10
    · exact grid_edge_right sigma A a b hab r h00

/-- Plane coordinates augmented by the sheet on the a-line. -/
def planeEquiv (sigma : Point K → K → Equiv.Perm S) (a b : K) (hab : a ≠ b) :
    (Point K × S) ≃ (K × K) × ((K × S) × K) where
  toFun p := ((planeCoords a b p.1).1,
    (((planeCoords a b p.1).2.1,sigma p.1 a p.2),(planeCoords a b p.1).2.2))
  invFun z := pointLift sigma a b z.1 z.2.1 z.2.2
  left_inv p := by
    apply Prod.ext
    · exact point_plane a b hab p.1
    · simp only [pointLift,point_plane a b hab,Equiv.symm_apply_apply]
  right_inv z := by
    rcases z with ⟨r,⟨u,v⟩⟩
    simp [pointLift,plane_point a b hab]

end Erdos713WengerCoverRestriction
