import FormalConjecturesUtil
import Submission.WengerRestrictionGeometry

/-! Permutation lifts of the four-coordinate Wenger graph require many
sheets to avoid C8. This is a construction obstruction, not Erdős 713. -/
open SimpleGraph
namespace Erdos713WengerCover
open Erdos713WengerRestriction
variable {K S : Type*} [Field K]
set_option maxHeartbeats 2000000

/-- An arbitrary permutation is assigned to each base incidence. This
models a uniform sheeted graph cover without an abelian-voltage assumption. -/
def Rel (sigma : Point K → K → Equiv.Perm S)
    (p l : Point K × S) : Prop :=
  l.1=lineThrough p.1 (l.1 0) ∧ l.2=sigma p.1 (l.1 0) p.2

abbrev graph (sigma : Point K → K → Equiv.Perm S) := Erdos713C6.bipGraph (Rel sigma)

def nearPoint (sigma : Point K → K → Equiv.Perm S)
    (a b : K) (r : K × K) (u v : K) (i : S) : Point K × S :=
  (point a b r u v,(sigma (point a b r u v) a).symm i)

def middleSheet (sigma : Point K → K → Equiv.Perm S)
    (a b : K) (r : K × K) (u v : K) (i : S) : S :=
  sigma (point a b r u v) b (nearPoint sigma a b r u v i).2

def farPoint (sigma : Point K → K → Equiv.Perm S)
    (a b : K) (r : K × K) (u x v : K) (i : S) : Point K × S :=
  (point a b r x v,(sigma (point a b r x v) b).symm (middleSheet sigma a b r u v i))

def endSheet (sigma : Point K → K → Equiv.Perm S)
    (a b : K) (r : K × K) (u x v : K) (i : S) : S :=
  sigma (point a b r x v) a (farPoint sigma a b r u x v i).2

lemma near_left (sigma : Point K → K → Equiv.Perm S)
    (a b : K) (r : K × K) (u v : K) (i : S) :
    Rel sigma (nearPoint sigma a b r u v i) (axisLine a b r u,i) := by
  constructor
  · exact (line_point_left a b r u v).symm
  · simp [nearPoint,axisLine]

lemma near_right (sigma : Point K → K → Equiv.Perm S)
    (a b : K) (hab : a ≠ b) (r : K × K) (u v : K) (i : S) :
    Rel sigma (nearPoint sigma a b r u v i)
      (axisLine b a r v,middleSheet sigma a b r u v i) := by
  exact ⟨(line_point_right a b hab r u v).symm,rfl⟩

lemma far_right (sigma : Point K → K → Equiv.Perm S)
    (a b : K) (hab : a ≠ b) (r : K × K) (u x v : K) (i : S) :
    Rel sigma (farPoint sigma a b r u x v i)
      (axisLine b a r v,middleSheet sigma a b r u v i) := by
  constructor
  · exact (line_point_right a b hab r x v).symm
  · simp [farPoint,axisLine]

lemma far_left (sigma : Point K → K → Equiv.Perm S)
    (a b : K) (r : K × K) (u x v : K) (i : S) :
    Rel sigma (farPoint sigma a b r u x v i)
      (axisLine a b r x,endSheet sigma a b r u x v i) := by
  exact ⟨(line_point_left a b r x v).symm,rfl⟩

/-- Different intermediate b-lines give internally disjoint base paths.
A collision of lifted endpoints therefore produces an injective C8. -/
theorem contains_of_endpoint_collision (sigma : Point K → K → Equiv.Perm S)
    (a b : K) (hab : a ≠ b) (r : K × K) (u x : K) (hux : u ≠ x)
    (i : S) (v w : K) (hvw : v ≠ w)
    (hEnd : endSheet sigma a b r u x v i=endSheet sigma a b r u x w i) :
    cycleGraph 8 ⊑ graph sigma := by
  let p : Fin 4 → Point K × S :=
    ![nearPoint sigma a b r u v i,nearPoint sigma a b r u w i,
      farPoint sigma a b r u x w i,farPoint sigma a b r u x v i]
  let l : Fin 4 → Point K × S :=
    ![(axisLine a b r u,i),(axisLine b a r w,middleSheet sigma a b r u w i),
      (axisLine a b r x,endSheet sigma a b r u x v i),
      (axisLine b a r v,middleSheet sigma a b r u v i)]
  have hp : Function.Injective p := by
    intro j k he
    have hh := congrArg Prod.fst he
    fin_cases j <;> fin_cases k <;> try rfl
    all_goals
      have h := point_inj a b hab r hh
      simp_all
  have hl : Function.Injective l := by
    intro j k he
    have h0 := congrArg (fun z : Point K × S => z.1 0) he
    have h1 := congrArg (fun z : Point K × S => z.1 1) he
    fin_cases j <;> fin_cases k <;> simp_all [l,axisLine]
  apply Erdos713WengerRestriction.contains_of_octagon (Rel sigma) p l hp hl
  · intro j
    fin_cases j
    · exact near_left sigma a b r u v i
    · exact near_right sigma a b hab r u w i
    · change Rel sigma (farPoint sigma a b r u x w i)
        (axisLine a b r x,endSheet sigma a b r u x v i)
      rw [hEnd]
      exact far_left sigma a b r u x w i
    · exact far_right sigma a b hab r u x v i
  · intro j
    fin_cases j
    · exact near_left sigma a b r u w i
    · exact far_right sigma a b hab r u x w i
    · exact far_left sigma a b r u x v i
    · exact near_right sigma a b hab r u v i

/-- For a C8-free cover, all q four-step lifts have distinct endpoints
in one fixed sheet fiber. -/
theorem endpoint_injective (sigma : Point K → K → Equiv.Perm S)
    (hf : (cycleGraph 8).Free (graph sigma))
    (a b : K) (hab : a ≠ b) (r : K × K) (u x : K) (hux : u ≠ x) (i : S) :
    Function.Injective (fun v => endSheet sigma a b r u x v i) := by
  intro v w h
  by_contra hvw
  exact hf (contains_of_endpoint_collision sigma a b hab r u x hux i v w hvw h)

/-- At least q sheets are necessary, regardless of the permutation labels. -/
theorem field_card_le_sheets [Fintype K] [Fintype S] [Nonempty S]
    (sigma : Point K → K → Equiv.Perm S) (hf : (cycleGraph 8).Free (graph sigma)) :
    Fintype.card K ≤ Fintype.card S := by
  obtain ⟨i⟩ := ‹Nonempty S›
  exact Fintype.card_le_of_injective _
    (endpoint_injective sigma hf 0 1 zero_ne_one (0,0) 0 1 zero_ne_one i)

end Erdos713WengerCover
