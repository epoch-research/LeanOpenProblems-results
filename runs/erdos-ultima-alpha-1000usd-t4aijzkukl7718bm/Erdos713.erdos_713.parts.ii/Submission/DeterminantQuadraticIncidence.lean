import FormalConjecturesUtil
import Submission.DeterminantQuadraticGeometry
import Submission.GlobalLightPairs
import Submission.ThetaCrossCompletion

/-! A five-parameter determinant-one quadratic incidence family. No theta
exclusion is claimed; it is used to test weaker column-link conditions. -/
open Finset
open scoped Classical
namespace Erdos713DeterminantQuadraticIncidence
open Erdos713DeterminantQuadraticGeometry Erdos713GlobalLight Erdos713ThetaCross
variable {K : Type*} [Field K]
set_option maxHeartbeats 2000000

abbrev Params (K : Type*) [Field K] := Kˣ × K × K
abbrev Rows (K : Type*) [Field K] := Params K × Vec K
abbrev Cols (K : Type*) := K × Vec K

def coeff (p : Rows K) : Quad K :=
  ((p.1.1,p.1.2.1),(p.1.2.2,(1+p.1.2.1*p.1.2.2)/(p.1.1 : K)),p.2)

def incidence (p : Rows K) (x : Cols K) : Prop := eval (coeff p) x.1 = x.2

lemma coeff_admissible (p : Rows K) : Admissible (coeff p) := by
  dsimp [Admissible,det,coeff]
  field_simp
  ring

lemma coeff_injective : Function.Injective (coeff (K := K)) := by
  intro p q h
  apply Prod.ext
  · refine Prod.ext (Units.ext (congrArg (fun f : Quad K => f.1.1) h)) ?_
    exact Prod.ext (congrArg (fun f : Quad K => f.1.2) h)
      (congrArg (fun f : Quad K => f.2.1.1) h)
  · exact congrArg (fun f : Quad K => f.2.2) h

def rowEquiv (p : Rows K) : K ≃ {x : Cols K // incidence p x} where
  toFun t := ⟨(t,eval (coeff p) t),rfl⟩
  invFun x := x.val.1
  left_inv _ := rfl
  right_inv x := Subtype.ext (Prod.ext rfl x.property)

def columnEquiv (x : Cols K) : Params K ≃ {p : Rows K // incidence p x} where
  toFun s := ⟨(s,(x.2.1-(s.1 : K)*x.1^2-s.2.2*x.1,
    x.2.2-s.2.1*x.1^2-((1+s.2.1*s.2.2)/(s.1 : K))*x.1)),by
      apply Prod.ext <;> dsimp [incidence,eval,coeff] <;> ring⟩
  invFun p := p.val.1
  left_inv _ := rfl
  right_inv p := by
    apply Subtype.ext
    refine Prod.ext ?_ ?_
    · rfl
    have h1 := congrArg Prod.fst p.property
    have h2 := congrArg Prod.snd p.property
    dsimp [incidence,eval,coeff] at h1 h2
    apply Prod.ext
    · dsimp; linear_combination -h1
    · dsimp; linear_combination -h2

def edgeEquiv : Rows K × K ≃ {p : Rows K × Cols K // incidence p.1 p.2} where
  toFun p := ⟨(p.1,(p.2,eval (coeff p.1) p.2)),rfl⟩
  invFun p := (p.val.1,p.val.2.1)
  left_inv _ := rfl
  right_inv p := Subtype.ext (Prod.ext rfl (Prod.ext rfl p.property))

lemma params_card [Fintype K] : Nat.card (Params K) = (Nat.card K-1)*(Nat.card K)^2 := by
  simp only [Params,Nat.card_prod,Nat.card_units,pow_two]

lemma rows_card [Fintype K] : Nat.card (Rows K) = (Nat.card K-1)*(Nat.card K)^4 := by
  rw [Rows,Nat.card_prod,params_card]
  simp only [Vec,Nat.card_prod]
  ring

omit [Field K] in
lemma cols_card : Nat.card (Cols K) = (Nat.card K)^3 := by
  simp only [Cols,Vec,Nat.card_prod]
  ring

lemma row_card (p : Rows K) : Nat.card {x : Cols K // incidence p x} = Nat.card K :=
  (Nat.card_congr (rowEquiv p)).symm

lemma column_card [Fintype K] (x : Cols K) :
    Nat.card {p : Rows K // incidence p x} = (Nat.card K-1)*(Nat.card K)^2 :=
  (Nat.card_congr (columnEquiv x)).symm.trans params_card

lemma edge_card [Fintype K] :
    Nat.card {p : Rows K × Cols K // incidence p.1 p.2} = (Nat.card K-1)*(Nat.card K)^5 := by
  rw [← Nat.card_congr (edgeEquiv (K := K)),Nat.card_prod,rows_card]
  ring

/-- Interpolate at two columns, with the nonzero leading first coordinate
as a free parameter. The value's first coordinates must differ. -/
def interpolate (x y : Cols K) (a : Kˣ) : Rows K :=
  let b := ((a : K)*(y.2.2-x.2.2)-(y.1-x.1))/(y.2.1-x.2.1)
  let c := (y.2.1-x.2.1)/(y.1-x.1)-(a : K)*(y.1+x.1)
  ((a,b,c),(x.2.1-(a : K)*x.1^2-c*x.1,
    x.2.2-b*x.1^2-((1+b*c)/(a : K))*x.1))

lemma interpolate_left (x y : Cols K) (a : Kˣ) : incidence (interpolate x y a) x := by
  apply Prod.ext <;> dsimp [incidence,eval,coeff,interpolate] <;> ring

lemma interpolate_right (x y : Cols K) (a : Kˣ)
    (hxy : y.1 ≠ x.1) (hval : y.2.1 ≠ x.2.1) : incidence (interpolate x y a) y := by
  have ht : y.1-x.1 ≠ 0 := sub_ne_zero.mpr hxy
  have hv : y.2.1-x.2.1 ≠ 0 := sub_ne_zero.mpr hval
  apply Prod.ext <;> dsimp [incidence,eval,coeff,interpolate] <;>
    field_simp <;> ring

lemma codegree_lower [Fintype K] (x y : Cols K)
    (hxy : x.1 ≠ y.1) (hval : x.2.1 ≠ y.2.1) :
    Nat.card K-1 ≤ codegree (incidence (K := K)) x y := by
  let f : Kˣ → {p : Rows K // incidence p x ∧ incidence p y} := fun a =>
    ⟨interpolate x y a,interpolate_left x y a,interpolate_right x y a hxy.symm hval.symm⟩
  have hi : Function.Injective f := by
    intro a b h
    exact congrArg (fun p : {p : Rows K // incidence p x ∧ incidence p y} => p.val.1.1) h
  simpa only [Nat.card_units] using Nat.card_le_card_of_injective f hi

#print axioms coeff_admissible
#print axioms edge_card
#print axioms codegree_lower
end Erdos713DeterminantQuadraticIncidence
