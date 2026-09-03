import Submission.Shared47DistinctBoxes
import Submission.TernaryTwoRootEmbedding

/-! Exact ternary residue geometry for the finite prime-47 obstruction. -/
namespace Erdos7Shared47TernaryArithmetic
open Erdos7Shared47DistinctBoxes Erdos7TernaryTwoRootEmbedding
open Erdos7TernaryTwoCoherentMixture
set_option maxHeartbeats 3000000
set_option autoImplicit false
attribute [local instance] Classical.propDecidable

lemma cast_three (z : Fin 9) (r : ZMod 3) :
    (z.val : ZMod 3)=r ↔ z.val%3=r.val := by
  constructor
  · intro h
    simpa only [ZMod.val_natCast] using congrArg ZMod.val h
  · intro h
    apply ZMod.val_injective 3
    simpa only [ZMod.val_natCast] using h

lemma cast_nine (z : Fin 9) (r : ZMod 9) :
    (z.val : ZMod 9)=r ↔ z.val=r.val := by
  constructor
  · intro h
    simpa only [ZMod.val_natCast,Nat.mod_eq_of_lt z.isLt] using congrArg ZMod.val h
  · intro h
    apply ZMod.val_injective 9
    simpa only [ZMod.val_natCast,Nat.mod_eq_of_lt z.isLt] using h

noncomputable def residue3 (a : ℤ) : Fin 3 := ⟨(a : ZMod 3).val,ZMod.val_lt _⟩
noncomputable def residue9 (a : ℤ) : Fin 9 := ⟨(a : ZMod 9).val,ZMod.val_lt _⟩

lemma point_avoids_cast (a b : ℤ) (x : Fin 5) :
    ((point (residue3 a) (residue9 b) x).val : ZMod 3)≠(a : ZMod 3) ∧
    ((point (residue3 a) (residue9 b) x).val : ZMod 9)≠(b : ZMod 9) := by
  have hh := point_avoids (residue3 a) (residue9 b) x
  constructor
  · intro h
    exact hh.1 ((cast_three _ _).mp h)
  · intro h
    exact hh.2 (Fin.ext ((cast_nine _ _).mp h))

lemma point_branch_cast (a b r : ℤ) : ∃ q : Fin 2,∀ x,
    ((point (residue3 a) (residue9 b) x).val : ZMod 3)=(r : ZMod 3) → branch x=q := by
  obtain ⟨q,hq⟩ := branches (residue3 a) (residue9 b) (residue3 r)
  exact ⟨q,fun x hx => hq x ((cast_three _ _).mp hx)⟩

lemma point_cell_cast (a b r : ℤ) : ∃ y : Fin 5,∀ x,
    ((point (residue3 a) (residue9 b) x).val : ZMod 9)=(r : ZMod 9) → x=y := by
  obtain ⟨y,hy⟩ := cells (residue3 a) (residue9 b) (residue9 r)
  exact ⟨y,fun x hx => hy x (Fin.ext ((cast_nine _ _).mp hx))⟩

def pure (d : ℕ) : Fin 14 → ℕ := Fin.cases d (fun _ => 0)

lemma eq_pure (e : Fin 14 → ℕ) (h : ∀ i : Fin 14, 1 ≤ i.val → e i=0) :
    e=pure (e 0) := by
  funext i
  cases i using Fin.cases with
  | zero => rfl
  | succ j => exact h j.succ (by simp only [Fin.val_succ]; omega)

noncomputable def pureResidue {κ : Type} (e : κ → Fin 14 → ℕ) (a : κ → ℤ) (d : ℕ) : ℤ :=
  if h : ∃ k,e k=pure d then a h.choose else 0

lemma pureResidue_eq {κ : Type} (e : κ → Fin 14 → ℕ) (he : Function.Injective e)
    (a : κ → ℤ) (k : κ) (d : ℕ) (hk : e k=pure d) : pureResidue e a d=a k := by
  classical
  have h : ∃ l,e l=pure d := ⟨k,hk⟩
  have hc : h.choose=k := he (h.choose_spec.trans hk.symm)
  simp only [pureResidue,dif_pos h,hc]

#print axioms point_avoids_cast
#print axioms point_branch_cast
#print axioms pureResidue_eq
end Erdos7Shared47TernaryArithmetic
