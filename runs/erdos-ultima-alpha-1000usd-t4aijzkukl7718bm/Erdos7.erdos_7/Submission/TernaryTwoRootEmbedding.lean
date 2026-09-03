import Submission.TernaryTwoCoherentMixture

/-! Five ternary survivors avoiding any specified pure3 and pure9 classes.
The two coarse branches have exactly sizes two and three. -/
namespace Erdos7TernaryTwoRootEmbedding
open Erdos7TernaryTwoCoherentMixture
set_option maxHeartbeats 3000000

def canonical : Fin 5 → ℕ := ![4,7,2,5,8]
def extraPoint (a : Fin 3) (b : Fin 9) : ℕ :=
  if b.val%3=a.val then a.val+1 else b.val
def unit (a : Fin 3) (b : Fin 9) : ℕ := (extraPoint a b+9-a.val)%9
def point (a : Fin 3) (b : Fin 9) (x : Fin 5) : Fin 9 :=
  ⟨(a.val+unit a b*canonical x)%9,Nat.mod_lt _ (by omega)⟩

lemma point_injective : ∀ a b,Function.Injective (point a b) := by decide +kernel
lemma point_avoids : ∀ a b x,(point a b x).val%3≠a.val ∧ point a b x≠b := by decide +kernel
lemma branches : ∀ a b (r : Fin 3),∃ q : Fin 2,
    ∀ x,(point a b x).val%3=r.val → branch x=q := by decide +kernel
lemma cells : ∀ a b (r : Fin 9),∃ y : Fin 5,
    ∀ x,point a b x=r → x=y := by decide +kernel
lemma branch_sizes : ∀ q : Fin 2,
    (Finset.univ.filter (fun x : Fin 5 => branch x=q)).card=if q.val=0 then 2 else 3 := by
  decide +kernel

/-- This includes the case where the old pure9 class is already contained
in the pure3 class: the extra deleted point is then chosen elsewhere. -/
theorem avoids_pure_classes : ∀ a b x,
    ¬ (3 : ℤ)∣((point a b x).val : ℤ)-(a.val : ℤ) ∧
    ¬ (9 : ℤ)∣((point a b x).val : ℤ)-(b.val : ℤ) := by
  decide +kernel

/-- Every mod3 section is bounded by one complete coarse branch, and every
mod9 section by one point. Empty restricted sections may be padded. -/
theorem sections (a : Fin 3) (b : Fin 9) :
    (∀ r : Fin 3,∃ q : Fin 2,∀ x,
      (if (point a b x).val%3=r.val then (1:ℝ) else 0) ≤
      (if branch x=q then (1:ℝ) else 0)) ∧
    (∀ r : Fin 9,∃ y : Fin 5,∀ x,
      (if point a b x=r then (1:ℝ) else 0) ≤ (if x=y then (1:ℝ) else 0)) := by
  constructor
  · intro r
    obtain ⟨q,hq⟩ := branches a b r
    refine ⟨q,fun x => ?_⟩
    by_cases h : (point a b x).val%3=r.val
    · simp only [if_pos h,if_pos (hq x h),le_refl]
    · simp [h]; split_ifs <;> norm_num
  · intro r
    obtain ⟨y,hy⟩ := cells a b r
    refine ⟨y,fun x => ?_⟩
    by_cases h : point a b x=r
    · simp only [if_pos h,if_pos (hy x h),le_refl]
    · simp [h]; split_ifs <;> norm_num

#print axioms point_injective
#print axioms avoids_pure_classes
#print axioms sections
end Erdos7TernaryTwoRootEmbedding
