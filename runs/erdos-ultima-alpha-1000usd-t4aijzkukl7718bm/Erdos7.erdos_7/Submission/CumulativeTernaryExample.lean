import FormalConjecturesUtil

/-! A finite positive example of a cumulative-slice coupling improvement.
This certifies a comparison of finite scores, NOT nonexistence of odd covers. -/
namespace Erdos7CumulativeTernaryExample
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 3000000

/-- Residues left after deleting 0 modulo3, 1 modulo9, and 2 modulo27. -/
def point : Fin 14 → ℕ := ![4,5,7,8,11,13,14,16,17,20,22,23,25,26]
def cell : Fin 5 → ℕ := ![2,4,5,7,8]
def short (a : Fin 140) : Bool := a.val<70

def count (a : Fin 140) (x : Fin 14) : ℕ :=
  1+(if point x%3=(if short a then 1 else 2) then 1 else 0)+
    (if point x%9=cell ⟨a.val/14%5,Nat.mod_lt _ (by decide)⟩ then 1 else 0)+
    (if x.val=a.val%14 then 1 else 0)

def keep (x : Fin 14) : Bool := count 74 x<4
def firstWeight (x : Fin 14) : ℕ := 16-5*count 74 x

def meanNum (a : Fin 140) : ℕ := ∑ x,if keep x then count a x else 0
def firstNum (a : Fin 140) : ℕ := ∑ x,firstWeight x*(count a x-3)
def zeroNum (a : Fin 140) : ℕ := ∑ x,if keep x ∧ count a x=1 then 1 else 0
def bothNum (a b : Fin 140) : ℕ :=
  ∑ x,if keep x ∧ count a x=1 ∧ count b x=1 then 1 else 0

def pairScore (a b : Fin 140) : ℕ :=
  5*firstNum a+20*meanNum a+20*meanNum b+16*bothNum a b

def jensenScore (a : Fin 140) : ℕ :=
  5*firstNum a+20*meanNum a+480+8*(zeroNum a+6)

lemma geometry : (∀ x,point x%3=1 ∨ point x%3=2) ∧
    (∀ x,point x%9≠1 ∧ point x≠2) ∧ Function.Injective point := by
  decide +kernel

/-- Only one-slice tables are needed; the pair maximum is proved below. -/
lemma single_bounds : ∀ a : Fin 140,
    meanNum a ≤ (if short a then 23 else 24) ∧
    firstNum a ≤ (if short a then 11 else 6) ∧
    zeroNum a ≤ (if short a then 7 else 6) := by
  decide +kernel

lemma one_excludes_branch (a : Fin 140) (x : Fin 14) (hc : count a x=1) :
    point x%3≠(if short a then 1 else 2) := by
  intro hh
  simp only [count,if_pos hh] at hc
  omega

lemma both_le_zero (a b : Fin 140) : bothNum a b ≤ zeroNum a := by
  unfold bothNum zeroNum
  apply Finset.sum_le_sum
  intro x _
  split_ifs <;> simp_all

lemma both_zero_of_ne (a b : Fin 140) (hab : short a≠short b) : bothNum a b=0 := by
  unfold bothNum
  apply Finset.sum_eq_zero
  intro x _
  apply if_neg
  rintro ⟨_,ha,hb⟩
  have h₁ := one_excludes_branch a x ha
  have h₂ := one_excludes_branch b x hb
  have hx := geometry.1 x
  cases hsa : short a <;> cases hsb : short b <;> simp_all

/-- Exact maximum of the coupled two-slice score. -/
theorem pair_bound (a b : Fin 140) : pairScore a b ≤ 1087 := by
  have ha := single_bounds a
  have hb := single_bounds b
  have hz := both_le_zero a b
  by_cases he : short a=short b
  · cases hsa : short a <;> have hsb := he.symm.trans hsa <;>
      simp only [hsa,hsb,Bool.false_eq_true,↓reduceIte] at ha hb <;>
      unfold pairScore <;> omega
  · have hh := both_zero_of_ne a b he
    cases hsa : short a <;> cases hsb : short b <;>
      simp only [hsa,hsb,Bool.false_eq_true,↓reduceIte] at ha hb he <;>
      unfold pairScore <;> omega

lemma pair_attained : pairScore 14 14=1087 := by decide +kernel

/-- Exact maximum when the later slice is replaced by the common Jensen law. -/
theorem jensen_bound (a : Fin 140) : jensenScore a ≤ 1099 := by
  have ha := single_bounds a
  cases hsa : short a <;>
    simp only [hsa,Bool.false_eq_true,↓reduceIte] at ha <;>
    unfold jensenScore <;> omega

lemma jensen_attained : jensenScore 14=1099 := by decide +kernel

/-- The common dominating slice has weighted masses6,4,2,1 at counts1,2,3,4. -/
lemma dominant_hinges : (∀ (a : Fin 140) (t : Fin 4),
    (∑ x,if keep x then count a x-t.val else 0) ≤
      ∑ x,if keep x then count 99 x-t.val else 0) ∧
    meanNum 99=24 ∧ zeroNum 99=6 := by
  decide +kernel

def pairValue (a b : Fin 140) : ℚ := ((pairScore a b : ℚ)-660)/1400
def jensenValue (a : Fin 140) : ℚ := ((jensenScore a : ℚ)-660)/1400

theorem exact_values : (∀ a b,pairValue a b ≤ 61/200) ∧
    pairValue 14 14=61/200 ∧ (∀ a,jensenValue a ≤ 439/1400) ∧
    jensenValue 14=439/1400 ∧ pairValue 14 14+3/350=jensenValue 14 := by
  have hp (a b : Fin 140) : (pairScore a b : ℚ) ≤ 1087 := by exact_mod_cast pair_bound a b
  have hj (a : Fin 140) : (jensenScore a : ℚ) ≤ 1099 := by exact_mod_cast jensen_bound a
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro a b; dsimp [pairValue]; linarith [hp a b]
  · simp [pairValue,pair_attained]; norm_num
  · intro a; dsimp [jensenValue]; linarith [hj a]
  · simp [jensenValue,jensen_attained]; norm_num
  · simp [pairValue,jensenValue,pair_attained,jensen_attained]; norm_num

#print axioms pair_bound
#print axioms dominant_hinges
#print axioms exact_values
end Erdos7CumulativeTernaryExample
