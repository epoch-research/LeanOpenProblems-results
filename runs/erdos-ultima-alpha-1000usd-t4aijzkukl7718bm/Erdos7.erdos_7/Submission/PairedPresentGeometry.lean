import Submission.PairedTernaryRoot
import Submission.TernaryTwoCurrentPadding

/-! Lower bounds from present first ternary cylinders. These describe actual
branch counts, but do not supply an unrestricted covering budget. -/
namespace Erdos7PairedPresentGeometry
open scoped BigOperators
open Erdos7PresentCylinderArithmetic Erdos7IndependentPureLifts
open Erdos7PairedTernaryRoot
set_option autoImplicit false
set_option maxHeartbeats 3000000

lemma first_cylinder_iff (E : ℕ) (a : ℕ → ℤ) (b c : ℤ)
    (x : ZMod (3^E)) (hx : x ∈ branchGood 3 E a b) :
    x ∈ cylinder 3 E 1 c ↔ (3 : ℤ) ∣ c-b := by
  have hb := ((mem_branchGood 3 E a b x).mp hx).1
  rw [mem_cylinder]
  norm_num only [pow_one, Nat.cast_ofNat]
  constructor
  · intro hc
    convert dvd_sub hb hc using 1; ring
  · intro hc
    convert dvd_sub hb hc using 1; ring

lemma ternary_nonzero_dichotomy (c : ℤ) (hc : ¬ (3 : ℤ) ∣ c) :
    ((3 : ℤ) ∣ c-1 ∧ ¬ (3 : ℤ) ∣ c-2) ∨
      (¬ (3 : ℤ) ∣ c-1 ∧ (3 : ℤ) ∣ c-2) := by
  simp only [Int.dvd_iff_emod_eq_zero] at hc ⊢
  omega

lemma first_pair_exact (E : ℕ) (a : ℕ → ℤ) (c : ℤ)
    (x y : ZMod (3^E)) (hx : x ∈ branchGood 3 E a 1)
    (hy : y ∈ branchGood 3 E a 2) (hc : ¬ (3 : ℤ) ∣ c) :
    (if x ∈ cylinder 3 E 1 c then (1:ℝ) else 0) +
      (if y ∈ cylinder 3 E 1 c then (1:ℝ) else 0) = 1 := by
  simp only [first_cylinder_iff E a 1 c x hx, first_cylinder_iff E a 2 c y hy]
  obtain (⟨h₁,h₂⟩ | ⟨h₁,h₂⟩) := ternary_nonzero_dichotomy c hc <;> simp [h₁,h₂]

noncomputable def count {X : Type*} [DecidableEq X]
    (C : ℕ → Finset X) (D : ℕ) (x : X) : ℝ :=
  1+∑ j ∈ Finset.range (D+1), if x ∈ C (j+1) then (1:ℝ) else 0

lemma count_ge_one {X : Type*} [DecidableEq X]
    (C : ℕ → Finset X) (D : ℕ) (x : X) : 1 ≤ count C D x := by
  unfold count
  have h : 0 ≤ ∑ j ∈ Finset.range (D+1), if x ∈ C (j+1) then (1:ℝ) else 0 := by
    apply Finset.sum_nonneg
    intro j hj
    split_ifs <;> norm_num
  linarith

lemma count_ge_first {X : Type*} [DecidableEq X]
    (C : ℕ → Finset X) (D : ℕ) (x : X) :
    1+(if x ∈ C 1 then (1:ℝ) else 0) ≤ count C D x := by
  unfold count
  rw [Finset.sum_range_succ']
  have h : 0 ≤ ∑ j ∈ Finset.range D, if x ∈ C (j+1+1) then (1:ℝ) else 0 := by
    apply Finset.sum_nonneg
    intro j hj
    split_ifs <;> norm_num
  simp only [Nat.zero_add]
  linarith

lemma pairAverage_eq_count {X : Type*} [DecidableEq X]
    (C : ℕ → Finset X) (D : ℕ) (x y : X) :
    pairAverage C D (x,y)=(count C D x+count C D y)/2 := rfl

/-- A present first cylinder outside the pure3 branch supplies one full
increment across the pair, even if the higher pure residues are arbitrary. -/
theorem arithmetic_count_sum_lower (D : ℕ) (a c : ℕ → ℤ)
    (x y : ZMod (3^(D+1))) (hx : x ∈ branchGood 3 (D+1) a 1)
    (hy : y ∈ branchGood 3 (D+1) a 2) (hc : ¬ (3 : ℤ) ∣ c 1) :
    3 ≤ count (fun e => cylinder 3 (D+1) e (c e)) D x +
      count (fun e => cylinder 3 (D+1) e (c e)) D y := by
  have h₁ := count_ge_first (fun e => cylinder 3 (D+1) e (c e)) D x
  have h₂ := count_ge_first (fun e => cylinder 3 (D+1) e (c e)) D y
  have h₃ := first_pair_exact (D+1) a (c 1) x y hx hy hc
  linarith

lemma arithmetic_pair_average_lower (D : ℕ) (a c : ℕ → ℤ)
    (x y : ZMod (3^(D+1))) (hx : x ∈ branchGood 3 (D+1) a 1)
    (hy : y ∈ branchGood 3 (D+1) a 2) (hc : ¬ (3 : ℤ) ∣ c 1) :
    3/2 ≤ pairAverage (fun e => cylinder 3 (D+1) e (c e)) D (x,y) := by
  rw [pairAverage_eq_count]
  have h := arithmetic_count_sum_lower D a c x y hx hy hc
  linarith

noncomputable def weighted {I X : Type*} [Fintype I] [DecidableEq X]
    (w : I → ℝ) (C : I → ℕ → Finset X) (D : ℕ) (x : X) : ℝ :=
  ∑ i, w i*count (C i) D x

lemma weighted_ge_one {I X : Type*} [Fintype I] [DecidableEq X]
    (w : I → ℝ) (hw : ∀ i, 0 ≤ w i) (hm : (∑ i, w i)=1)
    (C : I → ℕ → Finset X) (D : ℕ) (x : X) : 1 ≤ weighted w C D x := by
  calc
    _ = ∑ i, w i*1 := by simp [hm]
    _ ≤ _ := Finset.sum_le_sum (fun i _ =>
      mul_le_mul_of_nonneg_left (count_ge_one (C i) D x) (hw i))

lemma weighted_sum_lower {I X : Type*} [Fintype I] [DecidableEq X]
    (w : I → ℝ) (hw : ∀ i, 0 ≤ w i) (hm : (∑ i, w i)=1)
    (C : I → ℕ → Finset X) (D : ℕ) (x y : X)
    (hC : ∀ i, 3 ≤ count (C i) D x+count (C i) D y) :
    3 ≤ weighted w C D x+weighted w C D y := by
  have h := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset I)) =>
    mul_le_mul_of_nonneg_left (hC i) (hw i))
  simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hm, one_mul] at h
  exact h

/-- A single present family of weight w_j yields at least 1+w_j in
whichever branch its first cylinder meets. -/
lemma weighted_ge_one_add_weight {I X : Type*} [Fintype I] [DecidableEq X]
    (w : I → ℝ) (hw : ∀ i, 0 ≤ w i) (hm : (∑ i, w i)=1)
    (C : I → ℕ → Finset X) (D : ℕ) (x : X) (j : I) (hj : x ∈ C j 1) :
    1+w j ≤ weighted w C D x := by
  classical
  have hjc := count_ge_first (C j) D x
  simp only [if_pos hj] at hjc
  have hs := Finset.single_le_sum (fun i (_ : i ∈ (Finset.univ : Finset I)) =>
    mul_nonneg (hw i) (sub_nonneg.mpr (count_ge_one (C i) D x)))
    (Finset.mem_univ j)
  simp only [mul_sub, mul_one, Finset.sum_sub_distrib, hm] at hs
  have hh := mul_le_mul_of_nonneg_left (by linarith : 1 ≤ count (C j) D x-1) (hw j)
  dsimp only [weighted]
  nlinarith

/-- These are the geometric lower bounds used by a present-current pair
model. No conclusion about the value of its backward budget is drawn. -/
theorem arithmetic_weighted_lower {I : Type*} [Fintype I]
    (w : I → ℝ) (hw : ∀ i, 0 ≤ w i) (hm : (∑ i, w i)=1)
    (D : ℕ) (a : ℕ → ℤ) (c : I → ℕ → ℤ)
    (x y : ZMod (3^(D+1))) (hx : x ∈ branchGood 3 (D+1) a 1)
    (hy : y ∈ branchGood 3 (D+1) a 2) (hc : ∀ i, ¬ (3 : ℤ) ∣ c i 1)
    (j : I) :
    let C := fun i e => cylinder 3 (D+1) e (c i e)
    1 ≤ weighted w C D x ∧ 1 ≤ weighted w C D y ∧
      3 ≤ weighted w C D x+weighted w C D y ∧
      1+w j ≤ max (weighted w C D x) (weighted w C D y) := by
  refine ⟨weighted_ge_one w hw hm _ D x, weighted_ge_one w hw hm _ D y,
    weighted_sum_lower w hw hm _ D x y
      (fun i => arithmetic_count_sum_lower D a (c i) x y hx hy (hc i)), ?_⟩
  have hp := first_pair_exact (D+1) a (c j 1) x y hx hy (hc j)
  by_cases hxC : x ∈ cylinder 3 (D+1) 1 (c j 1)
  · exact (weighted_ge_one_add_weight w hw hm _ D x j hxC).trans (le_max_left _ _)
  · have hyC : y ∈ cylinder 3 (D+1) 1 (c j 1) := by
      by_contra hn
      simp [hxC,hn] at hp
    exact (weighted_ge_one_add_weight w hw hm _ D y j hyC).trans (le_max_right _ _)

lemma leading_quinary_bound {I : Type*} [Fintype I]
    (w : I → ℝ) (hw : ∀ i, 0 ≤ w i) (hm : (∑ i, w i)=1)
    (D : ℕ) (a : ℕ → ℤ) (c : I → ℕ → ℤ)
    (x y : ZMod (3^(D+1))) (hx : x ∈ branchGood 3 (D+1) a 1)
    (hy : y ∈ branchGood 3 (D+1) a 2) (hc : ∀ i, ¬ (3 : ℤ) ∣ c i 1)
    (j : I) (hj : 4/5 ≤ w j) :
    9/5 ≤ max
      (weighted w (fun i e => cylinder 3 (D+1) e (c i e)) D x)
      (weighted w (fun i e => cylinder 3 (D+1) e (c i e)) D y) := by
  have h := (arithmetic_weighted_lower w hw hm D a c x y hx hy hc j).2.2.2
  linarith

/-- The finite geometric current weights may have total below one. Padding
with one more genuine present cylinder family preserves the lower bounds;
the distinguished family's weight is unchanged. -/
theorem padded_weighted_lower {I : Type*} [Fintype I]
    (w : I → ℝ) (hw : ∀ i, 0 ≤ w i) (hm : (∑ i, w i) ≤ 1)
    (D : ℕ) (a : ℕ → ℤ) (c : Option I → ℕ → ℤ)
    (x y : ZMod (3^(D+1))) (hx : x ∈ branchGood 3 (D+1) a 1)
    (hy : y ∈ branchGood 3 (D+1) a 2) (hc : ∀ i, ¬ (3 : ℤ) ∣ c i 1)
    (j : I) (hj : 4/5 ≤ w j) :
    let w' := Erdos7TernaryTwoCurrentPadding.paddedWeight w
    let C := fun i e => cylinder 3 (D+1) e (c i e)
    1 ≤ weighted w' C D x ∧ 1 ≤ weighted w' C D y ∧
      3 ≤ weighted w' C D x+weighted w' C D y ∧
      9/5 ≤ max (weighted w' C D x) (weighted w' C D y) := by
  have hw' := Erdos7TernaryTwoCurrentPadding.paddedWeight_nonneg w hw hm
  have hm' := Erdos7TernaryTwoCurrentPadding.paddedWeight_mass w
  have h := arithmetic_weighted_lower
    (Erdos7TernaryTwoCurrentPadding.paddedWeight w) hw' hm' D a c x y hx hy hc (some j)
  refine ⟨h.1,h.2.1,h.2.2.1,?_⟩
  have hh := h.2.2.2
  change 1+w j ≤ _ at hh
  linarith

#print axioms arithmetic_pair_average_lower
#print axioms arithmetic_weighted_lower
#print axioms leading_quinary_bound
#print axioms padded_weighted_lower
end Erdos7PairedPresentGeometry
