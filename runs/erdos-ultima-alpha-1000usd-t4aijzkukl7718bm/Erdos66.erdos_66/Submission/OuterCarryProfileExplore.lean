import Submission.IntegerBlockExplore

/-! Repetition in an outer cyclic block controls the two carry fibers
separately, uniformly for every pair in a family of low templates. -/
namespace Erdos66OuterCarryProfile
open Erdos66IntegerBlock Erdos66CyclicThickening
open scoped Classical

variable (M : ℕ) [NeZero M]

noncomputable def cyclicCount (C D : Finset (ZMod M)) (z : ZMod M) : ℕ :=
  (C.filter (fun a ↦ z-a∈D)).card

lemma cyclicCount_sum (C D : Finset (ZMod M)) (z : ZMod M) :
    cyclicCount M C D z = ∑ a : ZMod M, if a∈C ∧ z-a∈D then 1 else 0 := by
  simp only [cyclicCount,Finset.card_filter,ite_and,Finset.sum_ite_mem,Finset.univ_inter]

lemma sum_zmod_range (f : ZMod M → ℕ) :
    (∑ a : ZMod M, f a) = ∑ x ∈ Finset.range M, f (x : ZMod M) := by
  have he : (Finset.range M).image (fun x : ℕ ↦ (x : ZMod M)) = Finset.univ := by
    ext a
    simp only [Finset.mem_image,Finset.mem_range,Finset.mem_univ,iff_true]
    exact ⟨a.val,ZMod.val_lt a,ZMod.natCast_zmod_val a⟩
  rw [← he,Finset.sum_image]
  intro x hx y hy hxy
  have hv := congrArg ZMod.val hxy
  simpa only [ZMod.val_natCast_of_lt (Finset.mem_range.mp hx),
    ZMod.val_natCast_of_lt (Finset.mem_range.mp hy)] using hv

lemma lower_zmod (C D : Finset (ZMod M)) (n : ℕ) :
    lower M C D n = ∑ a : ZMod M,
      if a.val ≤ n ∧ a∈C ∧ (n : ZMod M)-a∈D then 1 else 0 := by
  rw [sum_zmod_range]
  unfold lower
  apply Finset.sum_congr rfl
  intro x hx
  rw [ZMod.val_natCast_of_lt (Finset.mem_range.mp hx)]

variable (K : ℕ) [NeZero K]

noncomputable def outerLift (C : Finset (ZMod M)) : Finset (ZMod (M*K)) :=
  Finset.univ.filter (fun z ↦ reduceDigit M K z∈C)

lemma mem_outerLift (C : Finset (ZMod M)) (z : ZMod (M*K)) :
    z∈outerLift M K C ↔ reduceDigit M K z∈C := by simp [outerLift]

lemma outer_cyclicCount (C D : Finset (ZMod M)) (z : ZMod (M*K)) :
    cyclicCount (M*K) (outerLift M K C) (outerLift M K D) z =
      K*cyclicCount M C D (reduceDigit M K z) := by
  rw [cyclicCount_sum,cyclicCount_sum]
  simp only [mem_outerLift,map_sub]
  rw [← Equiv.sum_comp (blockEquiv M K),Fintype.sum_prod_type]
  simp only [blockEquiv,Equiv.ofBijective_apply,reduce_block,Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,smul_eq_mul,← Finset.mul_sum]

lemma blockDigit_le_iff (t a : ZMod M) (q i : Fin K) :
    (blockDigit M K a i).val ≤ (blockDigit M K t q).val ↔
      i.val < lowCutoff M K q t a := by
  have hh := borrow_block M K t a q i
  simp only [borrow] at hh
  split_ifs at hh <;> omega

/-- Exact lower carry count; all but the final small block contribute the
entire mixed cyclic count. -/
lemma outer_lower_formula (C D : Finset (ZMod M)) (t : ZMod M) (q : Fin K) :
    lower (M*K) (outerLift M K C) (outerLift M K D) (blockDigit M K t q).val =
      q.val*cyclicCount M C D t+lower M C D t.val := by
  rw [lower_zmod]
  simp only [ZMod.natCast_zmod_val,mem_outerLift,map_sub,reduce_block]
  rw [← Equiv.sum_comp (blockEquiv M K),Fintype.sum_prod_type]
  simp only [blockEquiv,Equiv.ofBijective_apply,reduce_block,blockDigit_le_iff]
  have hinner (a : ZMod M) :
      (∑ i : Fin K, if i.val < lowCutoff M K q t a ∧ a∈C ∧ t-a∈D then 1 else 0) =
        lowCutoff M K q t a*(if a∈C ∧ t-a∈D then 1 else 0) := by
    by_cases ha : a∈C ∧ t-a∈D
    · simp only [ha,and_true,if_true,mul_one]
      rw [← Finset.card_filter]
      exact card_fin_below K _ (lowCutoff_le M K q t a)
    · simp [ha]
  simp_rw [hinner]
  unfold lowCutoff
  simp only [add_mul,Finset.sum_add_distrib,← Finset.mul_sum]
  rw [← cyclicCount_sum,lower_zmod]
  simp only [ZMod.natCast_zmod_val]
  congr 1
  apply Finset.sum_congr rfl
  intro a ha
  split_ifs <;> simp_all

/-- Exact upper carry count. -/
lemma outer_upper_formula (C D : Finset (ZMod M)) (t : ZMod M) (q : Fin K) :
    upper (M*K) (outerLift M K C) (outerLift M K D) (blockDigit M K t q).val =
      (K-q.val-1)*cyclicCount M C D t+upper M C D t.val := by
  have hsum := lower_add_upper (M*K) (outerLift M K C) (outerLift M K D)
    (blockDigit M K t q).val
  change _ = cyclicCount (M*K) (outerLift M K C) (outerLift M K D)
    ((blockDigit M K t q).val : ZMod (M*K)) at hsum
  rw [ZMod.natCast_zmod_val,outer_cyclicCount,reduce_block,outer_lower_formula] at hsum
  have hsmall := lower_add_upper M C D t.val
  change _ = cyclicCount M C D (t.val : ZMod M) at hsmall
  rw [ZMod.natCast_zmod_val] at hsmall
  have hK : K=q.val+(K-q.val-1)+1 := by have := q.isLt; omega
  have hm := congrArg (fun k ↦ k*cyclicCount M C D t) hK
  nlinarith

/-- Individual lower and upper fibers admit a common profile even when C and
D are different templates. The error has only one extra small-block term. -/
theorem outer_carry_error (C D : Finset (ZMod M)) (t : ZMod M) (q : Fin K)
    (μ E : ℝ) (hμ : 0 ≤ μ) (hE : 0 ≤ E)
    (hcount : |(cyclicCount M C D t : ℝ)-μ| ≤ E) :
    |(lower (M*K) (outerLift M K C) (outerLift M K D) (blockDigit M K t q).val : ℝ)-q.val*μ| ≤
      K*E+μ+E ∧
    |(upper (M*K) (outerLift M K C) (outerLift M K D) (blockDigit M K t q).val : ℝ)-
      ((K : ℝ)-q.val)*μ| ≤ K*E+μ+E := by
  have hs := lower_add_upper M C D t.val
  change _ = cyclicCount M C D (t.val : ZMod M) at hs
  rw [ZMod.natCast_zmod_val] at hs
  have hs' : (lower M C D t.val : ℝ)+upper M C D t.val=cyclicCount M C D t := by exact_mod_cast hs
  have hcountup := (abs_le.mp hcount).2
  have hl0 : (0 : ℝ) ≤ lower M C D t.val := Nat.cast_nonneg _
  have hu0 : (0 : ℝ) ≤ upper M C D t.val := Nat.cast_nonneg _
  have hlup : (lower M C D t.val : ℝ) ≤ μ+E := by linarith
  have huup : (upper M C D t.val : ℝ) ≤ μ+E := by linarith
  have hq0 : (0 : ℝ) ≤ q.val := Nat.cast_nonneg _
  have hqK : (q.val : ℝ) ≤ K := by exact_mod_cast q.isLt.le
  constructor
  · rw [outer_lower_formula]
    push_cast
    have he : (q.val : ℝ)*cyclicCount M C D t+lower M C D t.val-q.val*μ =
        q.val*((cyclicCount M C D t : ℝ)-μ)+lower M C D t.val := by ring
    rw [he]
    calc
      _ ≤ |(q.val : ℝ)*((cyclicCount M C D t : ℝ)-μ)|+|((lower M C D t.val : ℝ))| := abs_add_le _ _
      _ = q.val*|((cyclicCount M C D t : ℝ)-μ)|+lower M C D t.val := by
        rw [abs_mul,abs_of_nonneg hq0,abs_of_nonneg hl0]
      _ ≤ q.val*E+(μ+E) := add_le_add (mul_le_mul_of_nonneg_left hcount hq0) hlup
      _ ≤ K*E+μ+E := by nlinarith [mul_le_mul_of_nonneg_right hqK hE]
  · rw [outer_upper_formula]
    have hr : ((K-q.val-1 : ℕ) : ℝ)=(K : ℝ)-q.val-1 := by
      rw [Nat.cast_sub (by have := q.isLt; omega),Nat.cast_sub q.isLt.le,Nat.cast_one]
    push_cast
    rw [hr]
    have he : ((K : ℝ)-q.val-1)*cyclicCount M C D t+upper M C D t.val-((K : ℝ)-q.val)*μ =
        ((K : ℝ)-q.val-1)*((cyclicCount M C D t : ℝ)-μ)+(upper M C D t.val-μ) := by ring
    rw [he]
    have hr0 : (0 : ℝ) ≤ (K : ℝ)-q.val-1 := by
      have hh : (q.val : ℝ)+1 ≤ K := by exact_mod_cast (show q.val+1 ≤ K from q.isLt)
      linarith
    have huabs : |(upper M C D t.val : ℝ)-μ| ≤ μ+E := by rw [abs_le]; constructor <;> linarith
    calc
      _ ≤ |((K : ℝ)-q.val-1)*((cyclicCount M C D t : ℝ)-μ)|+|(upper M C D t.val : ℝ)-μ| := abs_add_le _ _
      _ = ((K : ℝ)-q.val-1)*|((cyclicCount M C D t : ℝ)-μ)|+|(upper M C D t.val : ℝ)-μ| := by
        rw [abs_mul,abs_of_nonneg hr0]
      _ ≤ ((K : ℝ)-q.val-1)*E+(μ+E) := add_le_add (mul_le_mul_of_nonneg_left hcount hr0) huabs
      _ ≤ K*E+μ+E := by nlinarith

end Erdos66OuterCarryProfile
