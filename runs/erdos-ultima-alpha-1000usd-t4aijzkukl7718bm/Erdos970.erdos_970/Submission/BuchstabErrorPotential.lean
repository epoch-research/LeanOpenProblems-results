import Submission.BuchstabSharpSource

/-! Exact fixed-obstacle and positive-kernel forms of the finite-prime error
recurrence. The guards and all root/child units are retained. No analytic
bound is substituted for the finite kernel. -/
namespace Erdos970.RecursiveSieve.Buchstab
open Finset
set_option maxHeartbeats 1500000

noncomputable def finiteErrorSource (q : ℕ → ℝ) (keep : ℕ → ℝ → Prop)
    (k : ℕ) (D : ℝ) : ℝ := by
  classical
  exact 1+∑ i : Fin k, if keep i.val (D*q i.val) then (1 : ℝ) else 0

noncomputable def finiteErrorKernel (q : ℕ → ℝ) (keep : ℕ → ℝ → Prop)
    (F : ℕ → ℝ → ℝ) (k : ℕ) (D : ℝ) : ℝ := by
  classical
  exact ∑ i : Fin k, if keep i.val (D*q i.val) then
    ∑ j : Fin i.val, F j.val ((D*q i.val)*q j.val) else 0

lemma finiteErrorSource_nonneg (q : ℕ → ℝ) (keep : ℕ → ℝ → Prop) (k : ℕ) (D : ℝ) :
    0 ≤ finiteErrorSource q keep k D := by
  classical
  unfold finiteErrorSource
  positivity

lemma finiteErrorKernel_mono (q : ℕ → ℝ) (keep : ℕ → ℝ → Prop)
    (F G : ℕ → ℝ → ℝ) (hFG : ∀ k D, F k D ≤ G k D) (k : ℕ) (D : ℝ) :
    finiteErrorKernel q keep F k D ≤ finiteErrorKernel q keep G k D := by
  classical
  unfold finiteErrorKernel
  apply sum_le_sum
  intro i hi
  split_ifs
  · exact sum_le_sum (fun j hj => hFG _ _)
  · rfl

lemma finiteErrorKernel_nonneg (q : ℕ → ℝ) (keep : ℕ → ℝ → Prop)
    (F : ℕ → ℝ → ℝ) (hF : ∀ k D, 0 ≤ F k D) (k : ℕ) (D : ℝ) :
    0 ≤ finiteErrorKernel q keep F k D := by
  classical
  unfold finiteErrorKernel
  exact sum_nonneg (fun i _ => by
    split_ifs
    · exact sum_nonneg (fun j _ => hF _ _)
    · rfl)

/-- Every lower-child unit is in the source, and every retained grandchild is
in the linear kernel. The cutoff predicates are identical to the originals. -/
theorem double_error_eq_source_add_kernel (q : ℕ → ℝ) (keep : ℕ → ℝ → Prop)
    (F : ℕ → ℝ → ℝ) (k : ℕ) (D : ℝ) :
    1+(∑ i : Fin k, lowerErrorStep q keep F i.val (D*q i.val)) =
      finiteErrorSource q keep k D+finiteErrorKernel q keep F k D := by
  classical
  unfold finiteErrorSource finiteErrorKernel
  rw [add_assoc, ← sum_add_distrib]
  congr 1
  apply sum_congr rfl
  intro i hi
  unfold lowerErrorStep
  split_ifs <;> simp

lemma upperError_le_succ (q : ℕ → ℝ) (keep : ℕ → ℝ → Prop)
    (base : ℕ → ℝ → ℝ) (n k : ℕ) (D : ℝ) :
    upperError q keep base n k D ≤ upperError q keep base (n+1) k D :=
  le_max_left _ _

/-- The original outer maximum is exactly equivalent to a fixed initial
obstacle, not to adding the whole previous error at every depth. -/
theorem upperError_fixed_obstacle (q : ℕ → ℝ) (keep : ℕ → ℝ → Prop)
    (base : ℕ → ℝ → ℝ) (n k : ℕ) (D : ℝ) :
    upperError q keep base (n+1) k D = max (base k D)
      (finiteErrorSource q keep k D+finiteErrorKernel q keep (upperError q keep base n) k D) := by
  induction n with
  | zero => exact congrArg (max (base k D)) (double_error_eq_source_add_kernel q keep base k D)
  | succ n ih =>
    have hm := finiteErrorKernel_mono q keep _ _ (upperError_le_succ q keep base n) k D
    change max (upperError q keep base (n+1) k D)
      (1+∑ i : Fin k, lowerErrorStep q keep (upperError q keep base (n+1)) i.val (D*q i.val)) = _
    rw [double_error_eq_source_add_kernel, ih, max_assoc,
      max_eq_right (add_le_add le_rfl hm)]

noncomputable def finiteErrorKernelPower (q : ℕ → ℝ) (keep : ℕ → ℝ → Prop)
    (F : ℕ → ℝ → ℝ) : ℕ → ℕ → ℝ → ℝ
  | 0 => F
  | n+1 => finiteErrorKernel q keep (finiteErrorKernelPower q keep F n)

lemma finiteErrorKernelPower_nonneg (q : ℕ → ℝ) (keep : ℕ → ℝ → Prop)
    (F : ℕ → ℝ → ℝ) (hF : ∀ k D, 0 ≤ F k D) (n k : ℕ) (D : ℝ) :
    0 ≤ finiteErrorKernelPower q keep F n k D := by
  induction n generalizing k D with
  | zero => exact hF k D
  | succ n ih => exact finiteErrorKernel_nonneg q keep _ ih k D

/-- Two strict index descents occur in each kernel application. The finite
kernel is therefore nilpotent at each fixed root index, for arbitrary guards. -/
theorem finiteErrorKernelPower_eq_zero (q : ℕ → ℝ) (keep : ℕ → ℝ → Prop)
    (F : ℕ → ℝ → ℝ) (n k : ℕ) (D : ℝ) (hk : k < 2*n) :
    finiteErrorKernelPower q keep F n k D = 0 := by
  induction n generalizing k D with
  | zero => omega
  | succ n ih =>
    classical
    unfold finiteErrorKernelPower finiteErrorKernel
    apply sum_eq_zero
    intro i hi
    split_ifs
    · apply sum_eq_zero
      intro j hj
      exact ih j.val _ (by have := i.isLt; have := j.isLt; omega)
    · rfl

lemma finiteErrorKernel_sum (q : ℕ → ℝ) (keep : ℕ → ℝ → Prop)
    {α : Type*} (T : Finset α) (F : α → ℕ → ℝ → ℝ) (k : ℕ) (D : ℝ) :
    finiteErrorKernel q keep (fun j E => ∑ a ∈ T, F a j E) k D =
      ∑ a ∈ T, finiteErrorKernel q keep (F a) k D := by
  classical
  unfold finiteErrorKernel
  rw [sum_comm]
  apply sum_congr rfl
  intro i hi
  by_cases hk : keep i.val (D*q i.val)
  · simp only [if_pos hk]
    rw [sum_comm]
  · simp only [if_neg hk,sum_const_zero]

/-- The actual complete finite error is bounded by its positive finite
potential. This identity-based reduction makes no continuous approximation. -/
theorem upperError_le_finite_potential (q : ℕ → ℝ) (keep : ℕ → ℝ → Prop)
    (base : ℕ → ℝ → ℝ) (hbase : ∀ k D, 0 ≤ base k D) (n k : ℕ) (D : ℝ) :
    upperError q keep base n k D ≤ ∑ r ∈ range (n+1),
      finiteErrorKernelPower q keep (fun j E => base j E+finiteErrorSource q keep j E) r k D := by
  let F : ℕ → ℝ → ℝ := fun j E => base j E+finiteErrorSource q keep j E
  have hF : ∀ j E, 0 ≤ F j E := fun j E => add_nonneg (hbase j E) (finiteErrorSource_nonneg q keep j E)
  change upperError q keep base n k D ≤ ∑ r ∈ range (n+1), finiteErrorKernelPower q keep F r k D
  induction n generalizing k D with
  | zero =>
    simp only [Nat.zero_add,sum_range_one,finiteErrorKernelPower,F]
    exact le_add_of_nonneg_right (finiteErrorSource_nonneg q keep k D)
  | succ n ih =>
    rw [upperError_fixed_obstacle]
    have hk := finiteErrorKernel_mono q keep _ _ ih k D
    rw [finiteErrorKernel_sum] at hk
    have hnext : finiteErrorSource q keep k D+
        finiteErrorKernel q keep (upperError q keep base n) k D ≤
          finiteErrorSource q keep k D+
            ∑ r ∈ range (n+1), finiteErrorKernelPower q keep F (r+1) k D :=
      add_le_add le_rfl hk
    have hright : (∑ r ∈ range (n+1+1), finiteErrorKernelPower q keep F r k D) =
        base k D+(finiteErrorSource q keep k D+
          ∑ r ∈ range (n+1), finiteErrorKernelPower q keep F (r+1) k D) := by
      rw [sum_range_succ']
      simp only [finiteErrorKernelPower,F]
      ring
    rw [hright]
    apply max_le
    · exact le_add_of_nonneg_right (add_nonneg (finiteErrorSource_nonneg q keep k D)
        (sum_nonneg (fun r _ => finiteErrorKernelPower_nonneg q keep F hF (r+1) k D)))
    · exact hnext.trans (le_add_of_nonneg_left (hbase k D))

/-- A depth-independent finite potential: all terms beyond half the root
index vanish by strict descent. The remaining finite sum is not bounded
by a continuous integral here. -/
theorem upperError_le_truncated_finite_potential (q : ℕ → ℝ) (keep : ℕ → ℝ → Prop)
    (base : ℕ → ℝ → ℝ) (hbase : ∀ k D, 0 ≤ base k D) (n k : ℕ) (D : ℝ) :
    upperError q keep base n k D ≤ ∑ r ∈ range (k/2+1),
      finiteErrorKernelPower q keep (fun j E => base j E+finiteErrorSource q keep j E) r k D := by
  let F : ℕ → ℝ → ℝ := fun j E => base j E+finiteErrorSource q keep j E
  have hF : ∀ j E, 0 ≤ F j E := fun j E => add_nonneg (hbase j E) (finiteErrorSource_nonneg q keep j E)
  apply (upperError_le_finite_potential q keep base hbase n k D).trans
  change (∑ r ∈ range (n+1), finiteErrorKernelPower q keep F r k D) ≤
    ∑ r ∈ range (k/2+1), finiteErrorKernelPower q keep F r k D
  by_cases hn : n+1 ≤ k/2+1
  · exact sum_le_sum_of_subset_of_nonneg (range_mono hn)
      (fun r _ _ => finiteErrorKernelPower_nonneg q keep F hF r k D)
  · have he : (∑ r ∈ range (k/2+1), finiteErrorKernelPower q keep F r k D) =
        ∑ r ∈ range (n+1), finiteErrorKernelPower q keep F r k D := by
      apply sum_subset (range_mono (by omega : k/2+1 ≤ n+1))
      intro r hr hrsmall
      have hrs : k/2+1 ≤ r := by simpa only [mem_range,not_lt] using hrsmall
      exact finiteErrorKernelPower_eq_zero q keep F r k D (by omega)
    exact he.ge

/-- The actual recurrence, not only its potential majorant, stabilizes after
at most floor(k/2)+1 refinements at a fixed root index k. -/
theorem upperError_stable_after_half_index (q : ℕ → ℝ) (keep : ℕ → ℝ → Prop)
    (base : ℕ → ℝ → ℝ) (k n : ℕ) (hn : k/2+1 ≤ n) (D : ℝ) :
    upperError q keep base (n+1) k D = upperError q keep base n k D := by
  induction k using Nat.strong_induction_on generalizing n D with
  | h k ih =>
    cases n with
    | zero => omega
    | succ n =>
      classical
      conv_lhs => rw [upperError_fixed_obstacle]
      conv_rhs => rw [upperError_fixed_obstacle]
      apply congrArg (max (base k D))
      apply congrArg (fun z => finiteErrorSource q keep k D+z)
      unfold finiteErrorKernel
      apply sum_congr rfl
      intro i hi
      split_ifs
      · apply sum_congr rfl
        intro j hj
        exact ih j.val (lt_trans j.isLt i.isLt) n
          (by have := i.isLt; have := j.isLt; omega) _
      · rfl

#print axioms double_error_eq_source_add_kernel
#print axioms upperError_fixed_obstacle
#print axioms finiteErrorKernelPower_eq_zero
#print axioms upperError_le_finite_potential
#print axioms upperError_le_truncated_finite_potential
#print axioms upperError_stable_after_half_index
end Erdos970.RecursiveSieve.Buchstab
