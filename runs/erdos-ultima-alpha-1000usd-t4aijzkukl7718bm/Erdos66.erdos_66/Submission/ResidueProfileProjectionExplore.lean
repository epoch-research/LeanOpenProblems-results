import Submission.NaturalResidueProjectionExplore
import Submission.RoundingExplore

/-! The fractional harmonic profile has uniformly bounded residue-projection
errors. The bound depends on the fixed modulus, not on the target. -/
namespace Erdos66ResidueProfileProjection
open Erdos66NaturalResidueProjection Erdos66ResidueSeries Erdos66Rounding
  Erdos66Generating Erdos66Fractional
open scoped Classical
open AdditiveCombinatorics
set_option maxHeartbeats 2400000

lemma weighted_prefix_identity (w p : ℕ → ℝ) (N : ℕ) :
    (∑ j∈Finset.range N, w j*p j)=
      (∑ j∈Finset.range N, w j)*p N+
        ∑ j∈Finset.range N, (∑ k∈Finset.range (j+1), w k)*(p j-p (j+1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ,Finset.sum_range_succ,Finset.sum_range_succ,ih,
      Finset.sum_range_succ]
    ring

lemma sum_steps (p : ℕ → ℝ) (N : ℕ) :
    (∑ j∈Finset.range N, (p j-p (j+1)))=p 0-p N := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ,ih]; ring

lemma antitone_weighted_prefix_bound (w p : ℕ → ℝ) (D : ℝ) (hD : 0 ≤ D)
    (hp : ∀ n, 0 ≤ p n) (hm : Antitone p)
    (hw : ∀ N, |∑ j∈Finset.range N, w j| ≤ D) (N : ℕ) :
    |∑ j∈Finset.range N, w j*p j| ≤ D*p 0 := by
  rw [weighted_prefix_identity]
  calc
    _ ≤ |(∑ j∈Finset.range N, w j)*p N|+
        |∑ j∈Finset.range N, (∑ k∈Finset.range (j+1), w k)*(p j-p (j+1))| := abs_add_le _ _
    _ ≤ D*p N+∑ j∈Finset.range N, D*(p j-p (j+1)) := by
      apply add_le_add
      · rw [abs_mul,abs_of_nonneg (hp N)]
        exact mul_le_mul_of_nonneg_right (hw N) (hp N)
      · apply (Finset.abs_sum_le_sum_abs _ _).trans
        apply Finset.sum_le_sum
        intro j hj
        have hpj : 0 ≤ p j-p (j+1) := sub_nonneg.mpr (hm (Nat.le_succ j))
        rw [abs_mul,abs_of_nonneg hpj]
        exact mul_le_mul_of_nonneg_right (hw (j+1)) hpj
    _ = _ := by rw [← Finset.mul_sum,sum_steps]; ring

variable (m : ℕ) [NeZero m]

noncomputable def residueWeight (i : ZMod m) (n : ℕ) : ℝ :=
  (if (n : ZMod m)=i then 1 else 0)-1/m

lemma residueWeight_bound (i : ZMod m) (n : ℕ) : |residueWeight m i n| ≤ 1 := by
  have hm : (1 : ℝ) ≤ m := by exact_mod_cast NeZero.pos m
  have hp : 0 ≤ 1/(m : ℝ) := by positivity
  have hu : 1/(m : ℝ) ≤ 1 := (div_le_one (by linarith)).mpr hm
  unfold residueWeight
  split_ifs <;> rw [abs_le] <;> constructor <;> linarith

lemma residueWeight_period (i : ZMod m) (k n : ℕ) :
    residueWeight m i (k*m+n)=residueWeight m i n := by simp [residueWeight]

lemma residueWeight_block (i : ZMod m) : (∑ n∈Finset.range m, residueWeight m i n)=0 := by
  have hm : (m : ℝ)≠0 := by exact_mod_cast NeZero.ne m
  have hres : (∑ n∈Finset.range m, (if (n : ZMod m)=i then (1 : ℝ) else 0))=1 := by
    calc
      _ = ∑ n∈Finset.range m, if n=i.val then (1 : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro n hn
        have hn' := Finset.mem_range.mp hn
        have he : (n : ZMod m)=i ↔ n=i.val := by
          constructor
          · intro h
            simpa only [ZMod.val_natCast,Nat.mod_eq_of_lt hn'] using congrArg ZMod.val h
          · intro h
            rw [h,ZMod.natCast_zmod_val]
        simp only [he]
      _ = 1 := by simp [i.val_lt]
  simp only [residueWeight,Finset.sum_sub_distrib,hres,Finset.sum_const,
    Finset.card_range,nsmul_eq_mul]
  field_simp
  norm_num

lemma residueWeight_prefix (i : ZMod m) (N : ℕ) :
    |∑ n∈Finset.range N, residueWeight m i n| ≤ m := by
  have hfull (k : ℕ) : (∑ n∈Finset.range (k*m), residueWeight m i n)=0 := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Nat.succ_mul,Finset.sum_range_add,ih,zero_add]
      simpa only [residueWeight_period] using residueWeight_block m i
  have he : N=N/m*m+N%m := by
    simpa only [Nat.mul_comm,Nat.add_comm] using (Nat.mod_add_div N m).symm
  rw [he,Finset.sum_range_add,hfull,zero_add]
  simp only [residueWeight_period]
  calc
    _ ≤ ∑ n∈Finset.range (N%m), |residueWeight m i n| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _n∈Finset.range (N%m), (1 : ℝ) := Finset.sum_le_sum (fun n _ ↦ residueWeight_bound m i n)
    _ ≤ m := by simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,mul_one]; exact_mod_cast (Nat.mod_lt N (NeZero.pos m)).le

noncomputable def centeredProfile (i : ZMod m) (n : ℕ) : ℝ :=
  residueTerm m profile i n-profile n/m

lemma centeredProfile_eq (i : ZMod m) (n : ℕ) :
    centeredProfile m i n=residueWeight m i n*profile n := by
  unfold centeredProfile residueTerm residueWeight
  split_ifs <;> ring

lemma centeredProfile_prefix (i : ZMod m) (n : ℕ) : |prefixSum (centeredProfile m i) n| ≤ m := by
  simpa only [prefixSum,centeredProfile_eq,profile_zero,mul_one] using
    antitone_weighted_prefix_bound (residueWeight m i) profile m (Nat.cast_nonneg _)
      profile_nonneg profile_antitone (residueWeight_prefix m i) (n+1)

lemma projectionError_profile_eq (i : ZMod m) (n : ℕ) :
    projectionError m profile i n=sumConv (centeredProfile m i) profile n := by
  rw [projectionError,sumConv_comm_real profile (residueTerm m profile i)]
  simp only [sumConv,centeredProfile,sub_mul,div_mul_eq_mul_div,
    Finset.sum_sub_distrib,Finset.sum_div]

/-- Every residue of the fractional profile has bounded mixed-projection
error. There is no assumption about a Boolean set here. -/
theorem projectionError_profile_bound (i : ZMod m) (n : ℕ) :
    |projectionError m profile i n| ≤ 2*m := by
  rw [projectionError_profile_eq]
  exact mixed_convolution_bound _ m (Nat.cast_nonneg _) (centeredProfile_prefix m i) n

end Erdos66ResidueProfileProjection
