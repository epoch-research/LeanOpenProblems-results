import Submission.WitnessResidueProjectionExplore

/-! Modulus-independent fractional residue bounds. Exact discrepancy of a
residue class is at most one; combining the resulting L-infinity error
bound with a nonnegative L1 bound removes the number-of-residues loss. -/
namespace Erdos66UniformResidueProfile
open Erdos66ResidueProfileProjection Erdos66NaturalResidueProjection
  Erdos66WitnessResidueProjection Erdos66ResidueSeries Erdos66Generating
  Erdos66Fractional Erdos66FractionalFourthPower Erdos66Rounding
  Erdos66WeightedSquareStability
open AdditiveCombinatorics
open scoped Classical
set_option maxHeartbeats 2400000
variable (m : ℕ) [NeZero m]

lemma residueWeight_prefix_one (i : ZMod m) (N : ℕ) :
    |∑ n∈Finset.range N, residueWeight m i n| ≤ 1 := by
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
  have hres : (∑ n∈Finset.range (N%m), (if (n : ZMod m)=i then (1 : ℝ) else 0))=
      if i.val<N%m then 1 else 0 := by
    calc
      _ = ∑ n∈Finset.range (N%m), if n=i.val then (1 : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro n hn
        have hn' : n< m := (Finset.mem_range.mp hn).trans (Nat.mod_lt N (NeZero.pos m))
        have he' : (n : ZMod m)=i ↔ n=i.val := by
          constructor
          · intro h
            simpa only [ZMod.val_natCast,Nat.mod_eq_of_lt hn'] using congrArg ZMod.val h
          · intro h
            rw [h,ZMod.natCast_zmod_val]
        simp only [he']
      _ = _ := by simp
  simp only [residueWeight,Finset.sum_sub_distrib,hres,Finset.sum_const,
    Finset.card_range,nsmul_eq_mul,mul_one_div]
  have hm : (0 : ℝ)< m := by exact_mod_cast NeZero.pos m
  have hrem : ((N%m : ℕ) : ℝ)< m := by exact_mod_cast Nat.mod_lt N (NeZero.pos m)
  have hq0 : 0≤((N%m : ℕ) : ℝ)/m := by positivity
  have hq1 : ((N%m : ℕ) : ℝ)/m≤1 := (div_le_one hm).mpr hrem.le
  split_ifs <;> rw [abs_le] <;> constructor <;> linarith

lemma centeredProfile_prefix_one (i : ZMod m) (n : ℕ) :
    |prefixSum (centeredProfile m i) n| ≤ 1 := by
  simpa only [prefixSum,centeredProfile_eq,profile_zero,mul_one] using
    antitone_weighted_prefix_bound (residueWeight m i) profile 1 (by norm_num)
      profile_nonneg profile_antitone (residueWeight_prefix_one m i) (n+1)

/-- The same constant works for every positive modulus and every target. -/
theorem projectionError_profile_two (i : ZMod m) (n : ℕ) :
    |projectionError m profile i n| ≤ 2 := by
  rw [projectionError_profile_eq]
  simpa only [mul_one] using mixed_convolution_bound _ 1 (by norm_num)
    (centeredProfile_prefix_one m i) n

lemma sum_convolution_residues (f : ℕ → ℝ) (n : ℕ) :
    (∑ i : ZMod m, sumConv f (residueTerm m f i) n)=sumConv f f n := by
  unfold sumConv
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ij hij
  rw [←Finset.mul_sum]
  simp [residueTerm,eq_comm]

lemma convolution_nonneg {f g : ℕ → ℝ} (hf : ∀ n, 0≤f n) (hg : ∀ n, 0≤g n) (n : ℕ) :
    0 ≤ sumConv f g n := Finset.sum_nonneg (fun ij _ ↦ mul_nonneg (hf ij.1) (hg ij.2))

/-- Positivity controls the joint L1 error without a factor for the number
of residue classes. -/
lemma projectionError_l1_bound {f : ℕ → ℝ} (hf : ∀ n, 0≤f n) (n : ℕ) :
    (∑ i : ZMod m, |projectionError m f i n|) ≤ 2*sumConv f f n := by
  have hm : (0 : ℝ)< m := by exact_mod_cast NeZero.pos m
  have hC : 0 ≤ sumConv f f n := convolution_nonneg hf hf n
  have hmean : 0 ≤ sumConv f f n/m := div_nonneg hC hm.le
  calc
    _ ≤ ∑ i : ZMod m, (sumConv f (residueTerm m f i) n+sumConv f f n/m) := by
      apply Finset.sum_le_sum
      intro i hi
      have hp : ∀ k, 0 ≤ residueTerm m f i k := by
        intro k
        unfold residueTerm
        split_ifs
        · exact hf k
        · exact le_rfl
      have hh := abs_sub (sumConv f (residueTerm m f i) n) (sumConv f f n/m)
      simpa only [projectionError,abs_of_nonneg (convolution_nonneg hf hp n),abs_of_nonneg hmean] using hh
    _ = _ := by
      rw [Finset.sum_add_distrib,sum_convolution_residues]
      simp only [Finset.sum_const,Finset.card_univ,ZMod.card,nsmul_eq_mul]
      field_simp
      ring

/-- L-infinity times L1 gives a joint square bound uniform in m. -/
theorem projectionError_profile_square_sum (n : ℕ) :
    (∑ i : ZMod m, projectionError m profile i n^2) ≤ 4*(harmonic (n+1) : ℝ) := by
  have hsq (i : ZMod m) : projectionError m profile i n^2 ≤ 2*|projectionError m profile i n| := by
    have hh := mul_le_mul_of_nonneg_right (projectionError_profile_two m i n) (abs_nonneg (projectionError m profile i n))
    simpa only [←pow_two,sq_abs] using hh
  calc
    _ ≤ ∑ i : ZMod m, 2*|projectionError m profile i n| := Finset.sum_le_sum (fun i _ ↦ hsq i)
    _ = 2*(∑ i : ZMod m, |projectionError m profile i n|) := (Finset.mul_sum _ _ _).symm
    _ ≤ 2*(2*sumConv profile profile n) := mul_le_mul_of_nonneg_left (projectionError_l1_bound m profile_nonneg n) (by norm_num)
    _ = _ := by rw [profile_convolution]; ring

lemma scaled_projection_square_sum {c : ℝ} (hc : 0≤c) (n : ℕ) :
    (∑ i : ZMod m, projectionError m (fun k ↦ Real.sqrt c*profile k) i n^2) ≤
      4*c^2*(harmonic (n+1) : ℝ) := by
  simp only [projectionError_scale,Real.sq_sqrt hc,mul_pow,←Finset.mul_sum]
  have hh := mul_le_mul_of_nonneg_left (projectionError_profile_square_sum m n) (sq_nonneg c)
  nlinarith

lemma summable_harmonic_shift {r : ℝ} (hr0 : 0≤r) (hr1 : r<1) :
    Summable (fun n ↦ (harmonic (n+1) : ℝ)*r^n) := by
  have hp : Summable (fun n ↦ profile n*r^n) := by
    simpa only [pow_one] using summable_profile_power_weighted hr0 hr1 1
  have hh := summable_conv hp hp
  change Summable (fun n ↦ sumConv (fun k ↦ profile k*r^k) (fun k ↦ profile k*r^k) n) at hh
  simpa only [weighted_convolution,profile_convolution] using hh

/-- No modulus appears in the fractional aggregate-energy bound. -/
theorem fractional_residueEnergy_uniform {c r : ℝ} (hc : 0≤c) (hr0 : 0≤r) (hr1 : r<1) :
    residueEnergy m (fun n ↦ Real.sqrt c*profile n) r ≤
      4*c^2*series (fun n ↦ (harmonic (n+1) : ℝ)) r := by
  have hs := summable_harmonic_shift hr0 hr1
  have he : residueEnergy m (fun n ↦ Real.sqrt c*profile n) r=
      ∑' n, (∑ i : ZMod m, projectionError m (fun k ↦ Real.sqrt c*profile k) i n^2)*r^n := by
    simp only [residueEnergy,series,Finset.sum_mul]
    exact (Summable.tsum_finsetSum (fun i _ ↦ summable_profile_projection_sq m hc hr0 hr1 i)).symm
  rw [he]
  have hl : Summable (fun n ↦ (∑ i : ZMod m, projectionError m (fun k ↦ Real.sqrt c*profile k) i n^2)*r^n) := by
    simp only [Finset.sum_mul]
    exact summable_sum (fun i _ ↦ summable_profile_projection_sq m hc hr0 hr1 i)
  have hh := hl.tsum_le_tsum (fun n ↦ mul_le_mul_of_nonneg_right (scaled_projection_square_sum m hc n) (pow_nonneg hr0 n))
    (by convert hs.mul_left (4*c^2) using 1 <;> simp only [mul_assoc])
  simpa only [series,mul_assoc,tsum_mul_left] using hh

end Erdos66UniformResidueProfile
