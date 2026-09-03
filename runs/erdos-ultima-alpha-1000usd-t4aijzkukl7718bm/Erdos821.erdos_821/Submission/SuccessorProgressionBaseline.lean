import Submission.SuccessorTypeIDivisibility
import Submission.PeriodicCofactorMean

/-!
# A principal-unit baseline for successor progressions

Periodic counting bounds the actual output-divisibility discrepancies of
residue-one progressions relative to their principal-unit baselines. These
are unconditional Type I inputs, not bounds for the remaining Type II Gram
correlations or a prime-output lower bound.
-/
open Nat Finset ArithmeticFunction
open scoped Classical BigOperators
namespace Erdos821.AnalyticSieve.SuccessorVaughan
set_option maxHeartbeats 3000000

noncomputable def residueOneOutput (m n : ℕ) : ℝ :=
  if (n : ZMod m)=1 then 1 else 0

noncomputable def principalUnitOutput (m n : ℕ) : ℝ :=
  if n.Coprime m then 1/(m.totient : ℝ) else 0

noncomputable def progressionPrefixCost (m : ℕ) : ℝ :=
  1+(3 : ℝ)^m.primeFactors.card/(m.totient : ℝ)

lemma progressionPrefixCost_nonneg (m : ℕ) : 0 ≤ progressionPrefixCost m := by
  unfold progressionPrefixCost
  positivity

lemma residueOneOutput_mul_eq_zero (m d s : ℕ) (hd : ¬d.Coprime m) :
    residueOneOutput m (d*s)=0 := by
  have he : ((d*s : ℕ) : ZMod m) ≠ 1 := by
    intro he
    have hu : IsUnit ((d*s : ℕ) : ZMod m) := by rw [he]; exact isUnit_one
    have hc := (ZMod.isUnit_iff_coprime (d*s) m).mp hu
    exact hd (Nat.coprime_mul_iff_left.mp hc).1
  simp only [residueOneOutput,if_neg he]

lemma principalUnitOutput_mul_eq_zero (m d s : ℕ) (hd : ¬d.Coprime m) :
    principalUnitOutput m (d*s)=0 := by
  simp only [principalUnitOutput,Nat.coprime_mul_iff_left,hd,false_and,if_false]

lemma principalUnitOutput_multiples (m d L : ℕ) (hd : d.Coprime m) :
    (∑ s ∈ Icc 1 L, principalUnitOutput m (d*s)) =
      (coprimeCofactorCount m 0 L : ℝ)/(m.totient : ℝ) := by
  have he (s : ℕ) : (d*s).Coprime m ↔ s.Coprime m :=
    ⟨fun h => (Nat.coprime_mul_iff_left.mp h).2,
      fun h => Nat.coprime_mul_iff_left.mpr ⟨hd,h⟩⟩
  simp_rw [principalUnitOutput,he]
  rw [← sum_filter,sum_const,nsmul_eq_mul]
  simp only [coprimeCofactorCount,zero_add]
  ring

lemma principalUnitOutput_multiples_error (m d L : ℕ) (hm : 0 < m)
    (hd : d.Coprime m) :
    |(∑ s ∈ Icc 1 L, principalUnitOutput m (d*s))-(L : ℝ)/m| ≤
      (3 : ℝ)^m.primeFactors.card/(m.totient : ℝ) := by
  have hφ : (0 : ℝ) < m.totient := by exact_mod_cast Nat.totient_pos.mpr hm
  rw [principalUnitOutput_multiples m d L hd]
  have he : (coprimeCofactorCount m 0 L : ℝ)/(m.totient : ℝ)-(L : ℝ)/m =
      ((coprimeCofactorCount m 0 L : ℝ)-(L : ℝ)*(m.totient : ℝ)/m)/(m.totient : ℝ) := by
    field_simp
  rw [he,abs_div,abs_of_pos hφ]
  apply div_le_div_of_nonneg_right _ hφ.le
  simpa only [Nat.sub_zero] using coprimeCofactorCount_density_error m 0 L hm

lemma residueOneOutput_multiples_error (m d L : ℕ) (hm : 0 < m)
    (hd : d.Coprime m) :
    |(∑ s ∈ Icc 1 L, residueOneOutput m (d*s))-(L : ℝ)/m| ≤ 1 := by
  letI : NeZero m := ⟨hm.ne'⟩
  simpa only [residueOneOutput,Nat.cast_mul,Units.val_one,one_mul,mul_one,mul_comm] using
    unit_cofactor_prefix_error m L d (1 : (ZMod m)ˣ) hd

/-- This is uniform in both the output prefix and the divisor modulus.
Nonunit divisor moduli contribute exactly zero to both weights. -/
theorem progression_divisible_prefix_error (m d T : ℕ) (hm : 0 < m) (hd : 0 < d) :
    |divisibleOutputPrefix (fun n => residueOneOutput m n-principalUnitOutput m n) d T| ≤
      progressionPrefixCost m := by
  rw [divisibleOutputPrefix_eq_multiples _ d T hd,sum_sub_distrib]
  by_cases hdm : d.Coprime m
  · have h₁ := residueOneOutput_multiples_error m d (T/d) hm hdm
    have h₂ := principalUnitOutput_multiples_error m d (T/d) hm hdm
    have he : (∑ s ∈ Icc 1 (T/d), residueOneOutput m (d*s))-
        (∑ s ∈ Icc 1 (T/d), principalUnitOutput m (d*s)) =
        ((∑ s ∈ Icc 1 (T/d), residueOneOutput m (d*s))-((T/d : ℕ) : ℝ)/m)-
        ((∑ s ∈ Icc 1 (T/d), principalUnitOutput m (d*s))-((T/d : ℕ) : ℝ)/m) := by ring
    rw [he]
    exact (abs_sub _ _).trans (_root_.add_le_add h₁ h₂)
  · simp only [residueOneOutput_mul_eq_zero m d _ hdm,
      principalUnitOutput_mul_eq_zero m d _ hdm,sum_const_zero,sub_self,abs_zero]
    exact progressionPrefixCost_nonneg m

lemma progression_outputMaxPrefix_le (m d N : ℕ) (hm : 0 < m) (hd : 0 < d) :
    outputMaxPrefix (fun n => residueOneOutput m n-principalUnitOutput m n) d N ≤
      progressionPrefixCost m :=
  progression_divisible_prefix_error m d _ hm hd

lemma residueOneOutput_bounds (m n : ℕ) :
    0 ≤ residueOneOutput m n ∧ residueOneOutput m n ≤ 1 := by
  unfold residueOneOutput
  split_ifs <;> norm_num

lemma principalUnitOutput_bounds (m n : ℕ) (hm : 0 < m) :
    0 ≤ principalUnitOutput m n ∧ principalUnitOutput m n ≤ 1 := by
  have hφ : (0 : ℝ) < m.totient := by exact_mod_cast Nat.totient_pos.mpr hm
  have hφ1 : (1 : ℝ) ≤ m.totient := by
    exact_mod_cast Nat.totient_pos.mpr hm
  unfold principalUnitOutput
  split_ifs
  · exact ⟨by positivity,(div_le_one hφ).mpr hφ1⟩
  · norm_num

lemma progression_pointwise_difference_le (m n : ℕ) (hm : 0 < m) :
    |residueOneOutput m n-principalUnitOutput m n| ≤ 1 := by
  have hw := residueOneOutput_bounds m n
  have hv := principalUnitOutput_bounds m n hm
  exact abs_le.mpr ⟨by linarith,by linarith⟩

noncomputable def removeOneWeight (W : ℕ → ℝ) (n : ℕ) : ℝ :=
  if n=1 then 0 else W n

lemma divisibleOutputPrefix_remove_one (W : ℕ → ℝ) (d T : ℕ) :
    divisibleOutputPrefix (removeOneWeight W) d T =
      divisibleOutputPrefix W d T-(if 1 ≤ T ∧ d ∣ 1 then W 1 else 0) := by
  have he (n : ℕ) : removeOneWeight W n = W n-(if n=1 then W 1 else 0) := by
    unfold removeOneWeight
    by_cases h : n=1 <;> simp [h]
  simp_rw [divisibleOutputPrefix,he]
  rw [sum_sub_distrib]
  simp

lemma remove_one_progression_prefix_error (m d T : ℕ) (hm : 0 < m) (hd : 0 < d) :
    |divisibleOutputPrefix (fun n => removeOneWeight (residueOneOutput m) n-
      removeOneWeight (principalUnitOutput m) n) d T| ≤ progressionPrefixCost m+1 := by
  have he (n : ℕ) : removeOneWeight (residueOneOutput m) n-
      removeOneWeight (principalUnitOutput m) n =
      removeOneWeight (fun n => residueOneOutput m n-principalUnitOutput m n) n := by
    unfold removeOneWeight
    split_ifs <;> simp
  simp_rw [he]
  rw [divisibleOutputPrefix_remove_one]
  apply (abs_sub _ _).trans
  apply _root_.add_le_add (progression_divisible_prefix_error m d T hm hd)
  split_ifs
  · exact progression_pointwise_difference_le m 1 hm
  · norm_num

noncomputable def successorProgressionWeight (P : Finset ℕ) (n : ℕ) : ℝ :=
  ∑ m ∈ P, removeOneWeight (residueOneOutput m) n

noncomputable def successorProgressionPrincipal (P : Finset ℕ) (n : ℕ) : ℝ :=
  ∑ m ∈ P, removeOneWeight (principalUnitOutput m) n

noncomputable def progressionPoolPrefixCost (P : Finset ℕ) : ℝ :=
  ∑ m ∈ P, (progressionPrefixCost m+1)

lemma progressionPoolPrefixCost_nonneg (P : Finset ℕ) :
    0 ≤ progressionPoolPrefixCost P :=
  sum_nonneg (fun m _ => by linarith [progressionPrefixCost_nonneg m])

lemma progression_pool_prefix_error (P : Finset ℕ) (hP : ∀ m ∈ P, 0 < m)
    (d T : ℕ) (hd : 0 < d) :
    |divisibleOutputPrefix (fun n => successorProgressionWeight P n-
      successorProgressionPrincipal P n) d T| ≤ progressionPoolPrefixCost P := by
  simp only [successorProgressionWeight,successorProgressionPrincipal,← sum_sub_distrib]
  unfold divisibleOutputPrefix
  rw [sum_comm]
  apply (abs_sum_le_sum_abs _ _).trans
  exact sum_le_sum (fun m hm => remove_one_progression_prefix_error m d T (hP m hm) hd)

lemma progression_pool_max_prefix_error (P : Finset ℕ) (hP : ∀ m ∈ P, 0 < m)
    (d N : ℕ) (hd : 0 < d) :
    outputMaxPrefix (fun n => successorProgressionWeight P n-
      successorProgressionPrincipal P n) d N ≤ progressionPoolPrefixCost P :=
  progression_pool_prefix_error P hP d _ hd

/-- An unconditional Type I distribution bound for any finite pool of
positive progression moduli, uniform in the output prefix. -/
theorem progression_pool_divisor_error (P : Finset ℕ) (hP : ∀ m ∈ P, 0 < m)
    (Q N : ℕ) :
    outputDivisorError (fun n => successorProgressionWeight P n-
      successorProgressionPrincipal P n) Q N ≤ (Q : ℝ)*progressionPoolPrefixCost P := by
  calc
    _ ≤ ∑ _d ∈ Icc 1 Q, progressionPoolPrefixCost P :=
      sum_le_sum (fun d hd => progression_pool_max_prefix_error P hP d N (mem_Icc.mp hd).1)
    _ = _ := by simp

lemma progression_pool_pointwise_difference_le (P : Finset ℕ) (hP : ∀ m ∈ P, 0 < m)
    (n : ℕ) : |successorProgressionWeight P n-successorProgressionPrincipal P n| ≤ P.card := by
  unfold successorProgressionWeight successorProgressionPrincipal
  rw [← sum_sub_distrib]
  apply (abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _m ∈ P, (1 : ℝ) := by
      apply sum_le_sum
      intro m hm
      unfold removeOneWeight
      by_cases hn : n=1
      · simp [hn]
      · simp only [if_neg hn]
        exact progression_pointwise_difference_le m n (hP m hm)
    _ = _ := by simp

/-- The short term and both Type I terms are controlled unconditionally
for these concrete progression weights and their principal-unit baseline. -/
theorem progression_pool_TypeI_bound (P : Finset ℕ) (hP : ∀ m ∈ P, 0 < m)
    (N U V : ℕ) (hU : 1 ≤ U) :
    successorTypeIError (successorProgressionWeight P) (successorProgressionPrincipal P) N U V ≤
      (U : ℝ)*P.card*Real.log N+
      3*Real.log N*((U*V : ℕ) : ℝ)*progressionPoolPrefixCost P := by
  have h := successorTypeIError_le_bounded_divisor_error (successorProgressionWeight P)
    (successorProgressionPrincipal P) N U V hU P.card (Nat.cast_nonneg _)
    (fun n _ => progression_pool_pointwise_difference_le P hP n)
  have hd := mul_le_mul_of_nonneg_left (progression_pool_divisor_error P hP (U*V) N)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) (Real.log_natCast_nonneg N))
  linarith only [h,hd]

/-- The periodic cost per progression is bounded by an absolute constant;
there is no dependence on the output length or the pool. -/
theorem exists_uniform_progression_pool_prefix_constant :
    ∃ C : ℝ, 0 < C ∧ ∀ P : Finset ℕ, (∀ m ∈ P, 0 < m) →
      progressionPoolPrefixCost P ≤ C*P.card := by
  obtain ⟨C,hC,HC⟩ := exists_uniform_local_factor_div_totient 3 1 (by norm_num) (by norm_num)
  refine ⟨C+2,by linarith,?_⟩
  intro P hP
  calc
    _ ≤ ∑ _m ∈ P, (C+2) := by
      apply sum_le_sum
      intro m hm
      have hmR : (0 : ℝ) < m := by exact_mod_cast hP m hm
      have hh := HC m m (hP m hm) le_rfl
      have he : C*(m : ℝ)^(1 : ℝ)/(m : ℝ)=C := by
        rw [Real.rpow_one]
        field_simp
      rw [he] at hh
      unfold progressionPrefixCost
      linarith only [hh]
    _ = _ := by simp only [sum_const,nsmul_eq_mul]; ring

/-- Uniform, unconditional Type I control for the concrete progression
pool and its principal-unit baseline. No Gram bound is included. -/
theorem exists_uniform_progression_pool_TypeI_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ P : Finset ℕ, (∀ m ∈ P, 0 < m) →
      ∀ N U V : ℕ, 1 ≤ U →
      successorTypeIError (successorProgressionWeight P) (successorProgressionPrincipal P) N U V ≤
        (U : ℝ)*P.card*Real.log N+3*C*((U*V : ℕ) : ℝ)*P.card*Real.log N := by
  obtain ⟨C,hC,HC⟩ := exists_uniform_progression_pool_prefix_constant
  refine ⟨C,hC,?_⟩
  intro P hP N U V hU
  have hh := progression_pool_TypeI_bound P hP N U V hU
  have hcost := mul_le_mul_of_nonneg_left (HC P hP)
    (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) (Real.log_natCast_nonneg N))
      (Nat.cast_nonneg (U*V)))
  nlinarith only [hh,hcost]

lemma weighted_mangoldt_remove_one (W : ℕ → ℝ) (N : ℕ) :
    weightedSum vonMangoldt (removeOneWeight W) N = weightedSum vonMangoldt W N := by
  unfold weightedSum
  apply sum_congr rfl
  intro n hn
  by_cases h : n=1
  · simp [h,removeOneWeight]
  · simp only [removeOneWeight,if_neg h]

lemma weighted_principalUnitOutput (m N : ℕ) :
    weightedSum vonMangoldt (principalUnitOutput m) N =
      (mangoldtSum N-nonunitMangoldt m N)/(m.totient : ℝ) := by
  simp only [weightedSum,principalUnitOutput,mangoldtSum,nonunitMangoldt,
    ← sum_sub_distrib,sum_div]
  apply sum_congr rfl
  intro n hn
  by_cases h : n.Coprime m <;> simp [h,div_eq_mul_inv]

lemma progression_principal_mangoldt_eq (P : Finset ℕ) (N : ℕ) :
    weightedSum vonMangoldt (successorProgressionPrincipal P) N =
      ∑ m ∈ P, (mangoldtSum N-nonunitMangoldt m N)/(m.totient : ℝ) := by
  simp only [weightedSum,successorProgressionPrincipal,mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro m hm
  exact (weighted_mangoldt_remove_one (principalUnitOutput m) N).trans
    (weighted_principalUnitOutput m N)

/-- The principal main term uses the ordinary Mangoldt sum, with an
explicit prime-power correction for nonunits. -/
theorem progression_principal_mangoldt_lower (P : Finset ℕ) (N : ℕ)
    (hP : ∀ m ∈ P, 0 < m ∧ m ≤ N) :
    (mangoldtSum N-(Nat.log 2 N : ℝ)*Real.log N)*
      (∑ m ∈ P, 1/(m.totient : ℝ)) ≤
      weightedSum vonMangoldt (successorProgressionPrincipal P) N := by
  rw [progression_principal_mangoldt_eq,mul_sum]
  apply sum_le_sum
  intro m hm
  have he := nonunitMangoldt_le_liftError m N (hP m hm).1.ne'
  have hlog := mul_le_mul_of_nonneg_left (log_nat_mono (hP m hm).2)
    (Nat.cast_nonneg (Nat.log 2 N))
  have hh : nonunitMangoldt m N ≤ (Nat.log 2 N : ℝ)*Real.log N := he.trans hlog
  have hφ : (0 : ℝ) < m.totient := by exact_mod_cast Nat.totient_pos.mpr (hP m hm).1
  convert div_le_div_of_nonneg_right (sub_le_sub_left hh (mangoldtSum N)) hφ.le using 1
  ring

lemma successorProgressionWeight_one (P : Finset ℕ) :
    successorProgressionWeight P 1=0 := by
  simp [successorProgressionWeight,removeOneWeight]

lemma successorProgressionWeight_nonneg (P : Finset ℕ) (n : ℕ) :
    0 ≤ successorProgressionWeight P n := by
  apply sum_nonneg
  intro m hm
  unfold removeOneWeight
  split_ifs
  · exact le_rfl
  · exact (residueOneOutput_bounds m n).1

lemma successorProgressionWeight_card (P : Finset ℕ) (n : ℕ) (hn : 2 ≤ n) :
    successorProgressionWeight P n = ((P.filter (fun m => m ∣ n-1)).card : ℝ) := by
  have hn1 : n ≠ 1 := by omega
  simp only [successorProgressionWeight,removeOneWeight,if_neg hn1,residueOneOutput,
    residue_one_iff_dvd_pred (by omega : 1 ≤ n)]
  rw [← sum_filter,sum_const,nsmul_eq_mul,mul_one]

/-- Actual output collisions are bounded by the divisor count, not by
the total number of progression moduli in the input pool. -/
theorem successorProgressionWeight_le_divisors (P : Finset ℕ) (n : ℕ) (hn : 1 ≤ n) :
    successorProgressionWeight P n ≤ ((n-1).divisors.card : ℝ) := by
  by_cases hn1 : n=1
  · subst n
    simp only [successorProgressionWeight_one,Nat.sub_self,Nat.divisors_zero,card_empty,
      Nat.cast_zero,le_refl]
  have hn2 : 2 ≤ n := by omega
  rw [successorProgressionWeight_card P n hn2]
  apply Nat.cast_le.mpr
  apply card_le_card
  intro m hm
  exact Nat.mem_divisors.mpr ⟨(mem_filter.mp hm).2,by omega⟩

/-- Every detected prime has a genuinely smooth predecessor when the
retained progression modulus is smooth and its complementary factor is
shorter than Y. This does not assert that prime detection succeeds. -/
theorem progression_prime_output_smooth (P : Finset ℕ) (N Y n : ℕ)
    (hP : ∀ m ∈ P, m ∈ Nat.smoothNumbers Y ∧ N ≤ m*Y)
    (hn : n ∈ positivePrimeOutputs (successorProgressionWeight P) N) :
    n.Prime ∧ n ≤ N ∧ n-1 ∈ Nat.smoothNumbers Y := by
  obtain ⟨hnI,hnprime,hnweight⟩ := mem_filter.mp hn
  have hn2 := hnprime.two_le
  have hnN := (mem_Icc.mp hnI).2
  rw [successorProgressionWeight_card P n hn2] at hnweight
  have hc : 0 < (P.filter (fun m => m ∣ n-1)).card := by exact_mod_cast hnweight
  obtain ⟨m,hm⟩ := card_pos.mp hc
  obtain ⟨hmP,hmn⟩ := mem_filter.mp hm
  obtain ⟨b,hb⟩ := hmn
  have hb0 : 0 < b := by
    by_contra h
    have hz : b=0 := by omega
    simp only [hz,mul_zero] at hb
    omega
  have hmb : m*b < m*Y := by
    have hpred : n-1 < n := by omega
    rw [hb] at hpred
    exact hpred.trans_le (hnN.trans (hP m hmP).2)
  have hbY : b < Y := Nat.lt_of_mul_lt_mul_left hmb
  refine ⟨hnprime,hnN,?_⟩
  rw [hb]
  exact Nat.mul_mem_smoothNumbers (hP m hmP).1 (Nat.mem_smoothNumbers_of_lt hb0 hbY)

end Erdos821.AnalyticSieve.SuccessorVaughan
