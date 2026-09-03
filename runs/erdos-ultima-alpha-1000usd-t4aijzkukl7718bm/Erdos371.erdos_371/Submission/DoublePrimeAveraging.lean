import Submission.SmoothSkewPrimeAveraging

/-! Uniform two-sided small-prime averaging. The error estimate is unconditional;
no cancellation of the resulting determinant-one cofactor sum is asserted. -/

namespace Erdos371
open Finset Filter
open scoped Topology

noncomputable def doublePrimeWeightedSum (S : Finset ℕ) (a : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ range N, primeDivCount S (n+1)*primeDivCount S (n+2)*a (n+1)

private lemma shifted_prime_variance_le (S : Finset ℕ) (N : ℕ)
    (hS : ∀ p ∈ S, p.Prime) (hc : S.card ≤ N) (hN : 0 < N) :
    (∑ n ∈ range N, (primeDivCount S (n+1)-primeReciprocalSum S)^2) ≤
      6*N*primeReciprocalSum S ∧
    (∑ n ∈ range N, (primeDivCount S (n+2)-primeReciprocalSum S)^2) ≤
      6*N*primeReciprocalSum S := by
  have hc' : (S.card : ℝ) ≤ N := by exact_mod_cast hc
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hH : 0 ≤ primeReciprocalSum S := by unfold primeReciprocalSum; positivity
  constructor
  · have h := primeDivCount_variance_upper S N hS
    nlinarith [mul_le_mul_of_nonneg_left hc' hH]
  · have h := primeDivCount_variance_upper S (N+1) hS
    have he := sum_range_succ' (fun n => (primeDivCount S (n+1)-primeReciprocalSum S)^2) N
    have hsub : (∑ n ∈ range N, (primeDivCount S (n+2)-primeReciprocalSum S)^2) ≤
        ∑ n ∈ range (N+1), (primeDivCount S (n+1)-primeReciprocalSum S)^2 := by
      rw [he]
      simp only [Nat.add_assoc,Nat.reduceAdd]
      exact le_add_of_nonneg_right (sq_nonneg _)
    push_cast at h
    have hh := hsub.trans h
    nlinarith [mul_le_mul_of_nonneg_left hc' hH,
      mul_le_mul_of_nonneg_right hN' hH]

private lemma abs_sum_bound_of_sq_bound (f : ℕ → ℝ) (N : ℕ) (H : ℝ)
    (hH : 0 ≤ H) (hf : (∑ n ∈ range N, (f n)^2) ≤ 6*N*H) :
    (∑ n ∈ range N, |f n|) ≤ 3*N*Real.sqrt H := by
  have hcs := sum_mul_sq_le_sq_mul_sq (range N) (fun _ => (1 : ℝ)) (fun n => |f n|)
  simp only [one_mul,one_pow,sum_const,card_range,nsmul_eq_mul,mul_one,sq_abs] at hcs
  have hb := mul_le_mul_of_nonneg_left hf (Nat.cast_nonneg (α := ℝ) N)
  have hsum : 0 ≤ ∑ n ∈ range N, |f n| := sum_nonneg fun _ _ => abs_nonneg _
  have hright : 0 ≤ 3*(N : ℝ)*Real.sqrt H := by positivity
  have hs : (3*(N : ℝ)*Real.sqrt H)^2 = 9*(N : ℝ)^2*H := by
    rw [mul_pow,mul_pow,Real.sq_sqrt hH]
    ring
  have hNH : 0 ≤ (N : ℝ)^2*H := by positivity
  nlinarith

/-- Two shifted prime-divisor counts can replace the constant H^2 uniformly
against any bounded observable. Only one-dimensional variance bounds are used. -/
lemma doublePrimeWeightedSum_error_bound (S : Finset ℕ) (a : ℕ → ℝ) (N : ℕ)
    (hS : ∀ p ∈ S, p.Prime) (ha : ∀ n, |a n| ≤ 1)
    (hc : S.card ≤ N) (hN : 0 < N) :
    |(primeReciprocalSum S)^2*(∑ n ∈ range N, a (n+1)) -
      doublePrimeWeightedSum S a N| ≤
      6*N*primeReciprocalSum S + 6*N*primeReciprocalSum S*Real.sqrt (primeReciprocalSum S) := by
  let H := primeReciprocalSum S
  let x := fun n => primeDivCount S (n+1)-H
  let y := fun n => primeDivCount S (n+2)-H
  have hH : 0 ≤ H := by dsimp [H]; unfold primeReciprocalSum; positivity
  obtain ⟨hx,hy⟩ := shifted_prime_variance_le S N hS hc hN
  change (∑ n ∈ range N, (x n)^2) ≤ 6*N*H at hx
  change (∑ n ∈ range N, (y n)^2) ≤ 6*N*H at hy
  have hx1 := abs_sum_bound_of_sq_bound x N H hH hx
  have hy1 := abs_sum_bound_of_sq_bound y N H hH hy
  have hxy : (∑ n ∈ range N, |x n*y n|) ≤ 6*N*H := by
    have hpoint (n : ℕ) : 2*|x n*y n| ≤ (x n)^2+(y n)^2 := by
      rw [abs_mul]
      nlinarith [sq_nonneg (|x n|-|y n|),sq_abs (x n),sq_abs (y n)]
    have hh := sum_le_sum (s := range N) (fun n _ => hpoint n)
    rw [← mul_sum,sum_add_distrib] at hh
    linarith
  have hterm (n : ℕ) :
      |H^2-primeDivCount S (n+1)*primeDivCount S (n+2)| ≤
        |x n*y n|+H*|x n|+H*|y n| := by
    have he : H^2-primeDivCount S (n+1)*primeDivCount S (n+2) =
        -(x n*y n+H*x n+H*y n) := by dsimp [x,y]; ring
    rw [he,abs_neg]
    have hh := (abs_add_le (x n*y n+H*x n) (H*y n)).trans
      (add_le_add (abs_add_le (x n*y n) (H*x n)) (le_refl _))
    simpa only [abs_mul,abs_of_nonneg hH] using hh
  have he : H^2*(∑ n ∈ range N, a (n+1))-doublePrimeWeightedSum S a N =
      ∑ n ∈ range N, (H^2-primeDivCount S (n+1)*primeDivCount S (n+2))*a (n+1) := by
    simp only [doublePrimeWeightedSum,mul_sum,sub_mul,sum_sub_distrib]
  rw [he]
  calc
    _ ≤ ∑ n ∈ range N,
        |(H^2-primeDivCount S (n+1)*primeDivCount S (n+2))*a (n+1)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ range N, (|x n*y n|+H*|x n|+H*|y n|) := by
      apply sum_le_sum
      intro n hn
      rw [abs_mul]
      exact (mul_le_of_le_one_right (abs_nonneg _) (ha _)).trans (hterm n)
    _ = (∑ n ∈ range N, |x n*y n|)+H*(∑ n ∈ range N, |x n|)+
        H*(∑ n ∈ range N, |y n|) := by simp only [sum_add_distrib,mul_sum]
    _ ≤ 6*N*H + H*(3*N*Real.sqrt H) + H*(3*N*Real.sqrt H) :=
      add_le_add (add_le_add hxy (mul_le_mul_of_nonneg_left hx1 hH))
        (mul_le_mul_of_nonneg_left hy1 hH)
    _ = _ := by dsimp [H]; ring

lemma doublePrimeWeightedSum_normalized_error_bound (S : Finset ℕ) (a : ℕ → ℝ) (N : ℕ)
    (hS : ∀ p ∈ S, p.Prime) (ha : ∀ n, |a n| ≤ 1)
    (hc : S.card ≤ N) (hN : 0 < N) (hH : 0 < primeReciprocalSum S) :
    |(∑ n ∈ range N, a (n+1))/N -
      doublePrimeWeightedSum S a N/(N*(primeReciprocalSum S)^2)| ≤
      6/primeReciprocalSum S + 6/Real.sqrt (primeReciprocalSum S) := by
  let H := primeReciprocalSum S
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hH0 : H ≠ 0 := hH.ne'
  have hsq : (Real.sqrt H)^2 = H := Real.sq_sqrt hH.le
  have hs0 : Real.sqrt H ≠ 0 := (Real.sqrt_pos.mpr hH).ne'
  have hid : (∑ n ∈ range N, a (n+1))/N - doublePrimeWeightedSum S a N/(N*H^2) =
      (H^2*(∑ n ∈ range N, a (n+1))-doublePrimeWeightedSum S a N)/(N*H^2) := by
    field_simp
  change |(∑ n ∈ range N, a (n+1))/N-doublePrimeWeightedSum S a N/(N*H^2)| ≤ _
  rw [hid,abs_div,abs_of_pos (by positivity : 0 < (N : ℝ)*H^2)]
  apply (div_le_iff₀ (by positivity : 0 < (N : ℝ)*H^2)).mpr
  have hb := doublePrimeWeightedSum_error_bound S a N hS ha hc hN
  apply hb.trans_eq
  change 6*N*H+6*N*H*Real.sqrt H = (6/H+6/Real.sqrt H)*(N*H^2)
  field_simp
  nlinarith [hsq]

/-- Uniform convergence of the two-sided replacement error for every moving
bounded observable. This is not convergence of the weighted average itself. -/
theorem doublePrimeWeightedSum_error_tendsto (a : ℕ → ℕ → ℝ) (K : ℕ → ℕ)
    (ha : ∀ N n, |a N n| ≤ 1) (hK : Tendsto K atTop atTop)
    (hKN : ∀ᶠ N : ℕ in atTop, K N ≤ N) :
    Tendsto (fun N => (∑ n ∈ range N, a N (n+1))/N -
      doublePrimeWeightedSum (K N+1).primesBelow (a N) N /
        (N*(primeHarmonic (K N))^2)) atTop (nhds 0) := by
  have hH := primeHarmonic_atTop.comp hK
  have h1 : Tendsto (fun N => 6/primeHarmonic (K N)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hH
  have h2 : Tendsto (fun N => 6/Real.sqrt (primeHarmonic (K N))) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp hH)
  have ht := h1.add h2
  simp only [add_zero] at ht
  apply squeeze_zero_norm' _ ht
  filter_upwards [hKN,hH.eventually_gt_atTop 0,eventually_gt_atTop (0 : ℕ)]
    with N hKN hH hN
  rw [Real.norm_eq_abs]
  exact doublePrimeWeightedSum_normalized_error_bound (K N+1).primesBelow (a N) N
    (fun p hp => (Nat.mem_primesBelow.mp hp).2) (ha N)
    ((primesBelow_succ_card_le (K N)).trans hKN) hN hH

lemma doublePrimeWeightedSum_divisibility (S : Finset ℕ) (a : ℕ → ℝ) (N : ℕ) :
    doublePrimeWeightedSum S a N =
      ∑ p ∈ S, ∑ q ∈ S, ∑ n ∈ range N,
        if p ∣ n+1 ∧ q ∣ n+2 then a (n+1) else 0 := by
  unfold doublePrimeWeightedSum primeDivCount
  simp only [sum_mul,mul_sum]
  conv_rhs => rw [sum_comm]
  rw [sum_comm]
  apply sum_congr rfl
  intro p hp
  rw [sum_comm]
  apply sum_congr rfl
  intro q hq
  apply sum_congr rfl
  intro n hn
  split_ifs <;> simp_all

lemma doublePrimeWeightedSum_progressions (S : Finset ℕ) (a : ℕ → ℝ) (N : ℕ)
    (hS : ∀ p ∈ S, 0 < p) :
    doublePrimeWeightedSum S a N =
      ∑ p ∈ S, ∑ q ∈ S, ∑ m ∈ Icc 1 (N/p),
        if q ∣ p*m+1 then a (p*m) else 0 := by
  rw [doublePrimeWeightedSum_divisibility]
  apply sum_congr rfl
  intro p hp
  apply sum_congr rfl
  intro q hq
  have ht (n : ℕ) :
      (if p ∣ n+1 ∧ q ∣ n+2 then a (n+1) else 0) =
      if p ∣ n+1 then (if q ∣ (n+1)+1 then a (n+1) else 0) else 0 := by
    simp only [Nat.add_assoc,Nat.reduceAdd]
    split_ifs <;> simp_all
  simp_rw [ht]
  exact sum_positive_multiples (fun n => if q ∣ n+1 then a n else 0) p N (hS p hp)

lemma smoothIndicator_div_small (B q n : ℕ) (hq : 0 < q) (hn : 0 < n)
    (hqB : q ≤ B) (hd : q ∣ n) :
    smoothIndicator B (n/q) = smoothIndicator B n := by
  have hm : 0 < n/q := Nat.div_pos (Nat.le_of_dvd hn hd) hq
  have he := smoothIndicator_mul_small B q (n/q) hq hm hqB
  rw [Nat.mul_div_cancel' hd] at he
  exact he.symm

noncomputable def twoSidedPrimeSkewAverage (S : Finset ℕ) (B C N : ℕ) : ℝ :=
  ∑ p ∈ S, ∑ q ∈ S, ∑ m ∈ Icc 1 (N/p),
    if q ∣ p*m+1 then
      smoothIndicator B m*smoothIndicator C ((p*m+1)/q) -
      smoothIndicator C m*smoothIndicator B ((p*m+1)/q)
    else 0

lemma twoSidedPrimeSkewAverage_eq_weighted (S : Finset ℕ) (B C N : ℕ)
    (hS : ∀ p ∈ S, 0 < p ∧ p ≤ B ∧ p ≤ C) :
    twoSidedPrimeSkewAverage S B C N = doublePrimeWeightedSum S
      (fun n => smoothIndicator B n*smoothIndicator C (n+1)-
        smoothIndicator C n*smoothIndicator B (n+1)) N := by
  rw [doublePrimeWeightedSum_progressions S _ N (fun p hp => (hS p hp).1)]
  unfold twoSidedPrimeSkewAverage
  apply sum_congr rfl
  intro p hp
  apply sum_congr rfl
  intro q hq
  apply sum_congr rfl
  intro m hm
  have hm0 : 0 < m := (mem_Icc.mp hm).1
  by_cases hd : q ∣ p*m+1
  · rw [if_pos hd,if_pos hd,
      smoothIndicator_mul_small B p m (hS p hp).1 hm0 (hS p hp).2.1,
      smoothIndicator_mul_small C p m (hS p hp).1 hm0 (hS p hp).2.2,
      smoothIndicator_div_small B q (p*m+1) (hS q hq).1 (by omega) (hS q hq).2.1 hd,
      smoothIndicator_div_small C q (p*m+1) (hS q hq).1 (by omega) (hS q hq).2.2 hd]
  · rw [if_neg hd,if_neg hd]

lemma determinant_one_row (h : ℕ → ℝ) (p q m N : ℕ)
    (hq : 0 < q) (hm : p*m ≤ N) :
    (∑ k ∈ Icc 1 ((N+1)/q), if p*m+1 = q*k then h k else 0) =
      if q ∣ p*m+1 then h ((p*m+1)/q) else 0 := by
  classical
  by_cases hd : q ∣ p*m+1
  · rw [if_pos hd]
    have hk0 : 1 ≤ (p*m+1)/q :=
      Nat.div_pos (Nat.le_of_dvd (by omega : 0 < p*m+1) hd) hq
    have hkN : (p*m+1)/q ≤ (N+1)/q := Nat.div_le_div_right (by omega)
    have hiff (k : ℕ) : p*m+1 = q*k ↔ k = (p*m+1)/q := by
      constructor
      · intro he
        rw [he,Nat.mul_div_right _ hq]
      · rintro rfl
        exact (Nat.mul_div_cancel' hd).symm
    simp_rw [hiff]
    simp [mem_Icc.mpr ⟨hk0,hkN⟩]
  · rw [if_neg hd]
    apply sum_eq_zero
    intro k hk
    apply if_neg
    intro he
    exact hd ⟨k,he⟩

/-- Exact determinant-one cofactor formula. Both cofactor endpoints are kept;
no equidistribution in the progression or cancellation is used here. -/
theorem twoSidedPrimeSkewAverage_cofactor_formula (S : Finset ℕ) (B C N : ℕ)
    (hS : ∀ p ∈ S, 0 < p) :
    twoSidedPrimeSkewAverage S B C N =
      ∑ p ∈ S, ∑ q ∈ S, ∑ m ∈ Icc 1 (N/p), ∑ k ∈ Icc 1 ((N+1)/q),
        if p*m+1 = q*k then
          smoothIndicator B m*smoothIndicator C k -
            smoothIndicator C m*smoothIndicator B k
        else 0 := by
  unfold twoSidedPrimeSkewAverage
  apply sum_congr rfl
  intro p hp
  apply sum_congr rfl
  intro q hq
  apply sum_congr rfl
  intro m hm
  have hmN : p*m ≤ N := by
    simpa only [Nat.mul_comm] using
      (Nat.le_div_iff_mul_le (hS p hp)).mp (mem_Icc.mp hm).2
  exact (determinant_one_row (fun k => smoothIndicator B m*smoothIndicator C k -
    smoothIndicator C m*smoothIndicator B k) p q m N (hS q hq) hmN).symm

/-- Two-sided prime averaging of the actual moving smooth-cutoff skew has
vanishing replacement error. The remaining cofactor sum is not estimated. -/
theorem smoothCutoffSkew_twoSided_prime_error_tendsto (B C K : ℕ → ℕ)
    (hK : Tendsto K atTop atTop)
    (hcut : ∀ᶠ N : ℕ in atTop, K N ≤ B N ∧ K N ≤ C N ∧ K N ≤ N) :
    Tendsto (fun N => smoothCutoffSkew (B N) (C N) N/N -
      twoSidedPrimeSkewAverage (K N+1).primesBelow (B N) (C N) N /
        (N*(primeHarmonic (K N))^2)) atTop (nhds 0) := by
  have ht := doublePrimeWeightedSum_error_tendsto
    (fun N n => smoothIndicator (B N) n*smoothIndicator (C N) (n+1)-
      smoothIndicator (C N) n*smoothIndicator (B N) (n+1)) K
    (fun N n => smoothSkewPoint_abs_le_one (B N) (C N) n) hK
    (hcut.mono fun N h => h.2.2)
  apply ht.congr'
  filter_upwards [hcut] with N hcut
  have hS (p : ℕ) (hp : p ∈ (K N+1).primesBelow) :
      0 < p ∧ p ≤ B N ∧ p ≤ C N := by
    obtain ⟨hpK,hp⟩ := Nat.mem_primesBelow.mp hp
    exact ⟨hp.pos,(by omega : p ≤ K N).trans hcut.1,
      (by omega : p ≤ K N).trans hcut.2.1⟩
  rw [twoSidedPrimeSkewAverage_eq_weighted _ _ _ _ hS]
  rfl

#print axioms doublePrimeWeightedSum_error_bound
#print axioms doublePrimeWeightedSum_normalized_error_bound
#print axioms doublePrimeWeightedSum_error_tendsto
#print axioms twoSidedPrimeSkewAverage_cofactor_formula
#print axioms smoothCutoffSkew_twoSided_prime_error_tendsto
end Erdos371
