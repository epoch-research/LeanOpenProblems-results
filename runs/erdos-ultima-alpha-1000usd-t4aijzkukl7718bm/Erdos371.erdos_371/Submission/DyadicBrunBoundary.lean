import Submission.BothLargePrimeBound

/-! Absolute reciprocal summability for sufficiently thin moving top-prime
bands. This is a boundary estimate, not cancellation for the interior. -/
namespace Erdos371
open Finset Filter
open scoped Topology
set_option autoImplicit false

/-- A dyadic blocking criterion without any monotonicity hypothesis on f. -/
lemma summable_of_nonneg_dyadic_blocks (f : ℕ → ℝ) (hf : ∀ n, 0≤f n)
    (hs : Summable (fun k => ∑ n ∈ Ico (2^k) (2^(k+1)), f n)) : Summable f := by
  have he (K : ℕ) : (∑ n ∈ range (2^K), f n) =
      f 0+∑ k ∈ range K, ∑ n ∈ Ico (2^k) (2^(k+1)), f n := by
    induction K with
    | zero => simp
    | succ K ih =>
      have hp : 2^K≤(2:ℕ)^(K+1) := Nat.pow_le_pow_right (by omega) (by omega)
      rw [← sum_range_add_sum_Ico f hp,ih,sum_range_succ]
      ring
  apply summable_of_sum_range_le hf (c := f 0+∑' k, ∑ n ∈ Ico (2^k) (2^(k+1)), f n)
  intro N
  calc
    _ ≤ ∑ n ∈ range (2^N), f n :=
      sum_le_sum_of_subset_of_nonneg (range_mono Nat.lt_two_pow_self.le) (fun n _ _ => hf n)
    _ = _ := he N
    _ ≤ _ := add_le_add_right (hs.sum_le_tsum (range N) (fun k _ => sum_nonneg (fun n _ => hf n))) _

noncomputable def dyadicTopPrimePair (u : ℕ → ℝ) (n : ℕ) : Prop :=
  let k := Nat.log 2 n
  ((2 : ℝ)^(k+1))^(1-u k)<Nat.maxPrimeFac n ∧
    ((2 : ℝ)^(k+1))^(1-u k)<Nat.maxPrimeFac (n+1)

noncomputable def dyadicTopPrimeReciprocal (u : ℕ → ℝ) (n : ℕ) : ℝ := by
  classical
  exact if dyadicTopPrimePair u n then 1/n else 0

lemma dyadicTopPrimeReciprocal_nonneg (u : ℕ → ℝ) (n : ℕ) :
    0≤dyadicTopPrimeReciprocal u n := by
  unfold dyadicTopPrimeReciprocal
  split_ifs <;> positivity

lemma dyadicTopPrimeReciprocal_block_bound (u : ℕ → ℝ) (k : ℕ)
    (hu0 : 0≤u k) (hu : u k≤1/8) :
    (∑ n ∈ Ico (2^k) (2^(k+1)), dyadicTopPrimeReciprocal u n) ≤
      2*(FiniteSieve.largePairConstant*(u k+1/Real.log ((2 : ℝ)^(k+1)))^2+
        (2 : ℝ)^65*((2 : ℝ)^(k+1))^(-1/2 : ℝ)) := by
  classical
  let S := (Ico (2^k) (2^(k+1))).filter (dyadicTopPrimePair u)
  have hN : 1<(2 : ℕ)^(k+1) := by
    rw [pow_succ]
    have hh : 0<(2 : ℕ)^k := pow_pos (by omega) _
    omega
  have hS : S ⊆ FiniteSieve.bothLargePrimeSet (2^(k+1)) (u k) := by
    intro n hn
    obtain ⟨hn,hh⟩ := mem_filter.mp hn
    have hn' := mem_Ico.mp hn
    have hlog : Nat.log 2 n=k := Nat.log_eq_of_pow_le_of_lt_pow hn'.1 hn'.2
    change dyadicTopPrimePair u n at hh
    simp only [dyadicTopPrimePair,hlog] at hh
    apply mem_filter.mpr
    refine ⟨mem_range.mpr hn'.2,?_⟩
    simpa only [Nat.cast_pow,Nat.cast_ofNat] using hh
  have hb : (∑ n ∈ Ico (2^k) (2^(k+1)), dyadicTopPrimeReciprocal u n) ≤
      (S.card : ℝ)/(2 : ℝ)^k := by
    simp only [dyadicTopPrimeReciprocal,← sum_filter]
    calc
      _ ≤ ∑ _n ∈ S, (1 : ℝ)/(2 : ℝ)^k := by
        apply sum_le_sum
        intro n hn
        have hn' := (mem_Ico.mp (mem_filter.mp hn).1).1
        apply one_div_le_one_div_of_le (by positivity)
        exact_mod_cast hn'
      _ = _ := by simp only [sum_const,nsmul_eq_mul,div_eq_mul_inv,one_mul]
  have hc := div_le_div_of_nonneg_right (Nat.cast_le.mpr (card_le_card hS))
    (by positivity : (0 : ℝ)≤(2 : ℝ)^k)
  have hr := FiniteSieve.bothLargePrimeSet_ratio_bound (2^(k+1)) (u k) hN hu0 hu
  push_cast at hr
  have he (x : ℝ) : x/(2 : ℝ)^k=2*(x/(2 : ℝ)^(k+1)) := by
    rw [pow_succ]
    field_simp
  rw [he (((FiniteSieve.bothLargePrimeSet (2^(k+1)) (u k)).card : ℝ))] at hc
  exact (hb.trans hc).trans (mul_le_mul_of_nonneg_left hr (by norm_num))

lemma summable_inverse_log_dyadic_sq :
    Summable (fun k : ℕ => (1/Real.log ((2 : ℝ)^(k+1)))^2) := by
  have hs : Summable (fun k : ℕ => (1 : ℝ)/(k+1 : ℝ)^2) := by
    have ht := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by omega : 1<(2 : ℕ)))
    simpa only [Nat.cast_add,Nat.cast_one] using ht
  convert hs.mul_left (1/(Real.log 2)^2) using 1
  funext k
  rw [Real.log_pow]
  push_cast
  have hl : Real.log (2 : ℝ)≠0 := ne_of_gt (Real.log_pos (by norm_num))
  have hk : (k : ℝ)+1≠0 := by positivity
  field_simp

lemma summable_dyadic_inverse_sqrt :
    Summable (fun k : ℕ => ((2 : ℝ)^(k+1))^(-1/2 : ℝ)) := by
  have hr0 : 0≤(2 : ℝ)^(-1/2 : ℝ) := Real.rpow_nonneg (by norm_num) _
  have hr1 : (2 : ℝ)^(-1/2 : ℝ)<1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have hs := (summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one hr0 hr1)
  simpa only [Real.rpow_pow_comm (by norm_num : (0 : ℝ)≤2)] using hs

/-- A square-summable sequence of top-band widths gives a globally summable
reciprocal exceptional set, by the uniform two-prime sieve. -/
theorem summable_dyadicTopPrimeReciprocal (u : ℕ → ℝ)
    (hu0 : ∀ k, 0≤u k) (hu : ∀ k, u k≤1/8)
    (hs : Summable (fun k => (u k)^2)) :
    Summable (dyadicTopPrimeReciprocal u) := by
  apply summable_of_nonneg_dyadic_blocks _ (dyadicTopPrimeReciprocal_nonneg u)
  have hmajor : Summable (fun k : ℕ =>
      2*(FiniteSieve.largePairConstant*(2*(u k)^2+2*(1/Real.log ((2 : ℝ)^(k+1)))^2)+
        (2 : ℝ)^65*((2 : ℝ)^(k+1))^(-1/2 : ℝ))) :=
    ((((hs.mul_left 2).add (summable_inverse_log_dyadic_sq.mul_left 2)).mul_left
      FiniteSieve.largePairConstant).add (summable_dyadic_inverse_sqrt.mul_left ((2 : ℝ)^65))).mul_left 2
  apply Summable.of_nonneg_of_le (fun k => sum_nonneg (fun n _ => dyadicTopPrimeReciprocal_nonneg u n)) _ hmajor
  intro k
  apply (dyadicTopPrimeReciprocal_block_bound u k (hu0 k) (hu k)).trans
  have hc : 0≤FiniteSieve.largePairConstant := by unfold FiniteSieve.largePairConstant; positivity
  have hh : (u k+1/Real.log ((2 : ℝ)^(k+1)))^2 ≤
      2*(u k)^2+2*(1/Real.log ((2 : ℝ)^(k+1)))^2 := by
    nlinarith [sq_nonneg (u k-1/Real.log ((2 : ℝ)^(k+1)))]
  gcongr

noncomputable def threeQuarterBandWidth (k : ℕ) : ℝ :=
  (1/8 : ℝ)*(k+1 : ℝ)^(-3/4 : ℝ)

lemma threeQuarterBandWidth_nonneg (k : ℕ) : 0≤threeQuarterBandWidth k := by
  unfold threeQuarterBandWidth
  positivity

lemma threeQuarterBandWidth_le (k : ℕ) : threeQuarterBandWidth k≤1/8 := by
  have hh : (k+1 : ℝ)^(-3/4 : ℝ)≤1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by have := Nat.cast_nonneg (α := ℝ) k; linarith) (by norm_num)
  unfold threeQuarterBandWidth
  linarith

lemma summable_threeQuarterBandWidth_sq : Summable (fun k => (threeQuarterBandWidth k)^2) := by
  have hs : Summable (fun k : ℕ => (k+1 : ℝ)^(-3/2 : ℝ)) := by
    have ht := (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr (by norm_num : (-3/2 : ℝ)< -1))
    simpa only [Nat.cast_add,Nat.cast_one] using ht
  convert hs.mul_left (1/64 : ℝ) using 1
  funext k
  unfold threeQuarterBandWidth
  have he : ((k+1 : ℝ)^(-3/4 : ℝ))^2=(k+1 : ℝ)^(-3/2 : ℝ) := by
    calc
      _ = ((k+1 : ℝ)^(-3/4 : ℝ))^(2 : ℝ) := by rw [Real.rpow_two]
      _ = _ := by rw [← Real.rpow_mul (by positivity : (0 : ℝ)≤k+1)]; norm_num
  rw [mul_pow,he]
  norm_num

/-- A concrete subexponential cofactor boundary with finite reciprocal sum.
This is stronger than a natural-density-zero boundary statement. -/
theorem summable_threeQuarter_top_prime_pairs :
    Summable (dyadicTopPrimeReciprocal threeQuarterBandWidth) :=
  summable_dyadicTopPrimeReciprocal threeQuarterBandWidth
    threeQuarterBandWidth_nonneg threeQuarterBandWidth_le summable_threeQuarterBandWidth_sq

#print axioms summable_dyadicTopPrimeReciprocal
#print axioms summable_threeQuarter_top_prime_pairs
end Erdos371
