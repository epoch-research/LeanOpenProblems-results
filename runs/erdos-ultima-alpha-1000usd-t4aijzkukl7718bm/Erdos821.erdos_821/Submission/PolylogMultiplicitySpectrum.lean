import Submission.PolylogSmoothInputFibers
import Submission.PolynomialPoolWeight

/-!
# The critical exponent for one polylogarithmically restricted multiplicity

This concerns only preimages whose prime factors are bounded by the specified
fixed power of log n. The unrestricted conjecture is not settled.
-/

open Nat Filter
open scoped Classical BigOperators
namespace Erdos821
open AnalyticSieve HigherDivisors LogarithmicOverlap
set_option maxHeartbeats 3000000

lemma poolWeight_primesBelow_le_log_four (y : ℕ) :
    poolWeight y.primesBelow ≤ (y : ℝ)*Real.log 4 := by
  calc
    _ ≤ ∑ p ∈ y.primesBelow, Real.log (p : ℝ) := by
      apply Finset.sum_le_sum
      intro p hp
      exact log_nat_mono (Nat.sub_le p 1)
    _ = Real.log (ClosedPadding.primeProduct y.primesBelow : ℝ) := by
      unfold ClosedPadding.primeProduct
      rw [Nat.cast_prod, Real.log_prod]
      intro p hp
      exact_mod_cast (Nat.mem_primesBelow.mp hp).2.ne_zero
    _ ≤ Real.log ((4^y : ℕ) : ℝ) := by
      apply Real.log_le_log
      · exact_mod_cast ClosedPadding.primeProduct_pos y.primesBelow
          (fun p hp => (Nat.mem_primesBelow.mp hp).2)
      · exact_mod_cast ClosedPadding.primeProduct_primesBelow_le_four_pow y
    _ = _ := by rw [Nat.cast_pow,Nat.cast_ofNat,Real.log_pow]

lemma eventually_polylog_input_fiber_bound (κ α : ℝ) (hκ : 1<κ)
    (hα : 1-1/κ<α) (hα1 : α<1) :
    ∀ᶠ n : ℕ in atTop, ∀ F : Finset ℕ,
      (∀ m ∈ F, totient m=n ∧ ∀ p ∈ m.primeFactors,
        (p : ℝ) ≤ (4*Real.log (n : ℝ))^κ) →
      (F.card : ℝ) ≤ (n : ℝ)^α := by
  have hκ0 : 0<κ := by linarith
  have hinv : 1/κ<1 := (div_lt_one hκ0).mpr hκ
  have hα0 : 0<α := by linarith
  have hβα : κ*(1-α)<1 := by
    have h := (lt_div_iff₀ hκ0).mp (show 1-α<1/κ by linarith)
    nlinarith only [h]
  obtain ⟨s,t,hs,hsα,hst,ht,he⟩ := exists_pool_rankin_parameters α κ hα0 hα1 hκ0 hβα
  let C : ℝ := ((4 : ℝ)^κ+2)*Real.log 4
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity [Real.log_pos (by norm_num : (1 : ℝ)<4)]
  have hloglim : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_pool_weight_bound_controls_fiber C α κ s t hC hκ0.le
    hs.le hst.le ht hsα he,hloglim.eventually (eventually_ge_atTop 1)]
    with n hn hlog
  intro F hF
  let R : ℝ := (4*Real.log (n : ℝ))^κ
  let Y := ⌊R⌋₊+2
  let P := Y.primesBelow
  have hR : 0 ≤ R := Real.rpow_nonneg (by linarith) _
  have hP : ∀ p ∈ P, p.Prime := fun p hp => (Nat.mem_primesBelow.mp hp).2
  have hFP : ∀ m ∈ F, totient m=n ∧ m.primeFactors ⊆ P := by
    intro m hm
    refine ⟨(hF m hm).1,?_⟩
    intro p hp
    have hpR : p ≤ ⌊R⌋₊ := Nat.le_floor ((hF m hm).2 p hp)
    exact Nat.mem_primesBelow.mpr ⟨by dsimp [Y]; omega,Nat.prime_of_mem_primeFactors hp⟩
  have hY : (Y : ℝ) ≤ R+2 := by
    dsimp [Y]
    push_cast
    linarith [Nat.floor_le hR]
  have hpow : 1 ≤ (Real.log (n : ℝ))^κ := Real.one_le_rpow hlog hκ0.le
  have hReq : R = (4 : ℝ)^κ*(Real.log (n : ℝ))^κ :=
    Real.mul_rpow (by norm_num) (by linarith)
  have hW : poolWeight P ≤ C*(Real.log (n : ℝ))^κ := by
    calc
      _ ≤ (Y : ℝ)*Real.log 4 := poolWeight_primesBelow_le_log_four Y
      _ ≤ (R+2)*Real.log 4 := mul_le_mul_of_nonneg_right hY (Real.log_nonneg (by norm_num))
      _ ≤ _ := by
        rw [hReq]
        dsimp [C]
        have hh := mul_le_mul_of_nonneg_right hpow (Real.log_nonneg (by norm_num : (1 : ℝ)≤4))
        nlinarith only [hh]
  exact hn F P hP hFP hW

noncomputable def gPolylog (κ : ℝ) (n : ℕ) : ℕ :=
  {m : ℕ | totient m=n ∧ ∀ p ∈ m.primeFactors,
    (p : ℝ) ≤ (4*Real.log (n : ℝ))^κ}.ncard

lemma finite_polylog_totient_fiber (κ : ℝ) (n : ℕ) :
    {m : ℕ | totient m=n ∧ ∀ p ∈ m.primeFactors,
      (p : ℝ) ≤ (4*Real.log (n : ℝ))^κ}.Finite :=
  (finite_totient_fiber n).subset (fun _ hm => hm.1)

lemma gPolylog_le_g (κ : ℝ) (n : ℕ) : gPolylog κ n ≤ g n :=
  Set.ncard_le_ncard (fun _ hm => hm.1) (finite_totient_fiber n)

lemma finite_fiber_card_le_gPolylog (κ : ℝ) (n : ℕ) (F : Finset ℕ)
    (hF : ∀ m ∈ F, totient m=n ∧ ∀ p ∈ m.primeFactors,
      (p : ℝ) ≤ (4*Real.log (n : ℝ))^κ) : F.card ≤ gPolylog κ n := by
  have h := Set.ncard_le_ncard (s := (F : Set ℕ))
    (fun m hm => hF m hm) (finite_polylog_totient_fiber κ n)
  simpa only [Set.ncard_coe_finset,gPolylog] using h

/-- The upper exponent applies to all inputs in the restricted fiber, not
just squarefree inputs or the constructed lower-bound families. -/
theorem eventually_gPolylog_le (κ α : ℝ) (hκ : 1<κ) (hα : 1-1/κ<α) :
    ∀ᶠ n : ℕ in atTop, (gPolylog κ n : ℝ) ≤ (n : ℝ)^α := by
  by_cases hα1 : α<1
  · filter_upwards [eventually_polylog_input_fiber_bound κ α hκ hα hα1] with n hn
    have H := finite_polylog_totient_fiber κ n
    have hF : ∀ m ∈ H.toFinset, totient m=n ∧ ∀ p ∈ m.primeFactors,
        (p : ℝ) ≤ (4*Real.log (n : ℝ))^κ := by
      intro m hm
      exact H.mem_toFinset.mp hm
    simpa only [gPolylog, Set.ncard_eq_toFinset_card _ H] using hn H.toFinset hF
  · have h1α : 1 ≤ α := le_of_not_gt hα1
    filter_upwards [eventually_g_lt_self,eventually_ge_atTop 1] with n hn hn1
    have hcard : (gPolylog κ n : ℝ) ≤ n := by
      exact_mod_cast (gPolylog_le_g κ n).trans hn.le
    exact hcard.trans (by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
        (show (1 : ℝ)≤n by exact_mod_cast hn1) h1α)

/-- Every exponent below the current unrestricted lower threshold is already
attained with this fixed polylogarithmic input-prime bound. -/
theorem infinite_gPolylog_gt_wide_block (γ : ℝ) (hγ : γ<1036568/2000001) :
    {n : ℕ | (gPolylog (2000001/963433) n : ℝ) > (n : ℝ)^γ}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro N
  obtain ⟨n,F,hn,hcard,hF⟩ := wide_block_polylog_input_fibers γ hγ N
  refine ⟨n,?_,hn⟩
  exact hcard.trans_le (by exact_mod_cast
    finite_fiber_card_le_gPolylog _ n F (fun m hm => (hF m hm).2))

/-- Exponents strictly above that threshold occur only finitely often for
the restricted multiplicity. This does not bound the unrestricted g. -/
theorem finite_gPolylog_gt_wide_block (γ : ℝ) (hγ : 1036568/2000001<γ) :
    {n : ℕ | (gPolylog (2000001/963433) n : ℝ) > (n : ℝ)^γ}.Finite := by
  have H := eventually_gPolylog_le (2000001/963433) γ (by norm_num) (by norm_num; exact hγ)
  obtain ⟨N,hN⟩ := eventually_atTop.mp H
  apply (Set.finite_Iio N).subset
  intro n hn
  by_contra h
  exact hn.not_ge (hN n (le_of_not_gt h))

/-- The critical exponent is determined exactly for this restricted
multiplicity. The behavior at the critical exponent itself is not asserted. -/
theorem polylog_critical_exponent_wide_block :
    sSup {γ : ℝ | {n : ℕ | (gPolylog (2000001/963433) n : ℝ) >
      (n : ℝ)^γ}.Infinite} = 1036568/2000001 := by
  apply csSup_eq_of_forall_le_of_forall_lt_exists_gt
    ⟨0,infinite_gPolylog_gt_wide_block 0 (by norm_num)⟩
  · intro γ hγ
    by_contra h
    exact (finite_gPolylog_gt_wide_block γ (lt_of_not_ge h)).not_infinite hγ
  · intro γ hγ
    obtain ⟨δ,hγδ,hδ⟩ := exists_between hγ
    exact ⟨δ,infinite_gPolylog_gt_wide_block δ hδ,hγδ⟩


end Erdos821
