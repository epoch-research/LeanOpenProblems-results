import Submission.WeightedUnitDiagonal

/-! Complementary indices supported entirely above an independent cutoff W.
Their colour is unchanged when a smaller rough prime survives. -/
namespace Erdos371
open Finset Filter FiniteSieve
open scoped Topology

lemma roughRadical_dvd_of_le (B W m : ℕ) (hBW : B ≤ W) :
    roughRadical W m ∣ roughRadical B m := by
  apply prod_dvd_prod_of_subset
  intro p hp
  obtain ⟨hp,hW⟩ := mem_filter.mp hp
  exact mem_filter.mpr ⟨hp,hBW.trans_lt hW⟩

lemma minFac_div_of_not_dvd (R e : ℕ) (hR : 1 < R) (he : e ∣ R)
    (hpe : ¬R.minFac ∣ e) : (R/e).minFac=R.minFac := by
  have hp := Nat.minFac_prime (by omega : R ≠ 1)
  have hd : R.minFac ∣ R/e := by
    have h : R.minFac ∣ e*(R/e) := by
      simpa only [Nat.mul_div_cancel' he] using Nat.minFac_dvd R
    exact (hp.dvd_mul.mp h).resolve_left hpe
  have hq1 : R/e ≠ 1 := by
    intro h
    rw [h] at hd
    exact hp.not_dvd_one hd
  have hq := Nat.minFac_prime hq1
  apply le_antisymm (Nat.minFac_le_of_dvd hp.two_le hd)
  exact Nat.minFac_le_of_dvd hq.two_le ((Nat.minFac_dvd (R/e)).trans (Nat.div_dvd_of_dvd he))

lemma high_divisor_colour (B W n e : ℕ) (hBW : B ≤ W)
    (he : e ∣ roughRadical W (n*(n+1)))
    (hR : 1 < roughRadical B (n*(n+1)))
    (hmin : (roughRadical B (n*(n+1))).minFac ≤ W) :
    divisorSideColour n (roughRadical B (n*(n+1))/e)=
      divisorSideColour n (roughRadical B (n*(n+1))) := by
  have hed := he.trans (roughRadical_dvd_of_le B W _ hBW)
  have hp := Nat.minFac_prime (by omega : roughRadical B (n*(n+1)) ≠ 1)
  have hnot : ¬(roughRadical B (n*(n+1))).minFac ∣ e := by
    intro hd
    exact (not_lt_of_ge hmin) (roughRadical_prime_large W _ _ hp (hd.trans he))
  simp only [divisorSideColour,minFac_div_of_not_dvd _ e hR hed hnot]

noncomputable def highDivisorWeight (W X n : ℕ) : ℝ :=
  ∑ e ∈ (roughRadical W (n*(n+1))).divisors,
    if 1 < e ∧ e ≤ X then (ArithmeticFunction.moebius e : ℝ) else 0

noncomputable def highComplementAt (B D W X n : ℕ) : ℝ :=
  (ArithmeticFunction.moebius (roughRadical B (n*(n+1))) : ℝ)*
    ∑ e ∈ (roughRadical W (n*(n+1))).divisors,
      if 1 < e ∧ e ≤ X ∧ D*e < roughRadical B (n*(n+1)) then
        (ArithmeticFunction.moebius e : ℝ)*divisorSideColour n (roughRadical B (n*(n+1))/e)
      else 0

/-- This is exactly the indicated subrange of the original complementary
sum, not a different choice of divisibility weights. -/
lemma highComplementAt_original_support (B D W X n : ℕ) (hBW : B ≤ W) (hn : 0 < n) :
    highComplementAt B D W X n=
      (ArithmeticFunction.moebius (roughRadical B (n*(n+1))) : ℝ)*
        ∑ e ∈ (roughRadical B (n*(n+1))).divisors,
          if 1 < e ∧ e ≤ X ∧ W < e.minFac ∧ D*e < roughRadical B (n*(n+1)) then
            (ArithmeticFunction.moebius e : ℝ)*divisorSideColour n (roughRadical B (n*(n+1))/e)
          else 0 := by
  unfold highComplementAt
  congr 1
  rw [← sum_filter,← sum_filter]
  congr 1
  ext e
  simp only [mem_filter,Nat.mem_divisors]
  constructor
  · rintro ⟨⟨he,_⟩,he1,heX,heD⟩
    refine ⟨⟨he.trans (roughRadical_dvd_of_le B W _ hBW),(roughRadical_pos B _).ne'⟩,
      he1,heX,?_,heD⟩
    exact roughRadical_prime_large W _ _ (Nat.minFac_prime (by omega)) ((Nat.minFac_dvd e).trans he)
  · rintro ⟨⟨he,_⟩,he1,heX,heW,heD⟩
    refine ⟨⟨?_,(roughRadical_pos W _).ne'⟩,he1,heX,heD⟩
    exact squarefree_rough_dvd_radical W _ e (by positivity)
      (he.trans (roughRadical_dvd B _)) ((roughRadical_squarefree B _).squarefree_of_dvd he) heW

lemma highComplementAt_eq_weighted_unit (B D W X n : ℕ) (hBW : B ≤ W)
    (hR : 1 < roughRadical B (n*(n+1)))
    (hmin : (roughRadical B (n*(n+1))).minFac ≤ W)
    (hlarge : D*X < roughRadical B (n*(n+1))) :
    highComplementAt B D W X n=highDivisorWeight W X n*untruncatedRoughUnit B n := by
  unfold highComplementAt highDivisorWeight untruncatedRoughUnit
  rw [mul_left_comm,sum_mul]
  congr 1
  apply sum_congr rfl
  intro e he
  by_cases h : 1 < e ∧ e ≤ X
  · have hd : D*e < roughRadical B (n*(n+1)) := (Nat.mul_le_mul_left D h.2).trans_lt hlarge
    rw [if_pos ⟨h.1,h.2,hd⟩,if_pos h,
      high_divisor_colour B W n e hBW (Nat.mem_divisors.mp he).1 hR hmin]
  · have hn : ¬(1 < e ∧ e ≤ X ∧ D*e < roughRadical B (n*(n+1))) := fun he => h ⟨he.1,he.2.1⟩
    rw [if_neg hn,if_neg h,zero_mul]

lemma squarefree_divisors_card_le (R : ℕ) (hR : Squarefree R) :
    R.divisors.card ≤ 2^R.primeFactors.card := by
  rw [← card_powerset]
  apply card_le_card_of_injOn Nat.primeFactors
  · intro e he
    exact mem_powerset.mpr (Nat.primeFactors_mono (Nat.mem_divisors.mp he).1 hR.ne_zero)
  · intro e he f hf hef
    have heq := Nat.prod_primeFactors_of_squarefree (hR.squarefree_of_dvd (Nat.mem_divisors.mp he).1)
    have hfq := Nat.prod_primeFactors_of_squarefree (hR.squarefree_of_dvd (Nat.mem_divisors.mp hf).1)
    rw [← heq,← hfq,hef]

lemma highRadical_card_bound (W L N n : ℕ) (hW : 1 < W)
    (hWN : N+1 ≤ W^L) (hn : 0 < n) (hnN : n ≤ N) :
    (roughRadical W (n*(n+1))).primeFactors.card ≤ 2*L := by
  apply short_prime_product_card_le _ W (2*L) hW
  · intro p hp
    exact roughRadical_prime_large W _ p (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp)
  · rw [Nat.prod_primeFactors_of_squarefree (roughRadical_squarefree W _)]
    calc
      _ ≤ n*(n+1) := Nat.le_of_dvd (by positivity) (roughRadical_dvd W _)
      _ ≤ (N+1)^2 := by nlinarith
      _ ≤ (W^L)^2 := Nat.pow_le_pow_left hWN 2
      _ = _ := by rw [← pow_mul]; congr 1; omega

lemma high_weight_and_complement_bound (W L N n B D X : ℕ) (hW : 1 < W)
    (hWN : N+1 ≤ W^L) (hn : 0 < n) (hnN : n ≤ N) :
    |highDivisorWeight W X n| ≤ (2 : ℝ)^(2*L) ∧
    |highComplementAt B D W X n| ≤ (2 : ℝ)^(2*L) := by
  have hc : ((roughRadical W (n*(n+1))).divisors.card : ℝ) ≤ (2 : ℝ)^(2*L) := by
    exact_mod_cast (squarefree_divisors_card_le _ (roughRadical_squarefree W _)).trans
      (Nat.pow_le_pow_right (by norm_num) (highRadical_card_bound W L N n hW hWN hn hnN))
  have hm (e : ℕ) : |(ArithmeticFunction.moebius e : ℝ)| ≤ 1 := by
    rw [← Int.cast_abs]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := e)
  constructor
  · apply le_trans _ hc
    unfold highDivisorWeight
    apply (abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ _e ∈ (roughRadical W (n*(n+1))).divisors, (1 : ℝ) := by
        apply sum_le_sum
        intro e _
        split_ifs
        · exact hm e
        · norm_num
      _ = _ := by simp
  · apply le_trans _ hc
    unfold highComplementAt
    rw [abs_mul,roughRadical_moebius_abs,one_mul]
    apply (abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ _e ∈ (roughRadical W (n*(n+1))).divisors, (1 : ℝ) := by
        apply sum_le_sum
        intro e _
        split_ifs
        · rw [abs_mul,divisorSideColour_abs,mul_one]
          exact hm e
        · norm_num
      _ = _ := by simp

lemma highDivisorWeight_zero (W X : ℕ) : highDivisorWeight W X 0=0 := by
  simp [highDivisorWeight,roughRadical]

lemma highComplementAt_zero (B D W X : ℕ) : highComplementAt B D W X 0=0 := by
  simp [highComplementAt,roughRadical]

#print axioms highComplementAt_eq_weighted_unit
#print axioms high_weight_and_complement_bound
end Erdos371
