import Submission.SelbergLowerMain

/-! A lower-supported Selberg test with explicit distribution errors. The
test is not asserted to be bounded by 1 on rough integers. -/
namespace Erdos972SelbergLowerTest

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Erdos972SelbergWeights Erdos972PairSieve Erdos972SelbergLocalCost
open Erdos972SelbergLowerMain

set_option maxHeartbeats 1500000

noncomputable def smallPrimeCount (Z n : ℕ) : ℝ :=
  ∑ p ∈ smallPrimes Z, if p ∣ n then (1:ℝ) else 0

noncomputable def lowerTest (R Z n : ℕ) : ℝ := (1-smallPrimeCount Z n)*majorant R n

lemma majorant_upper {R : ℕ} (hR : 1 ≤ R) (n : ℕ) : majorant R n ≤ (R:ℝ)^4 := by
  rw [majorant_expansion]
  calc
    _ ≤ ∑ z ∈ weightIndices R, |weightCoeff R z| := by
      apply sum_le_sum
      intro z hz
      split_ifs
      · exact le_abs_self _
      · exact abs_nonneg _
    _ ≤ _ := weightCoeff_abs_sum hR

lemma smallPrimeCount_nonneg (Z n : ℕ) : 0 ≤ smallPrimeCount Z n := by
  apply sum_nonneg
  intro p hp
  split_ifs <;> norm_num

lemma one_le_smallPrimeCount {Z n : ℕ} (hn : ¬n.Coprime Z.factorial) :
    1 ≤ smallPrimeCount Z n := by
  have hg : n.gcd Z.factorial ≠ 1 := by simpa only [Nat.coprime_iff_gcd_eq_one] using hn
  obtain ⟨p, hp, hpd⟩ := Nat.ne_one_iff_exists_prime_dvd.mp hg
  obtain ⟨hpn, hpf⟩ := Nat.dvd_gcd_iff.mp hpd
  have hpZ : p ≤ Z := hp.dvd_factorial.mp hpf
  have hps : p ∈ smallPrimes Z := mem_filter.mpr ⟨mem_Ioc.mpr ⟨hp.pos, hpZ⟩, hp⟩
  have hh := single_le_sum (f := fun q => if q ∣ n then (1:ℝ) else 0)
    (s := smallPrimes Z) (fun q hq => by dsimp only; split_ifs <;> norm_num) hps
  simpa only [if_pos hpn] using hh

lemma lowerTest_upper {R : ℕ} (hR : 1 ≤ R) (Z n : ℕ) :
    lowerTest R Z n ≤ if n.Coprime Z.factorial then (R:ℝ)^4 else 0 := by
  unfold lowerTest
  split_ifs with hc
  · calc
      _ ≤ majorant R n := mul_le_of_le_one_left (majorant_nonneg R n)
        (by linarith only [smallPrimeCount_nonneg Z n])
      _ ≤ _ := majorant_upper hR n
  · exact mul_nonpos_of_nonpos_of_nonneg
      (by linarith only [one_le_smallPrimeCount hc]) (majorant_nonneg R n)

noncomputable def row (S : Finset ℕ) (a : ℕ → ℝ) (g : ℕ → ℕ) (d : ℕ) : ℝ :=
  ∑ n ∈ S, if d ∣ g n then a n else 0

noncomputable def moment (S : Finset ℕ) (a : ℕ → ℝ) (g : ℕ → ℕ) (R p : ℕ) : ℝ :=
  ∑ n ∈ S, if p ∣ g n then a n*majorant R (g n) else 0

lemma moment_expansion (S : Finset ℕ) (a : ℕ → ℝ) (g : ℕ → ℕ) (R p : ℕ) :
    moment S a g R p = ∑ z ∈ weightIndices R,
      weightCoeff R z*row S a g ((weightDivisor z).lcm p) := by
  simp only [moment, row, mul_sum, majorant_expansion]
  rw [sum_comm]
  apply sum_congr rfl
  intro n hn
  by_cases hp : p ∣ g n
  · rw [if_pos hp]
    apply sum_congr rfl
    intro z hz
    simp only [Nat.lcm_dvd_iff, hp, and_true]
    split_ifs <;> simp [mul_comm]
  · rw [if_neg hp]
    symm
    apply sum_eq_zero
    intro z hz
    simp [Nat.lcm_dvd_iff, hp]

lemma localMain_indices (R p : ℕ) : localMain R p =
    ∑ z ∈ weightIndices R, weightCoeff R z/((weightDivisor z).lcm p) := by
  simp only [weightIndices, sum_product, weightCoeff, weightDivisor, localMain]

lemma moment_error (S : Finset ℕ) (a : ℕ → ℝ) (g : ℕ → ℕ)
    {R p : ℕ} (hR : 1 ≤ R) {X E : ℝ} (hE : 0 ≤ E)
    (hrows : ∀ z ∈ weightIndices R,
      |row S a g ((weightDivisor z).lcm p)-X/((weightDivisor z).lcm p)| ≤ E) :
    |moment S a g R p-X*localMain R p| ≤ E*(R:ℝ)^4 := by
  rw [moment_expansion, localMain_indices, mul_sum, ← sum_sub_distrib]
  apply (abs_sum_le_sum_abs _ _).trans
  calc
    _ = ∑ z ∈ weightIndices R, |weightCoeff R z| *
      |row S a g ((weightDivisor z).lcm p)-X/((weightDivisor z).lcm p)| := by
      apply sum_congr rfl
      intro z hz
      rw [← abs_mul]
      congr 1
      ring
    _ ≤ ∑ z ∈ weightIndices R, |weightCoeff R z| * E :=
      sum_le_sum (fun z hz => mul_le_mul_of_nonneg_left (hrows z hz) (abs_nonneg _))
    _ = E*(∑ z ∈ weightIndices R, |weightCoeff R z|) := by rw [← sum_mul, mul_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_left (weightCoeff_abs_sum hR) hE

lemma localMain_one {R : ℕ} (hR : 1 ≤ R) : localMain R 1 = 1/sieveMass R := by
  simpa only [localMain, Nat.lcm_one_right, quadraticMain] using quadraticMain_selbergWeight hR

lemma lowerTest_sum (S : Finset ℕ) (a : ℕ → ℝ) (g : ℕ → ℕ) (R Z : ℕ) :
    (∑ n ∈ S, a n*lowerTest R Z (g n)) =
      moment S a g R 1-∑ p ∈ smallPrimes Z, moment S a g R p := by
  simp only [lowerTest, smallPrimeCount, moment, one_dvd, if_true, sub_mul, one_mul,
    mul_sub, mul_sum, sum_mul, sum_sub_distrib]
  congr 1
  rw [sum_comm]
  apply sum_congr rfl
  intro p hp
  apply sum_congr rfl
  intro n hn
  split_ifs <;> simp

lemma smallPrimes_card_le (Z : ℕ) : (smallPrimes Z).card ≤ Z := by
  simpa only [Nat.card_Ioc, Nat.sub_zero] using card_le_card (filter_subset Nat.Prime (Ioc 0 Z))

/-- All moduli in the lower-supported test are at most R^2 Z. The lower
bound retains the complete coefficient-mass error. -/
theorem rough_weight_lower (S : Finset ℕ) (a : ℕ → ℝ) (g : ℕ → ℕ)
    (ha : ∀ n ∈ S, 0 ≤ a n) {R Z : ℕ} (hR : 1 ≤ R) (hZ : 1 ≤ Z)
    {X E : ℝ} (hE : 0 ≤ E)
    (hrows : ∀ d : ℕ, 0 < d → d ≤ R^2*Z → |row S a g d-X/d| ≤ E) :
    X*lowerMain R Z-E*((Z:ℝ)+1)*(R:ℝ)^4 ≤
      (R:ℝ)^4*(∑ n ∈ S, if (g n).Coprime Z.factorial then a n else 0) := by
  have herror {p : ℕ} (hp : 0 < p) (hpZ : p ≤ Z) :
      |moment S a g R p-X*localMain R p| ≤ E*(R:ℝ)^4 := by
    apply moment_error S a g hR hE
    intro z hz
    obtain ⟨hd0, hdR⟩ := weightDivisor_bounds hz
    apply hrows _ (Nat.pos_of_ne_zero (Nat.lcm_ne_zero hd0.ne' hp.ne'))
    exact (Nat.lcm_le_mul hd0 hp).trans (Nat.mul_le_mul hdR hpZ)
  have h₁ := (abs_le.mp (herror (p := 1) (by norm_num) hZ)).1
  have hp (p : ℕ) (hp : p ∈ smallPrimes Z) :=
    (abs_le.mp (herror (mem_Ioc.mp (mem_filter.mp hp).1).1 (mem_Ioc.mp (mem_filter.mp hp).1).2)).2
  have hsum : (∑ p ∈ smallPrimes Z, (moment S a g R p-X*localMain R p)) ≤
      (Z:ℝ)*E*(R:ℝ)^4 := by
    apply (sum_le_sum hp).trans
    rw [sum_const, nsmul_eq_mul]
    have hh := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (smallPrimes_card_le Z))
      (show 0 ≤ E*(R:ℝ)^4 by positivity)
    nlinarith only [hh]
  have hlow : X*lowerMain R Z-E*((Z:ℝ)+1)*(R:ℝ)^4 ≤
      ∑ n ∈ S, a n*lowerTest R Z (g n) := by
    rw [lowerTest_sum]
    rw [localMain_one hR] at h₁
    simp only [sum_sub_distrib, ← mul_sum] at hsum
    unfold lowerMain
    nlinarith only [h₁, hsum]
  apply hlow.trans
  rw [mul_sum]
  apply sum_le_sum
  intro n hn
  have hh := mul_le_mul_of_nonneg_left (lowerTest_upper hR Z (g n)) (ha n hn)
  split_ifs at hh ⊢ <;> simpa only [mul_zero, mul_comm] using hh

lemma sieveMass_le (R : ℕ) : sieveMass R ≤ R := by
  calc
    _ ≤ ∑ n ∈ Ioc 0 R, (1:ℝ) := by
      apply sum_le_sum
      intro n hn
      have hmu : (μ n : ℝ)^2 ≤ 1 := by
        rw [← abs_real_moebius_eq_sq]
        exact_mod_cast abs_moebius_le_one (n := n)
      have ht : (1:ℝ) ≤ n.totient := by exact_mod_cast Nat.totient_pos.mpr (mem_Ioc.mp hn).1
      apply (div_le_one (by linarith only [ht])).mpr
      exact hmu.trans ht
    _ = _ := by simp

/-- An explicit positive lower bound once the numerical row-error budget
and main-term condition are satisfied. -/
theorem rough_weight_positive_bound (S : Finset ℕ) (a : ℕ → ℝ) (g : ℕ → ℕ)
    (ha : ∀ n ∈ S, 0 ≤ a n) {R Z v N : ℕ} (hR : 1 ≤ R) (hZ : 1 ≤ Z)
    (hv : R^5*Z ≤ v) {X E : ℝ} (hE : 0 ≤ E) (hX : (N:ℝ)/2 ≤ X)
    (hmain : 1/(2*sieveMass R) ≤ lowerMain R Z)
    (hbudget : E ≤ (N:ℝ)/(16*v))
    (hrows : ∀ d : ℕ, 0 < d → d ≤ R^2*Z → |row S a g d-X/d| ≤ E) :
    (N:ℝ)/(8*(R:ℝ)^5) ≤ ∑ n ∈ S, if (g n).Coprime Z.factorial then a n else 0 := by
  have hR0 : (0:ℝ) < R := Nat.cast_pos.mpr hR
  have hG : 0 < sieveMass R := lt_of_lt_of_le (by norm_num) (one_le_sieveMass hR)
  have hv0 : (0:ℝ) < v := Nat.cast_pos.mpr ((show 0 < R^5*Z by positivity).trans_le hv)
  have hX0 : 0 ≤ X := (by positivity : (0:ℝ) ≤ (N:ℝ)/2).trans hX
  have hmass := rough_weight_lower S a g ha hR hZ hE hrows
  have hmain' : (N:ℝ)/(4*R) ≤ X*lowerMain R Z := by
    calc
      _ ≤ (N:ℝ)/(4*sieveMass R) := div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity)
        (mul_le_mul_of_nonneg_left (sieveMass_le R) (by norm_num))
      _ = ((N:ℝ)/2)*(1/(2*sieveMass R)) := by ring
      _ ≤ X*lowerMain R Z := mul_le_mul hX hmain (by positivity) hX0
  have hbudget' : E*((Z:ℝ)+1)*(R:ℝ)^4 ≤ (N:ℝ)/(8*R) := by
    have hvR : (R:ℝ)^5*Z ≤ v := by exact_mod_cast hv
    have hZR : (1:ℝ) ≤ Z := by exact_mod_cast hZ
    have htotal := (le_div_iff₀ (show 0 < 16*(v:ℝ) by positivity)).mp hbudget
    have hb := mul_le_mul_of_nonneg_left hvR hE
    apply (le_div_iff₀ (show 0 < 8*(R:ℝ) by positivity)).mpr
    have hZb := mul_le_mul_of_nonneg_left (show (Z:ℝ)+1 ≤ 2*Z by linarith only [hZR])
      (show 0 ≤ 8*E*(R:ℝ)^5 by positivity)
    nlinarith only [htotal, hb, hZb]
  have hh : (N:ℝ)/(8*R) ≤ (R:ℝ)^4*(∑ n ∈ S, if (g n).Coprime Z.factorial then a n else 0) := by
    have he : (N:ℝ)/(4*R) = 2*((N:ℝ)/(8*R)) := by ring
    linarith only [hmass, hmain', hbudget', he]
  apply (div_le_iff₀ (show 0 < 8*(R:ℝ)^5 by positivity)).mpr
  have ht := (div_le_iff₀ (show 0 < 8*(R:ℝ) by positivity)).mp hh
  nlinarith only [ht]

#print axioms rough_weight_positive_bound

end Erdos972SelbergLowerTest
