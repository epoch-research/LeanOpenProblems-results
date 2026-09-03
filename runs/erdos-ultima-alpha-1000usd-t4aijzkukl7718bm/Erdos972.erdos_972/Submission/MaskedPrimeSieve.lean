import Submission.LeastFactorSieve

/-! A single designated prime may be repeated: all other small prime divisors
are excluded. This upper sieve is not a lower bound for prime pairs. -/
namespace Erdos972MaskedPrimeSieve

open Finset ArithmeticFunction
open Erdos972SelbergWeights Erdos972PairSieve Erdos972SelbergLocalCost
open Erdos972SelbergUnitWeights Erdos972SelbergLowerTest Erdos972LeastFactorSieve

set_option autoImplicit false
set_option maxHeartbeats 1500000

noncomputable def maskedWeight (R p d : ℕ) : ℝ :=
  if p ∣ d then 0 else selbergWeight R d

noncomputable def maskedMajorant (R p n : ℕ) : ℝ :=
  (∑ d ∈ Ioc 0 R, if d ∣ n then maskedWeight R p d else 0)^2

/-- This condition does not exclude any power of the designated prime. -/
def NoOtherSmallPrime (R p n : ℕ) : Prop :=
  ∀ q : ℕ, q.Prime → q ≤ R → q ∣ n → q = p

noncomputable def singlePrimeWeight (S : Finset ℕ) (a : ℕ → ℝ)
    (g : ℕ → ℕ) (R p : ℕ) : ℝ := by
  classical
  exact ∑ n ∈ S, if p ∣ g n ∧ NoOtherSmallPrime R p (g n) then a n else 0

lemma coprimeMass_mono (p : ℕ) : Monotone (fun R => coprimeMass R p) := by
  intro R T hRT
  apply sum_le_sum_of_subset_of_nonneg (Ioc_subset_Ioc_right hRT)
  intro r _ _
  split_ifs
  · exact le_rfl
  · exact sieveAtom_nonneg r

lemma localMain_nonneg {R p : ℕ} (hR : 1 ≤ R) (hp : p.Prime) :
    0 ≤ localMain R p := by
  rw [localMain_exact hR hp]
  exact div_nonneg (sub_nonneg.mpr (coprimeMass_mono p (Nat.div_le_self R p)))
    (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))

lemma maskedMain_nonneg (R p : ℕ) : 0 ≤ quadraticMain R (maskedWeight R p) := by
  rw [quadraticMain_diagonal]
  exact sum_nonneg (fun r _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))

/-- Deleting the weights divisible by p costs at most a factor of two. -/
lemma maskedMain_upper {R p : ℕ} (hR : 1 ≤ R) (hp : p.Prime) :
    quadraticMain R (maskedWeight R p) ≤ 2/sieveMass R := by
  have hcomp := localMain_complement hp R
  rw [quadraticMain_selbergWeight hR] at hcomp
  change localMain R p = 1/sieveMass R -
    (1-1/(p:ℝ))*quadraticMain R (maskedWeight R p) at hcomp
  have hp2 : (2:ℝ) ≤ p := Nat.cast_le.mpr hp.two_le
  have hpinv : 1/(p:ℝ) ≤ 1/2 := by
    exact one_div_le_one_div_of_le (by norm_num) hp2
  have hmul := mul_le_mul_of_nonneg_right (show (1:ℝ)/2 ≤ 1-1/(p:ℝ) by linarith)
    (maskedMain_nonneg R p)
  have hn := localMain_nonneg hR hp
  rw [show 2/sieveMass R = 2*(1/sieveMass R) by ring]
  linarith only [hcomp, hmul, hn]

lemma maskedWeight_abs_le_one {R : ℕ} (hR : 1 ≤ R) (p d : ℕ) :
    |maskedWeight R p d| ≤ 1 := by
  unfold maskedWeight
  split_ifs
  · norm_num
  · exact abs_selbergWeight_le_one hR d

lemma maskedMajorant_eq_one {R p n : ℕ} (hR : 1 ≤ R) (hp : p.Prime)
    (hn : NoOtherSmallPrime R p n) : maskedMajorant R p n = 1 := by
  have hs : (∑ d ∈ Ioc 0 R, if d ∣ n then maskedWeight R p d else 0) = 1 := by
    rw [sum_eq_single 1]
    · simp [maskedWeight, hp.not_dvd_one, selbergWeight_one hR]
    · intro d hd hd1
      by_cases hdn : d ∣ n
      · rw [if_pos hdn]
        by_cases hpd : p ∣ d
        · simp [maskedWeight, hpd]
        · have hq := Nat.minFac_prime hd1
          have he : d.minFac = p := hn d.minFac hq
            ((Nat.minFac_le (Nat.pos_of_ne_zero (by have := mem_Ioc.mp hd; omega))).trans
              (mem_Ioc.mp hd).2) ((Nat.minFac_dvd d).trans hdn)
          exact (hpd (he ▸ Nat.minFac_dvd d)).elim
      · exact if_neg hdn
    · intro h
      exact (h (mem_Ioc.mpr ⟨by omega, hR⟩)).elim
  simp only [maskedMajorant, hs, one_pow]

noncomputable def maskedMoment (S : Finset ℕ) (a : ℕ → ℝ)
    (g : ℕ → ℕ) (R p : ℕ) : ℝ :=
  ∑ n ∈ S, if p ∣ g n then a n * maskedMajorant R p (g n) else 0

lemma maskedMoment_expansion (S : Finset ℕ) (a : ℕ → ℝ)
    (g : ℕ → ℕ) (R p : ℕ) :
    maskedMoment S a g R p = ∑ d ∈ Ioc 0 R, ∑ e ∈ Ioc 0 R,
      maskedWeight R p d * maskedWeight R p e * row S a g ((d.lcm e).lcm p) := by
  classical
  have hterm (n : ℕ) :
      (if p ∣ g n then a n * maskedMajorant R p (g n) else 0) =
        ∑ d ∈ Ioc 0 R, ∑ e ∈ Ioc 0 R,
          maskedWeight R p d * maskedWeight R p e *
            (if (d.lcm e).lcm p ∣ g n then a n else 0) := by
    by_cases hpn : p ∣ g n
    · rw [if_pos hpn, maskedMajorant, pow_two, sum_mul_sum, mul_sum]
      apply sum_congr rfl
      intro d hd
      rw [mul_sum]
      apply sum_congr rfl
      intro e he
      by_cases hdn : d ∣ g n <;> by_cases hen : e ∣ g n <;>
        simp [Nat.lcm_dvd_iff, hpn, hdn, hen] <;> ring
    · simp [hpn, Nat.lcm_dvd_iff]
  unfold maskedMoment
  simp_rw [hterm]
  rw [sum_comm]
  apply sum_congr rfl
  intro d hd
  rw [sum_comm]
  apply sum_congr rfl
  intro e he
  simp only [row, mul_sum]

lemma maskedMoment_main {p : ℕ} (hp : p.Prime) (R : ℕ) (X : ℝ) :
    (∑ d ∈ Ioc 0 R, ∑ e ∈ Ioc 0 R,
      maskedWeight R p d * maskedWeight R p e * (X/((d.lcm e).lcm p))) =
      (X/(p:ℝ))*quadraticMain R (maskedWeight R p) := by
  simp only [quadraticMain, mul_sum]
  apply sum_congr rfl
  intro d hd
  apply sum_congr rfl
  intro e he
  by_cases hpd : p ∣ d
  · simp [maskedWeight, hpd]
  by_cases hpe : p ∣ e
  · simp [maskedWeight, hpe]
  have hc : (d.lcm e).Coprime p := (hp.coprime_iff_not_dvd.mpr (by
    simpa only [hp.dvd_lcm, not_or] using And.intro hpd hpe)).symm
  rw [hc.lcm_eq_mul, Nat.cast_mul]
  ring

/-- Every modulus used is at most p*R^2, and the absolute coefficient error
is at most E*R^2. -/
theorem maskedMoment_error (S : Finset ℕ) (a : ℕ → ℝ)
    (g : ℕ → ℕ) {R p : ℕ} (hR : 1 ≤ R) (hp : p.Prime)
    {X E : ℝ} (hE : 0 ≤ E)
    (hrows : ∀ d : ℕ, 0 < d → d ≤ p*R^2 → |row S a g d-X/d| ≤ E) :
    |maskedMoment S a g R p-(X/(p:ℝ))*quadraticMain R (maskedWeight R p)| ≤
      E*(R:ℝ)^2 := by
  rw [maskedMoment_expansion, ← maskedMoment_main hp R X, ← sum_sub_distrib]
  have hterm (d : ℕ) (hd : d ∈ Ioc 0 R) (e : ℕ) (he : e ∈ Ioc 0 R) :
      |maskedWeight R p d * maskedWeight R p e * row S a g ((d.lcm e).lcm p) -
        maskedWeight R p d * maskedWeight R p e * (X/((d.lcm e).lcm p))| ≤ E := by
    have hde : 0 < d.lcm e := Nat.pos_of_ne_zero
      (Nat.lcm_ne_zero (mem_Ioc.mp hd).1.ne' (mem_Ioc.mp he).1.ne')
    have hb : (d.lcm e).lcm p ≤ p*R^2 := by
      apply (Nat.lcm_le_mul hde hp.pos).trans
      have hh := (weightDivisor_bounds (R := R) (z := (d,e)) (mem_product.mpr ⟨hd, he⟩)).2
      change d.lcm e ≤ R^2 at hh
      nlinarith
    have hr := hrows _ (Nat.pos_of_ne_zero (Nat.lcm_ne_zero hde.ne' hp.ne_zero)) hb
    rw [← mul_sub, abs_mul, abs_mul]
    exact (mul_le_mul_of_nonneg_left hr (mul_nonneg (abs_nonneg _) (abs_nonneg _))).trans
      (mul_le_of_le_one_left hE (mul_le_one₀ (maskedWeight_abs_le_one hR p d)
        (abs_nonneg _) (maskedWeight_abs_le_one hR p e)))
  calc
    _ ≤ ∑ d ∈ Ioc 0 R,
        |(∑ e ∈ Ioc 0 R, maskedWeight R p d * maskedWeight R p e *
          row S a g ((d.lcm e).lcm p)) -
         (∑ e ∈ Ioc 0 R, maskedWeight R p d * maskedWeight R p e *
          (X/((d.lcm e).lcm p)))| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ Ioc 0 R, ∑ e ∈ Ioc 0 R, E := by
      apply sum_le_sum
      intro d hd
      rw [← sum_sub_distrib]
      exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum (fun e he => hterm d hd e he))
    _ = _ := by simp; ring

lemma singlePrimeWeight_le_moment (S : Finset ℕ) (a : ℕ → ℝ)
    (g : ℕ → ℕ) (ha : ∀ n ∈ S, 0 ≤ a n) {R p : ℕ}
    (hR : 1 ≤ R) (hp : p.Prime) :
    singlePrimeWeight S a g R p ≤ maskedMoment S a g R p := by
  classical
  unfold singlePrimeWeight maskedMoment
  apply sum_le_sum
  intro n hn
  by_cases hpn : p ∣ g n
  · rw [if_pos hpn]
    by_cases hc : NoOtherSmallPrime R p (g n)
    · rw [if_pos ⟨hpn, hc⟩, maskedMajorant_eq_one hR hp hc, mul_one]
    · rw [if_neg (fun h => hc h.2)]
      exact mul_nonneg (ha n hn) (sq_nonneg _)
  · simp only [hpn, false_and, if_false, le_refl]

/-- An upper bound for a single prime factor and arbitrary powers of it,
with no other prime divisor up to R. -/
theorem singlePrimeWeight_upper (S : Finset ℕ) (a : ℕ → ℝ)
    (g : ℕ → ℕ) (ha : ∀ n ∈ S, 0 ≤ a n) {R p : ℕ}
    (hR : 1 ≤ R) (hp : p.Prime) {X E : ℝ} (hX : 0 ≤ X) (hE : 0 ≤ E)
    (hrows : ∀ d : ℕ, 0 < d → d ≤ p*R^2 → |row S a g d-X/d| ≤ E) :
    singlePrimeWeight S a g R p ≤ 2*X/((p:ℝ)*sieveMass R)+E*(R:ℝ)^2 := by
  have he := (abs_le.mp (maskedMoment_error S a g hR hp hE hrows)).2
  have hm := mul_le_mul_of_nonneg_left (maskedMain_upper hR hp)
    (div_nonneg hX (Nat.cast_nonneg p))
  have hw := singlePrimeWeight_le_moment S a g ha hR hp
  have hid : (X/(p:ℝ))*(2/sieveMass R) = 2*X/((p:ℝ)*sieveMass R) := by ring
  rw [hid] at hm
  linarith only [he, hm, hw]

/-- Multiplication by log R removes the normalizing sieve mass. -/
theorem log_mul_singlePrimeWeight_upper (S : Finset ℕ) (a : ℕ → ℝ)
    (g : ℕ → ℕ) (ha : ∀ n ∈ S, 0 ≤ a n) {R p : ℕ}
    (hR : 2 ≤ R) (hp : p.Prime) {X E : ℝ} (hX : 0 ≤ X) (hE : 0 ≤ E)
    (hrows : ∀ d : ℕ, 0 < d → d ≤ p*R^2 → |row S a g d-X/d| ≤ E) :
    Real.log R * singlePrimeWeight S a g R p ≤
      4*X/(p:ℝ)+E*(R:ℝ)^2*Real.log R := by
  have hG : 0 < sieveMass R := lt_of_lt_of_le (by norm_num)
    (one_le_sieveMass (show 1 ≤ R by omega))
  have he := mul_le_mul_of_nonneg_left
    (singlePrimeWeight_upper S a g ha (by omega) hp hX hE hrows)
    (Real.log_natCast_nonneg R)
  have hl := mul_le_mul_of_nonneg_left (log_sieveMass_bound hR)
    (show 0 ≤ 2*X/(p:ℝ) by positivity)
  have hmain : Real.log R*(2*X/((p:ℝ)*sieveMass R)) ≤ 4*X/(p:ℝ) := by
    rw [show Real.log R*(2*X/((p:ℝ)*sieveMass R)) =
      (2*X/(p:ℝ)*Real.log R)/sieveMass R by ring]
    apply (div_le_iff₀ hG).mpr
    convert hl using 1 <;> ring
  nlinarith only [he, hmain]

#print axioms maskedMajorant_eq_one
#print axioms maskedMoment_error
#print axioms singlePrimeWeight_upper
#print axioms log_mul_singlePrimeWeight_upper

end Erdos972MaskedPrimeSieve
