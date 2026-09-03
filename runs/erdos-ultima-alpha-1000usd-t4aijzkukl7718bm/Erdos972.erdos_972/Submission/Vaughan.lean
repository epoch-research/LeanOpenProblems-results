import FormalConjecturesUtil

/-!
An algebraic Vaughan decomposition for the analytic route to Erdős 972.
This file does not assert a prime-pair estimate or settle the conjecture.
-/

namespace Erdos972Vaughan

open ArithmeticFunction
open scoped ArithmeticFunction ArithmeticFunction.zeta ArithmeticFunction.Moebius

@[simp] lemma sub_apply (f g : ArithmeticFunction ℝ) (n : ℕ) :
    (f - g) n = f n - g n := rfl


/-- Restrict an arithmetic function to the integers at most `U`. -/
def cutoff (f : ArithmeticFunction ℝ) (U : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun n => if n ≤ U then f n else 0, by simp⟩

/-- The complementary, large-input part of an arithmetic function. -/
def tail (f : ArithmeticFunction ℝ) (U : ℕ) : ArithmeticFunction ℝ :=
  f - cutoff f U

@[simp] lemma cutoff_apply (f : ArithmeticFunction ℝ) (U n : ℕ) :
    cutoff f U n = if n ≤ U then f n else 0 := rfl

lemma cutoff_eq_of_le (f : ArithmeticFunction ℝ) {U n : ℕ} (h : n ≤ U) :
    cutoff f U n = f n := by simp [h]

lemma cutoff_eq_zero_of_lt (f : ArithmeticFunction ℝ) {U n : ℕ} (h : U < n) :
    cutoff f U n = 0 := by simp [not_le.mpr h]

lemma tail_eq_zero_of_le (f : ArithmeticFunction ℝ) {U n : ℕ} (h : n ≤ U) :
    tail f U n = 0 := by simp [tail, h]

lemma tail_eq_of_lt (f : ArithmeticFunction ℝ) {U n : ℕ} (h : U < n) :
    tail f U n = f n := by simp [tail, not_le.mpr h]

/-- The algebraic identity behind Vaughan's decomposition, before choosing cutoffs. -/
lemma vaughan_split (M L : ArithmeticFunction ℝ) :
    Λ = M * ArithmeticFunction.log - M * ζ * L + L +
      ((μ : ArithmeticFunction ℝ) - M) * ζ * (Λ - L) := by
  rw [← zeta_mul_vonMangoldt]
  calc
    Λ = ((μ : ArithmeticFunction ℝ) * ζ) * Λ -
        ((μ : ArithmeticFunction ℝ) * ζ) * L + L := by simp
    _ = M * (ζ * Λ) - M * ζ * L + L +
        ((μ : ArithmeticFunction ℝ) - M) * ζ * (Λ - L) := by ring

/-- Vaughan's four-term decomposition, with independent Möbius and Mangoldt cutoffs. -/
theorem vaughan_identity (U V : ℕ) :
    Λ = cutoff (μ : ArithmeticFunction ℝ) U * ArithmeticFunction.log -
      cutoff (μ : ArithmeticFunction ℝ) U * ζ * cutoff Λ V + cutoff Λ V +
      tail (μ : ArithmeticFunction ℝ) U * ζ * tail Λ V := by
  simpa only [tail] using vaughan_split (cutoff (μ : ArithmeticFunction ℝ) U)
    (cutoff Λ V)

/-- Above the Mangoldt cutoff the isolated small-input term vanishes. -/
theorem vaughan_apply_above (U V n : ℕ) (hn : V < n) :
    Λ n = (cutoff (μ : ArithmeticFunction ℝ) U * ArithmeticFunction.log) n -
      (cutoff (μ : ArithmeticFunction ℝ) U * ζ * cutoff Λ V) n +
      (tail (μ : ArithmeticFunction ℝ) U * ζ * tail Λ V) n := by
  have h := congrArg (fun f : ArithmeticFunction ℝ => f n) (vaughan_identity U V)
  simpa only [ArithmeticFunction.add_apply, sub_apply,
    cutoff_eq_zero_of_lt Λ hn, add_zero] using h

/-- A convolution of two large-input parts has no contribution below the product
of their cutoffs. -/
lemma tail_mul_tail_eq_zero_of_le (f g : ArithmeticFunction ℝ) (U V n : ℕ)
    (hn : n ≤ U * V) : (tail f U * tail g V) n = 0 := by
  rw [ArithmeticFunction.mul_apply]
  apply Finset.sum_eq_zero
  intro ab hab
  by_cases ha : ab.1 ≤ U
  · rw [tail_eq_zero_of_le f ha, zero_mul]
  by_cases hb : ab.2 ≤ V
  · rw [tail_eq_zero_of_le g hb, mul_zero]
  have he := (Nat.mem_divisorsAntidiagonal.mp hab).1
  have hm := Nat.mul_le_mul (Nat.succ_le_of_lt (lt_of_not_ge ha))
    (Nat.succ_le_of_lt (lt_of_not_ge hb))
  simp only [Nat.succ_eq_add_one] at hm
  exfalso
  nlinarith

/-- Inserting the constant-one arithmetic function preserves that support bound. -/
lemma typeII_eq_zero_of_le (f g : ArithmeticFunction ℝ) (U V n : ℕ)
    (hn : n ≤ U * V) : (tail f U * ζ * tail g V) n = 0 := by
  have he : tail f U * ζ * tail g V = (tail f U * tail g V) * ζ := by ring
  rw [he, ArithmeticFunction.coe_mul_zeta_apply]
  apply Finset.sum_eq_zero
  intro d hd
  obtain ⟨hdn, hn0⟩ := Nat.mem_divisors.mp hd
  exact tail_mul_tail_eq_zero_of_le f g U V d
    ((Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hdn).trans hn)

lemma abs_cutoff_moebius_le_one (U n : ℕ) :
    |cutoff (μ : ArithmeticFunction ℝ) U n| ≤ 1 := by
  rw [cutoff_apply]
  split_ifs
  · rw [intCoe_apply]
    exact_mod_cast (abs_moebius_le_one (n := n))
  · simp

lemma cutoff_vonMangoldt_nonneg (V n : ℕ) : 0 ≤ cutoff Λ V n := by
  rw [cutoff_apply]
  split_ifs
  · exact vonMangoldt_nonneg
  · rfl

lemma cutoff_vonMangoldt_le (V n : ℕ) : cutoff Λ V n ≤ Λ n := by
  rw [cutoff_apply]
  split_ifs
  · rfl
  · exact vonMangoldt_nonneg

/-- The coefficient in Vaughan's second Type-I term is bounded by `log n`,
without using a pointwise divisor-function estimate. -/
theorem abs_typeI_coefficient_le_log (U V n : ℕ) :
    |(cutoff (μ : ArithmeticFunction ℝ) U * cutoff Λ V) n| ≤ Real.log n := by
  rw [ArithmeticFunction.mul_apply]
  calc
    _ ≤ ∑ ab ∈ n.divisorsAntidiagonal,
        |cutoff (μ : ArithmeticFunction ℝ) U ab.1 * cutoff Λ V ab.2| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ ab ∈ n.divisorsAntidiagonal, Λ ab.2 := by
      apply Finset.sum_le_sum
      intro ab hab
      rw [abs_mul, abs_of_nonneg (cutoff_vonMangoldt_nonneg V ab.2)]
      calc
        _ ≤ 1 * cutoff Λ V ab.2 :=
          mul_le_mul_of_nonneg_right (abs_cutoff_moebius_le_one U ab.1)
            (cutoff_vonMangoldt_nonneg V ab.2)
        _ ≤ Λ ab.2 := by simpa using cutoff_vonMangoldt_le V ab.2
    _ = _ := by rw [Nat.sum_divisorsAntidiagonal' (fun _ b => Λ b), vonMangoldt_sum]

lemma cutoff_mul_cutoff_eq_zero_of_lt (f g : ArithmeticFunction ℝ)
    (U V n : ℕ) (hn : U * V < n) : (cutoff f U * cutoff g V) n = 0 := by
  rw [ArithmeticFunction.mul_apply]
  apply Finset.sum_eq_zero
  intro ab hab
  by_cases ha : ab.1 ≤ U
  · have hb : V < ab.2 := by
      have he := (Nat.mem_divisorsAntidiagonal.mp hab).1
      by_contra hb
      have := Nat.mul_le_mul ha (Nat.le_of_not_gt hb)
      omega
    rw [cutoff_eq_zero_of_lt g hb, mul_zero]
  · rw [cutoff_eq_zero_of_lt f (Nat.lt_of_not_ge ha), zero_mul]

lemma abs_tail_moebius_le_one (U n : ℕ) :
    |tail (μ : ArithmeticFunction ℝ) U n| ≤ 1 := by
  by_cases hn : n ≤ U
  · rw [tail_eq_zero_of_le _ hn]
    norm_num
  · rw [tail_eq_of_lt _ (Nat.lt_of_not_ge hn), intCoe_apply]
    exact_mod_cast (abs_moebius_le_one (n := n))

/-- A convenient pointwise majorant for the large Möbius convolution. -/
lemma abs_typeII_coefficient_le_card_divisors (U n : ℕ) :
    |(tail (μ : ArithmeticFunction ℝ) U * ζ) n| ≤ (n.divisors.card : ℝ) := by
  rw [ArithmeticFunction.coe_mul_zeta_apply]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ d ∈ n.divisors, (1 : ℝ) :=
      Finset.sum_le_sum (fun d hd => abs_tail_moebius_le_one U d)
    _ = _ := by simp

lemma tail_vonMangoldt_nonneg (V n : ℕ) : 0 ≤ tail Λ V n := by
  by_cases hn : n ≤ V
  · rw [tail_eq_zero_of_le _ hn]
  · rw [tail_eq_of_lt _ (Nat.lt_of_not_ge hn)]
    exact vonMangoldt_nonneg

lemma tail_vonMangoldt_le (V n : ℕ) : tail Λ V n ≤ Λ n := by
  by_cases hn : n ≤ V
  · rw [tail_eq_zero_of_le _ hn]
    exact vonMangoldt_nonneg
  · rw [tail_eq_of_lt _ (Nat.lt_of_not_ge hn)]

lemma tail_mul_zeta_eq_zero_of_le (f : ArithmeticFunction ℝ)
    (U n : ℕ) (hn : n ≤ U) : (tail f U * ζ) n = 0 := by
  rw [ArithmeticFunction.coe_mul_zeta_apply]
  apply Finset.sum_eq_zero
  intro d hd
  exact tail_eq_zero_of_le f ((Nat.le_of_dvd
    (Nat.pos_of_ne_zero (Nat.mem_divisors.mp hd).2)
    (Nat.mem_divisors.mp hd).1).trans hn)

#print axioms abs_typeI_coefficient_le_log
#print axioms cutoff_mul_cutoff_eq_zero_of_lt
#print axioms abs_typeII_coefficient_le_card_divisors

#print axioms typeII_eq_zero_of_le


#print axioms vaughan_identity
#print axioms vaughan_apply_above

end Erdos972Vaughan
