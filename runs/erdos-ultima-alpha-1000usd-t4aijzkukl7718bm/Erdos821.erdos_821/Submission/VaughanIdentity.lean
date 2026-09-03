import FormalConjecturesUtil

/-!
# Vaughan's identity and its elementary coefficient bounds

The identity is an exact equality of arithmetic functions under Dirichlet
convolution. It imposes no unproved hypothesis about primes.
-/

open scoped BigOperators ArithmeticFunction.zeta ArithmeticFunction.Moebius
open ArithmeticFunction Finset

namespace Erdos821.AnalyticSieve

/-- The part of an arithmetic function supported at `n ≤ U`. -/
def shortPart {R : Type*} [Zero R] (f : ArithmeticFunction R) (U : ℕ) : ArithmeticFunction R :=
  ⟨fun n => if n ≤ U then f n else 0, by simp⟩

/-- The part of an arithmetic function supported at `U < n`. -/
def longPart {R : Type*} [Zero R] (f : ArithmeticFunction R) (U : ℕ) : ArithmeticFunction R :=
  ⟨fun n => if U < n then f n else 0, by simp⟩

@[simp] lemma shortPart_apply {R : Type*} [Zero R] (f : ArithmeticFunction R) (U n : ℕ) :
    shortPart f U n = if n ≤ U then f n else 0 := rfl

@[simp] lemma longPart_apply {R : Type*} [Zero R] (f : ArithmeticFunction R) (U n : ℕ) :
    longPart f U n = if U < n then f n else 0 := rfl

lemma shortPart_add_longPart {R : Type*} [AddMonoid R] (f : ArithmeticFunction R) (U : ℕ) :
    shortPart f U + longPart f U = f := by
  ext n
  simp only [ArithmeticFunction.add_apply, shortPart_apply, longPart_apply]
  by_cases h : n ≤ U
  · simp [h, not_lt.mpr h]
  · simp [h, Nat.lt_of_not_ge h]

lemma longPart_eq_sub {R : Type*} [AddCommGroup R] (f : ArithmeticFunction R) (U : ℕ) :
    longPart f U = f - shortPart f U := by
  rw [eq_sub_iff_add_eq, add_comm, shortPart_add_longPart]

lemma vaughan_algebra {R : Type*} [CommRing R] (mu z lam a b : R) (hμ : mu * z = 1) :
    lam = a + b * (z * lam) - b * z * a + (mu - b) * z * (lam - a) := by
  symm
  calc
    _ = a + (mu * z) * (lam - a) := by ring
    _ = lam := by rw [hμ]; ring

/-- Vaughan's identity. `U` cuts off von Mangoldt and `V` cuts off Möbius. -/
theorem vaughan_identity (U V : ℕ) :
    vonMangoldt = shortPart vonMangoldt U + shortPart (μ : ArithmeticFunction ℝ) V * log -
      shortPart (μ : ArithmeticFunction ℝ) V * (ζ : ArithmeticFunction ℝ) * shortPart vonMangoldt U +
      longPart (μ : ArithmeticFunction ℝ) V * (ζ : ArithmeticFunction ℝ) * longPart vonMangoldt U := by
  simpa only [longPart_eq_sub, zeta_mul_vonMangoldt] using
    vaughan_algebra (μ : ArithmeticFunction ℝ) (ζ : ArithmeticFunction ℝ) vonMangoldt
      (shortPart vonMangoldt U) (shortPart (μ : ArithmeticFunction ℝ) V) coe_moebius_mul_coe_zeta

lemma shortPart_mul_eq_zero {R : Type*} [Semiring R] (f g : ArithmeticFunction R)
    {U V n : ℕ} (hn : U * V < n) : (shortPart f U * shortPart g V) n = 0 := by
  rw [ArithmeticFunction.mul_apply]
  apply Finset.sum_eq_zero
  intro d hd
  have hp := (Nat.mem_divisorsAntidiagonal.mp hd).1
  simp only [shortPart_apply]
  by_cases h₁ : d.1 ≤ U
  · have h₂ : ¬d.2 ≤ V := by
      intro h₂
      have hh := Nat.mul_le_mul h₁ h₂
      rw [hp] at hh
      omega
    simp [h₂]
  · simp [h₁]

noncomputable def vaughanTypeI (U V : ℕ) : ArithmeticFunction ℝ :=
  shortPart (μ : ArithmeticFunction ℝ) V * shortPart vonMangoldt U

noncomputable def vaughanTypeII (V : ℕ) : ArithmeticFunction ℝ :=
  longPart (μ : ArithmeticFunction ℝ) V * (ζ : ArithmeticFunction ℝ)

lemma vaughanTypeI_eq_zero {U V n : ℕ} (hn : U * V < n) : vaughanTypeI U V n = 0 := by
  unfold vaughanTypeI
  exact shortPart_mul_eq_zero _ _ (by simpa only [mul_comm U V] using hn)

lemma vaughanTypeII_eq_zero {V n : ℕ} (hn : n ≤ V) : vaughanTypeII V n = 0 := by
  rw [vaughanTypeII, coe_mul_zeta_apply]
  apply Finset.sum_eq_zero
  intro d hd
  have hdV := (Nat.divisor_le hd).trans hn
  simp only [longPart_apply, if_neg (not_lt.mpr hdV)]

lemma abs_shortPart_moebius_le_one (V n : ℕ) :
    |shortPart (μ : ArithmeticFunction ℝ) V n| ≤ 1 := by
  rw [shortPart_apply]
  split_ifs
  · simp only [ArithmeticFunction.intCoe_apply]
    exact_mod_cast (abs_moebius_le_one (n := n))
  · norm_num

lemma abs_longPart_moebius_le_one (V n : ℕ) :
    |longPart (μ : ArithmeticFunction ℝ) V n| ≤ 1 := by
  rw [longPart_apply]
  split_ifs
  · simp only [ArithmeticFunction.intCoe_apply]
    exact_mod_cast (abs_moebius_le_one (n := n))
  · norm_num

lemma shortPart_vonMangoldt_nonneg (U n : ℕ) : 0 ≤ shortPart vonMangoldt U n := by
  rw [shortPart_apply]
  split_ifs
  · exact vonMangoldt_nonneg
  · rfl

lemma shortPart_vonMangoldt_le (U n : ℕ) : shortPart vonMangoldt U n ≤ vonMangoldt n := by
  rw [shortPart_apply]
  split_ifs
  · rfl
  · exact vonMangoldt_nonneg

lemma abs_vaughanTypeI_le (U V n : ℕ) : |vaughanTypeI U V n| ≤ Real.log n := by
  rw [vaughanTypeI, ArithmeticFunction.mul_apply]
  calc
    _ ≤ ∑ d ∈ n.divisorsAntidiagonal,
        |shortPart (μ : ArithmeticFunction ℝ) V d.1 * shortPart vonMangoldt U d.2| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ n.divisorsAntidiagonal, vonMangoldt d.2 := by
      apply Finset.sum_le_sum
      intro d hd
      rw [abs_mul, abs_of_nonneg (shortPart_vonMangoldt_nonneg U d.2)]
      apply (mul_le_mul_of_nonneg_right (abs_shortPart_moebius_le_one V d.1)
        (shortPart_vonMangoldt_nonneg U d.2)).trans
      rw [one_mul]
      exact shortPart_vonMangoldt_le U d.2
    _ = Real.log n := by
      rw [← Nat.map_div_left_divisors, Finset.sum_map]
      simp only [Function.Embedding.coeFn_mk]
      exact vonMangoldt_sum

lemma abs_vaughanTypeII_le (V n : ℕ) : |vaughanTypeII V n| ≤ (n.divisors.card : ℝ) := by
  rw [vaughanTypeII, coe_mul_zeta_apply]
  calc
    _ ≤ ∑ d ∈ n.divisors, |longPart (μ : ArithmeticFunction ℝ) V d| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ n.divisors, (1 : ℝ) := Finset.sum_le_sum (fun d hd => abs_longPart_moebius_le_one V d)
    _ = _ := by simp

/-- Vaughan's identity in Type I / Type II form. -/
theorem vaughan_identity_typeI_typeII (U V : ℕ) :
    vonMangoldt = shortPart vonMangoldt U + shortPart (μ : ArithmeticFunction ℝ) V * log -
      vaughanTypeI U V * (ζ : ArithmeticFunction ℝ) + vaughanTypeII V * longPart vonMangoldt U := by
  convert vaughan_identity U V using 1
  unfold vaughanTypeI vaughanTypeII
  ring

end Erdos821.AnalyticSieve
