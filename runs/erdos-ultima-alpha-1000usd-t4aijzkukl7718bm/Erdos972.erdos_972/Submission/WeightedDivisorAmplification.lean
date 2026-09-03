import FormalConjecturesUtil

/-! A finite divisor-count amplification inequality under a nonnegative weight.
The weight enters linearly in the variance, rather than through its square.
No prime-pair correlation estimate is asserted here. -/
namespace Erdos972WeightedDivisorAmplification

open Finset

noncomputable def divisorIndicator (d n : ℕ) : ℝ := if d ∣ n then 1 else 0
noncomputable def divisorRow (S : Finset ℕ) (a : ℕ → ℝ) (d : ℕ) : ℝ :=
  ∑ n ∈ S, if d ∣ n then a n else 0
noncomputable def divisorCount (P : Finset ℕ) (n : ℕ) : ℝ :=
  ∑ p ∈ P, divisorIndicator p n
noncomputable def harmonicMass (P : Finset ℕ) : ℝ := ∑ p ∈ P, 1 / (p : ℝ)
noncomputable def centeredPair (S : Finset ℕ) (a : ℕ → ℝ) (p q : ℕ) : ℝ :=
  ∑ n ∈ S, a n * (divisorIndicator p n - 1 / (p : ℝ)) *
    (divisorIndicator q n - 1 / (q : ℝ))

lemma centeredPair_rows (S : Finset ℕ) (a : ℕ → ℝ) (p q : ℕ) :
    centeredPair S a p q = divisorRow S a (p.lcm q) - divisorRow S a p / q -
      divisorRow S a q / p + divisorRow S a 1 / ((p : ℝ) * q) := by
  have h (n : ℕ) : a n * (divisorIndicator p n - 1 / (p : ℝ)) *
      (divisorIndicator q n - 1 / (q : ℝ)) =
      (if p.lcm q ∣ n then a n else 0) - (if p ∣ n then a n else 0) / q -
        (if q ∣ n then a n else 0) / p + a n / ((p : ℝ) * q) := by
    by_cases hp : p ∣ n <;> by_cases hq : q ∣ n <;>
      simp [divisorIndicator, Nat.lcm_dvd_iff, hp, hq, div_eq_mul_inv] <;> ring
  unfold centeredPair divisorRow
  simp_rw [h]
  simp only [sum_add_distrib, sum_sub_distrib, ← sum_div, one_dvd, if_true]

lemma centeredPair_error (S : Finset ℕ) (a : ℕ → ℝ) {p q : ℕ}
    (hp : 1 ≤ p) (hq : 1 ≤ q) {X E : ℝ} (hE : 0 ≤ E)
    (h1 : |divisorRow S a 1 - X| ≤ E)
    (hpRow : |divisorRow S a p - X / p| ≤ E)
    (hqRow : |divisorRow S a q - X / q| ≤ E)
    (hpqRow : |divisorRow S a (p.lcm q) - X / (p.lcm q)| ≤ E) :
    |centeredPair S a p q -
      X * (1 / (p.lcm q : ℕ) - 1 / ((p : ℝ) * q))| ≤ 4 * E := by
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hp0 : (0 : ℝ) < p := by linarith
  have hq0 : (0 : ℝ) < q := by linarith
  have hprod : (1 : ℝ) ≤ (p : ℝ) * q := by nlinarith [mul_nonneg (sub_nonneg.mpr hpR) (sub_nonneg.mpr hqR)]
  have heq : centeredPair S a p q -
      X * (1 / (p.lcm q : ℕ) - 1 / ((p : ℝ) * q)) =
      (divisorRow S a (p.lcm q) - X / (p.lcm q)) -
      (divisorRow S a p - X / p) / q -
      (divisorRow S a q - X / q) / p +
      (divisorRow S a 1 - X) / ((p : ℝ) * q) := by
    rw [centeredPair_rows]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  have hep : |(divisorRow S a p - X / p) / q| ≤ E := by
    rw [abs_div, abs_of_pos hq0]
    exact (div_le_div_of_nonneg_right hpRow hq0.le).trans (div_le_self hE hqR)
  have heq' : |(divisorRow S a q - X / q) / p| ≤ E := by
    rw [abs_div, abs_of_pos hp0]
    exact (div_le_div_of_nonneg_right hqRow hp0.le).trans (div_le_self hE hpR)
  have he1 : |(divisorRow S a 1 - X) / ((p : ℝ) * q)| ≤ E := by
    rw [abs_div, abs_of_pos (mul_pos hp0 hq0)]
    exact (div_le_div_of_nonneg_right h1 (mul_nonneg hp0.le hq0.le)).trans
      (div_le_self hE hprod)
  rw [heq]
  have ht1 := abs_sub (divisorRow S a (p.lcm q) - X / (p.lcm q))
    ((divisorRow S a p - X / p) / q)
  have ht2 := abs_sub ((divisorRow S a (p.lcm q) - X / (p.lcm q)) -
    (divisorRow S a p - X / p) / q) ((divisorRow S a q - X / q) / p)
  have ht3 := abs_add_le (((divisorRow S a (p.lcm q) - X / (p.lcm q)) -
    (divisorRow S a p - X / p) / q) - (divisorRow S a q - X / q) / p)
    ((divisorRow S a 1 - X) / ((p : ℝ) * q))
  linarith

lemma variance_pair_expansion (S P : Finset ℕ) (a : ℕ → ℝ) :
    (∑ n ∈ S, a n * (divisorCount P n - harmonicMass P)^2) =
      ∑ p ∈ P, ∑ q ∈ P, centeredPair S a p q := by
  unfold divisorCount harmonicMass centeredPair
  simp_rw [← sum_sub_distrib, pow_two, mul_sum, sum_mul]
  simp_rw [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro p hp
  rw [sum_comm]
  apply sum_congr rfl
  intro q hq
  apply sum_congr rfl
  intro n hn
  ring

/-- A weighted Turán--Kubilius variance estimate from the actual single and
pair divisor rows. No bound for the sum of squares of `a` is required. -/
theorem weighted_variance (S P : Finset ℕ) (a : ℕ → ℝ)
    (hP : ∀ p ∈ P, Nat.Prime p) {X E : ℝ} (hX : 0 ≤ X) (hE : 0 ≤ E)
    (h1 : |divisorRow S a 1 - X| ≤ E)
    (hpRows : ∀ p ∈ P, |divisorRow S a p - X / p| ≤ E)
    (hpqRows : ∀ p ∈ P, ∀ q ∈ P,
      |divisorRow S a (p.lcm q) - X / (p.lcm q)| ≤ E) :
    (∑ n ∈ S, a n * (divisorCount P n - harmonicMass P)^2) ≤
      X * harmonicMass P + 4 * E * (P.card : ℝ)^2 := by
  have hpair (p : ℕ) (hp : p ∈ P) (q : ℕ) (hq : q ∈ P) :
      centeredPair S a p q ≤ (if p = q then X / p else 0) + 4 * E := by
    have hp' := hP p hp
    have hq' := hP q hq
    have herr := centeredPair_error S a (show 1 ≤ p by have := hp'.two_le; omega)
      (show 1 ≤ q by have := hq'.two_le; omega) hE h1 (hpRows p hp) (hpRows q hq)
      (hpqRows p hp q hq)
    have hu := (abs_le.mp herr).2
    by_cases he : p = q
    · subst q
      simp only [Nat.lcm_self, if_true] at hu ⊢
      have hn : 0 ≤ X * (1 / ((p : ℝ) * p)) := by positivity
      have he' : X * (1 / (p : ℝ) - 1 / ((p : ℝ) * p)) =
          X / p - X * (1 / ((p : ℝ) * p)) := by ring
      rw [he'] at hu
      linarith
    · have hlcm : p.lcm q = p * q :=
        ((Nat.coprime_primes hp' hq').mpr he).lcm_eq_mul
      simp only [hlcm, Nat.cast_mul, sub_self, mul_zero, sub_zero] at hu
      simpa only [if_neg he, zero_add] using hu
  rw [variance_pair_expansion]
  apply (sum_le_sum (fun p hp => sum_le_sum (fun q hq => hpair p hp q hq))).trans
  have he : (∑ p ∈ P, ∑ q ∈ P, ((if p = q then X / (p : ℝ) else 0) + 4 * E)) =
      X * harmonicMass P + 4 * E * (P.card : ℝ)^2 := by
    simp only [sum_add_distrib, sum_const, nsmul_eq_mul]
    have hs : (∑ p ∈ P, ∑ q ∈ P, if p = q then X / (p : ℝ) else 0) =
        X * harmonicMass P := by
      rw [harmonicMass, mul_sum]
      apply sum_congr rfl
      intro p hp
      simp [hp, div_eq_mul_inv]
    rw [hs]
    ring
  exact he.le

/-- A weighted Cauchy--Schwarz bound that does not square the weight. -/
theorem amplification_sq (S : Finset ℕ) (a b K : ℕ → ℝ) (H : ℝ)
    (ha : ∀ n ∈ S, 0 ≤ a n) (hb : ∀ n ∈ S, |b n| ≤ 1) :
    (H * (∑ n ∈ S, a n * b n) - ∑ n ∈ S, a n * b n * K n)^2 ≤
      (∑ n ∈ S, a n) * ∑ n ∈ S, a n * (K n - H)^2 := by
  have hc := sum_sq_le_sum_mul_sum_of_sq_eq_mul S
    (r := fun n => a n * b n * (H - K n))
    (f := fun n => a n * (b n)^2)
    (g := fun n => a n * (H - K n)^2)
    (fun n hn => mul_nonneg (ha n hn) (sq_nonneg _))
    (fun n hn => mul_nonneg (ha n hn) (sq_nonneg _))
    (fun n _ => by ring)
  have hfirst : (∑ n ∈ S, a n * (b n)^2) ≤ ∑ n ∈ S, a n := by
    apply sum_le_sum
    intro n hn
    have hsq : (b n)^2 ≤ 1 := by nlinarith [(abs_le.mp (hb n hn)).1, (abs_le.mp (hb n hn)).2]
    simpa using mul_le_mul_of_nonneg_left hsq (ha n hn)
  have hsecond : 0 ≤ ∑ n ∈ S, a n * (H - K n)^2 :=
    sum_nonneg fun n hn => mul_nonneg (ha n hn) (sq_nonneg _)
  have hleft : (∑ n ∈ S, a n * b n * (H - K n)) =
      H * (∑ n ∈ S, a n * b n) - ∑ n ∈ S, a n * b n * K n := by
    simp_rw [mul_sub, sum_sub_distrib, ← sum_mul]
    ring
  rw [hleft] at hc
  apply hc.trans
  have hh := mul_le_mul_of_nonneg_right hfirst hsecond
  have he : (∑ n ∈ S, a n * (H - K n)^2) =
      ∑ n ∈ S, a n * (K n - H)^2 := by
    apply sum_congr rfl
    intro n hn
    ring
  exact hh.trans_eq (by rw [he])

/-- Opening the amplifier gives actual divisor sums, not a new weight
whose correlation has silently been estimated. -/
lemma open_amplifier (S P : Finset ℕ) (a b : ℕ → ℝ) :
    (∑ n ∈ S, a n * b n * divisorCount P n) =
      ∑ p ∈ P, divisorRow S (fun n => a n * b n) p := by
  unfold divisorCount divisorRow
  simp_rw [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro p hp
  apply sum_congr rfl
  intro n hn
  by_cases h : p ∣ n <;> simp [divisorIndicator, h]

/-- Complete finite amplification budget. This controls the replacement
error only; the amplified divisor sum on the left still needs an estimate. -/
theorem amplification_rows_sq (S P : Finset ℕ) (a b : ℕ → ℝ)
    (ha : ∀ n ∈ S, 0 ≤ a n) (hb : ∀ n ∈ S, |b n| ≤ 1)
    (hP : ∀ p ∈ P, Nat.Prime p) {X E : ℝ} (hX : 0 ≤ X) (hE : 0 ≤ E)
    (h1 : |divisorRow S a 1 - X| ≤ E)
    (hpRows : ∀ p ∈ P, |divisorRow S a p - X / p| ≤ E)
    (hpqRows : ∀ p ∈ P, ∀ q ∈ P,
      |divisorRow S a (p.lcm q) - X / (p.lcm q)| ≤ E) :
    (harmonicMass P * (∑ n ∈ S, a n * b n) -
      ∑ p ∈ P, divisorRow S (fun n => a n * b n) p)^2 ≤
      (X + E) * (X * harmonicMass P + 4 * E * (P.card : ℝ)^2) := by
  have hc := amplification_sq S a b (divisorCount P) (harmonicMass P) ha hb
  rw [open_amplifier] at hc
  apply hc.trans
  have ht : (∑ n ∈ S, a n) ≤ X + E := by
    have hh := (abs_le.mp h1).2
    simpa only [divisorRow, one_dvd, if_true] using (show divisorRow S a 1 ≤ X + E by linarith)
  exact mul_le_mul ht (weighted_variance S P a hP hX hE h1 hpRows hpqRows)
    (sum_nonneg fun n hn => mul_nonneg (ha n hn) (sq_nonneg _)) (add_nonneg hX hE)

/-- Specialization to the actual output Mangoldt weight and the Möbius
coefficient. The divisor-row hypotheses and the amplified sum remain explicit. -/
theorem output_moebius_amplification (α : ℝ) (N : ℕ) (P : Finset ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p) {X E : ℝ} (hX : 0 ≤ X) (hE : 0 ≤ E)
    (h1 : |divisorRow (Ioc 0 N) (fun n => ArithmeticFunction.vonMangoldt ⌊α * n⌋₊) 1 - X| ≤ E)
    (hpRows : ∀ p ∈ P,
      |divisorRow (Ioc 0 N) (fun n => ArithmeticFunction.vonMangoldt ⌊α * n⌋₊) p - X / p| ≤ E)
    (hpqRows : ∀ p ∈ P, ∀ q ∈ P,
      |divisorRow (Ioc 0 N) (fun n => ArithmeticFunction.vonMangoldt ⌊α * n⌋₊)
        (p.lcm q) - X / (p.lcm q)| ≤ E) :
    (harmonicMass P * (∑ n ∈ Ioc 0 N,
      ArithmeticFunction.vonMangoldt ⌊α * n⌋₊ * (ArithmeticFunction.moebius n : ℝ)) -
      ∑ p ∈ P, divisorRow (Ioc 0 N) (fun n =>
        ArithmeticFunction.vonMangoldt ⌊α * n⌋₊ * (ArithmeticFunction.moebius n : ℝ)) p)^2 ≤
      (X + E) * (X * harmonicMass P + 4 * E * (P.card : ℝ)^2) := by
  apply amplification_rows_sq (Ioc 0 N) P _ _
    (fun n _ => ArithmeticFunction.vonMangoldt_nonneg) _ hP hX hE h1 hpRows hpqRows
  intro n hn
  exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n)

#print axioms centeredPair_error
#print axioms amplification_sq
#print axioms weighted_variance
#print axioms amplification_rows_sq
#print axioms output_moebius_amplification

end Erdos972WeightedDivisorAmplification
