import Submission.PrimeRoughOutputs
import Submission.SmoothCorrelationApprox

/-! Exact mean-square dispersion of the actual divisor rows. The diagonal
has an elementary bound, but no cancellation of the centered off-diagonal
is asserted here. -/
namespace Erdos972DivisorRowDispersion

open Finset ArithmeticFunction
open Erdos972SelbergLowerTest Erdos972PrimeRoughOutputs
open Erdos972PrimePowerError Erdos972SmoothCorrelationApprox
set_option autoImplicit false
set_option maxHeartbeats 1500000

noncomputable def commonDivisorCount (D x y : ℕ) : ℝ :=
  ∑ d ∈ Ioc 0 D, if d ∣ x ∧ d ∣ y then 1 else 0

noncomputable def reciprocalDivisorSum (D x : ℕ) : ℝ :=
  ∑ d ∈ Ioc 0 D, if d ∣ x then 1/(d:ℝ) else 0

noncomputable def rowEnergy (S : Finset ℕ) (a : ℕ → ℝ)
    (g : ℕ → ℕ) (D : ℕ) (X : ℝ) : ℝ :=
  ∑ d ∈ Ioc 0 D, (row S a g d-X/d)^2

noncomputable def rowDiagonal (S : Finset ℕ) (a : ℕ → ℝ)
    (g : ℕ → ℕ) (D : ℕ) : ℝ :=
  ∑ n ∈ S, a n^2*commonDivisorCount D (g n) (g n)

noncomputable def rowOffDiagonal (S : Finset ℕ) (a : ℕ → ℝ)
    (g : ℕ → ℕ) (D : ℕ) : ℝ :=
  ∑ n ∈ S, ∑ m ∈ S.erase n, a n*a m*commonDivisorCount D (g n) (g m)

lemma commonDivisorCount_nonneg (D x y : ℕ) : 0 ≤ commonDivisorCount D x y := by
  unfold commonDivisorCount
  apply sum_nonneg
  intro d hd
  split_ifs <;> norm_num

lemma commonDivisorCount_eq_gcd_card (D x y : ℕ) :
    commonDivisorCount D x y = ((Ioc 0 D).filter (fun d => d ∣ x.gcd y)).card := by
  classical
  simp only [commonDivisorCount, ← Nat.dvd_gcd_iff, ← sum_filter, sum_const,
    nsmul_eq_mul, mul_one]

lemma commonDivisorCount_self_le {x : ℕ} (hx : x ≠ 0) (D : ℕ) :
    commonDivisorCount D x x ≤ (x.divisors.card:ℝ) := by
  rw [commonDivisorCount_eq_gcd_card, Nat.gcd_self]
  exact Nat.cast_le.mpr (card_le_card (by
    intro d hd
    exact Nat.mem_divisors.mpr ⟨(mem_filter.mp hd).2, hx⟩))

lemma row_second_moment (S : Finset ℕ) (a : ℕ → ℝ)
    (g : ℕ → ℕ) (D : ℕ) :
    (∑ d ∈ Ioc 0 D, (row S a g d)^2) =
      ∑ n ∈ S, ∑ m ∈ S, a n*a m*commonDivisorCount D (g n) (g m) := by
  have hterm (d : ℕ) : (row S a g d)^2 =
      ∑ n ∈ S, ∑ m ∈ S, a n*a m*(if d ∣ g n ∧ d ∣ g m then 1 else 0) := by
    simp only [row, pow_two]
    rw [sum_mul_sum]
    apply sum_congr rfl
    intro n hn
    apply sum_congr rfl
    intro m hm
    by_cases hdn : d ∣ g n <;> by_cases hdm : d ∣ g m <;> simp [hdn, hdm]
  simp_rw [hterm]
  rw [sum_comm]
  apply sum_congr rfl
  intro n hn
  rw [sum_comm]
  apply sum_congr rfl
  intro m hm
  simp only [commonDivisorCount, mul_sum]

lemma row_second_moment_split (S : Finset ℕ) (a : ℕ → ℝ)
    (g : ℕ → ℕ) (D : ℕ) :
    (∑ d ∈ Ioc 0 D, (row S a g d)^2) =
      rowDiagonal S a g D+rowOffDiagonal S a g D := by
  rw [row_second_moment]
  unfold rowDiagonal rowOffDiagonal
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro n hn
  rw [← sum_erase_add S (fun m => a n*a m*commonDivisorCount D (g n) (g m)) hn]
  ring

lemma reciprocal_rows (S : Finset ℕ) (a : ℕ → ℝ)
    (g : ℕ → ℕ) (D : ℕ) :
    (∑ d ∈ Ioc 0 D, row S a g d/(d:ℝ)) =
      ∑ n ∈ S, a n*reciprocalDivisorSum D (g n) := by
  simp only [row, sum_div, reciprocalDivisorSum, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro n hn
  apply sum_congr rfl
  intro d hd
  split_ifs <;> ring

/-- The centering terms are indispensable. An estimate for the raw gcd
second moment alone is not an estimate for this dispersion. -/
theorem rowEnergy_identity (S : Finset ℕ) (a : ℕ → ℝ)
    (g : ℕ → ℕ) (D : ℕ) (X : ℝ) :
    rowEnergy S a g D X = rowDiagonal S a g D+rowOffDiagonal S a g D-
      2*X*(∑ n ∈ S, a n*reciprocalDivisorSum D (g n))+
      X^2*(∑ d ∈ Ioc 0 D, 1/(d:ℝ)^2) := by
  rw [← row_second_moment_split, ← reciprocal_rows]
  unfold rowEnergy
  simp only [mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
  apply sum_congr rfl
  intro d hd
  ring

lemma rowEnergy_nonneg (S : Finset ℕ) (a : ℕ → ℝ)
    (g : ℕ → ℕ) (D : ℕ) (X : ℝ) : 0 ≤ rowEnergy S a g D X :=
  sum_nonneg (fun d _ => sq_nonneg _)

/-- A genuine mean-square row bound would control a signed divisor
polynomial without taking the worst individual row error. -/
theorem weighted_row_error_square (S : Finset ℕ) (a : ℕ → ℝ)
    (g : ℕ → ℕ) (D : ℕ) (X : ℝ) (c : ℕ → ℝ) :
    |∑ d ∈ Ioc 0 D, c d*(row S a g d-X/d)|^2 ≤
      (∑ d ∈ Ioc 0 D, c d^2)*rowEnergy S a g D X := by
  rw [sq_abs]
  exact sum_mul_sq_le_sq_mul_sq _ _ _

lemma absolute_row_error_square (S : Finset ℕ) (a : ℕ → ℝ)
    (g : ℕ → ℕ) (D : ℕ) (X : ℝ) :
    (∑ d ∈ Ioc 0 D, |row S a g d-X/d|)^2 ≤ (D:ℝ)*rowEnergy S a g D X := by
  have hh := sum_mul_sq_le_sq_mul_sq (Ioc 0 D) (fun _ => (1:ℝ))
    (fun d => |row S a g d-X/d|)
  simpa only [one_mul, one_pow, sq_abs, sum_const, Nat.card_Ioc, Nat.sub_zero,
    nsmul_eq_mul, mul_one, rowEnergy] using hh

lemma rowDiagonal_bound (S : Finset ℕ) (a : ℕ → ℝ) (g : ℕ → ℕ)
    (D : ℕ) {L : ℝ} (hL : 0 ≤ L)
    (hg : ∀ n ∈ S, g n ≠ 0) (ha : ∀ n ∈ S, |a n| ≤ L) :
    rowDiagonal S a g D ≤ L^2*(∑ n ∈ S, ((g n).divisors.card:ℝ)) := by
  unfold rowDiagonal
  rw [mul_sum]
  apply sum_le_sum
  intro n hn
  have hb : a n^2 ≤ L^2 := by
    simpa only [sq_abs] using (pow_le_pow_left₀ (abs_nonneg (a n)) (ha n hn) 2)
  exact mul_le_mul hb (commonDivisorCount_self_le (hg n hn) D)
    (commonDivisorCount_nonneg _ _ _) (sq_nonneg L)

/-- On the actual prime-input Beatty graph, the whole diagonal is bounded
by O_alpha(N log^3 N), independently of the divisor cutoff D. -/
theorem prime_rowDiagonal_bound {α : ℝ} (hα : 1 ≤ α) (N D : ℕ) :
    rowDiagonal (Ioc 0 N) primeWeight (floorMul α) D ≤
      (Real.log N)^2*(floorMul α N:ℝ)*(1+Real.log (floorMul α N)) := by
  have ha (n : ℕ) (hn : n ∈ Ioc 0 N) : |primeWeight n| ≤ Real.log N := by
    rw [abs_of_nonneg (primeWeight_nonneg n)]
    unfold primeWeight
    split_ifs
    · exact log_input_le hn
    · exact Real.log_natCast_nonneg _
  have hh := rowDiagonal_bound (Ioc 0 N) primeWeight (floorMul α) D
    (Real.log_natCast_nonneg N) (fun n hn => (floorMul_pos hα (mem_Ioc.mp hn).1).ne') ha
  apply hh.trans
  have hd := mul_le_mul_of_nonneg_left (sum_output_divisors_le hα N) (sq_nonneg (Real.log N))
  convert hd using 1
  ring

#print axioms rowEnergy_identity
#print axioms weighted_row_error_square
#print axioms prime_rowDiagonal_bound
end Erdos972DivisorRowDispersion
