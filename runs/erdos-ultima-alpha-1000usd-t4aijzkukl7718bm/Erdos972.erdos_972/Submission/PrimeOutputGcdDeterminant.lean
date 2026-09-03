import Submission.DivisorRowDispersion

/-! A nonzero small determinant for two distinct prime inputs with a common
output divisor. This is structural information, not a prime-pair lower bound. -/
namespace Erdos972PrimeOutputGcdDeterminant

open Finset ArithmeticFunction
open Erdos972PrimePowerError Erdos972PrimeRoughOutputs Erdos972SelbergLowerTest
open Erdos972DivisorRowDispersion
set_option autoImplicit false
set_option maxHeartbeats 1500000

/-- Eliminating the slope leaves a determinant in a strict interval of
length (p+q)/d. The floor errors are not discarded. -/
lemma cofactor_determinant_bounds {α : ℝ} (hα : 0 ≤ α)
    {p q d k l : ℕ} (hp : 0 < p) (hq : 0 < q)
    (hk : floorMul α p = d*k) (hl : floorMul α q = d*l) :
    -(q:ℝ) < (d:ℝ)*((k:ℝ)*q-(l:ℝ)*p) ∧
      (d:ℝ)*((k:ℝ)*q-(l:ℝ)*p) < p := by
  have hp0 : (d:ℝ)*k ≤ α*p := by
    have hh := Nat.floor_le (mul_nonneg hα (Nat.cast_nonneg p))
    change (floorMul α p:ℝ) ≤ α*p at hh
    simpa only [hk, Nat.cast_mul] using hh
  have hq0 : (d:ℝ)*l ≤ α*q := by
    have hh := Nat.floor_le (mul_nonneg hα (Nat.cast_nonneg q))
    change (floorMul α q:ℝ) ≤ α*q at hh
    simpa only [hl, Nat.cast_mul] using hh
  have hp1 : α*p < (d:ℝ)*k+1 := by
    have hh := Nat.lt_floor_add_one (α*p)
    change α*p < (floorMul α p:ℝ)+1 at hh
    simpa only [hk, Nat.cast_mul] using hh
  have hq1 : α*q < (d:ℝ)*l+1 := by
    have hh := Nat.lt_floor_add_one (α*q)
    change α*q < (floorMul α q:ℝ)+1 at hh
    simpa only [hl, Nat.cast_mul] using hh
  have hp0q := mul_le_mul_of_nonneg_right hp0 (Nat.cast_nonneg (α := ℝ) q)
  have hq0p := mul_le_mul_of_nonneg_right hq0 (Nat.cast_nonneg (α := ℝ) p)
  have hp1q := mul_lt_mul_of_pos_right hp1 (Nat.cast_pos.mpr hq : (0:ℝ) < q)
  have hq1p := mul_lt_mul_of_pos_right hq1 (Nat.cast_pos.mpr hp : (0:ℝ) < p)
  constructor <;> nlinarith only [hp0q, hq0p, hp1q, hq1p]

lemma zero_determinant_divisor_le_slope {α : ℝ} (hα : 1 ≤ α)
    {p q d k l : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hk : floorMul α p = d*k) (he : k*q = l*p) : (d:ℝ) ≤ α := by
  have hcop := (Nat.coprime_primes hp hq).mpr hpq
  have hpk : p ∣ k := hcop.dvd_of_dvd_mul_right (by rw [he]; exact dvd_mul_left _ _)
  have hkpos : 0 < k := by
    have hf := floorMul_pos hα hp.pos
    rw [hk] at hf
    by_contra hk0
    have hkz : k = 0 := by omega
    simp only [hkz, mul_zero] at hf
    omega
  have hple := Nat.le_of_dvd hkpos hpk
  have hreal : (d:ℝ)*k ≤ α*p := by
    have hh := floorMul_le_real hα (le_refl p)
    simpa only [hk, Nat.cast_mul] using hh
  have hm := mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hple : (p:ℝ) ≤ k)
    (Nat.cast_nonneg (α := ℝ) d)
  exact (mul_le_mul_iff_left₀ (Nat.cast_pos.mpr hp.pos : (0:ℝ) < p)).mp
    (by nlinarith only [hm, hreal])

/-- In the nonlocal divisor range, the determinant cannot be zero. -/
theorem common_divisor_determinant {α : ℝ} (hα : 1 ≤ α)
    {p q d : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hd : α < (d:ℝ)) (hdp : d ∣ floorMul α p) (hdq : d ∣ floorMul α q) :
    ∃ k l : ℕ, floorMul α p = d*k ∧ floorMul α q = d*l ∧
      k*q ≠ l*p ∧
      -(q:ℝ) < (d:ℝ)*((k:ℝ)*q-(l:ℝ)*p) ∧
      (d:ℝ)*((k:ℝ)*q-(l:ℝ)*p) < p := by
  let k := floorMul α p/d
  let l := floorMul α q/d
  have hk : floorMul α p = d*k := (Nat.mul_div_cancel' hdp).symm
  have hl : floorMul α q = d*l := (Nat.mul_div_cancel' hdq).symm
  refine ⟨k, l, hk, hl, ?_, cofactor_determinant_bounds (by linarith) hp.pos hq.pos hk hl⟩
  intro he
  exact (not_le_of_gt hd) (zero_determinant_divisor_le_slope hα hp hq hpq hk he)

/-- Distinct prime inputs at most N cannot share an output divisor d>=N
once d exceeds the slope. -/
theorem common_output_divisor_lt_max {α : ℝ} (hα : 1 ≤ α)
    {p q d : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hd : α < (d:ℝ)) (hdp : d ∣ floorMul α p) (hdq : d ∣ floorMul α q) :
    d < max p q := by
  obtain ⟨k, l, hk, hl, hne, hlo, hhi⟩ := common_divisor_determinant hα hp hq hpq hd hdp hdq
  by_contra hn
  have hpd : p ≤ d := (le_max_left _ _).trans (le_of_not_gt hn)
  have hqd : q ≤ d := (le_max_right _ _).trans (le_of_not_gt hn)
  have hpdR : (p:ℝ) ≤ d := Nat.cast_le.mpr hpd
  have hqdR : (q:ℝ) ≤ d := Nat.cast_le.mpr hqd
  have hd0 : (0:ℝ) < d := by linarith only [hα, hd]
  have habs : |(k:ℝ)*q-(l:ℝ)*p| < 1 := by
    rw [abs_lt]
    constructor <;> nlinarith only [hlo, hhi, hpdR, hqdR, hd0]
  have hi : |((k:ℤ)*q-(l:ℤ)*p)| < 1 := by exact_mod_cast habs
  have hz := Int.abs_lt_one_iff.mp hi
  apply hne
  exact_mod_cast sub_eq_zero.mp hz

lemma at_most_one_prime_input {α : ℝ} (hα : 1 ≤ α) {N d : ℕ}
    (hd : α < (d:ℝ)) (hNd : N ≤ d) {p q : ℕ}
    (hpN : p ≤ N) (hqN : q ≤ N) (hp : p.Prime) (hq : q.Prime)
    (hdp : d ∣ floorMul α p) (hdq : d ∣ floorMul α q) : p = q := by
  by_contra hpq
  have hh := common_output_divisor_lt_max hα hp hq hpq hd hdp hdq
  exact (not_lt_of_ge ((max_le hpN hqN).trans hNd)) hh

/-- The square of a large-divisor prime row contains no off-diagonal
prime terms. The weights in this identity are the actual prime weights. -/
theorem large_divisor_row_square {α : ℝ} (hα : 1 ≤ α) {N d : ℕ}
    (hd : α < (d:ℝ)) (hNd : N ≤ d) :
    (row (Ioc 0 N) primeWeight (floorMul α) d)^2 =
      ∑ n ∈ Ioc 0 N, if d ∣ floorMul α n then (primeWeight n)^2 else 0 := by
  classical
  unfold row
  rw [pow_two, sum_mul_sum]
  apply sum_congr rfl
  intro n hn
  rw [sum_eq_single n]
  · split_ifs <;> ring
  · intro m hm hmn
    by_cases hdn : d ∣ floorMul α n
    swap
    · simp [hdn]
    by_cases hdm : d ∣ floorMul α m
    swap
    · simp [hdm]
    rw [if_pos hdn, if_pos hdm]
    by_cases hnp : n.Prime
    swap
    · simp [primeWeight, hnp]
    by_cases hmp : m.Prime
    swap
    · simp [primeWeight, hmp]
    exact (hmn (at_most_one_prime_input hα hd hNd
      (mem_Ioc.mp hm).2 (mem_Ioc.mp hn).2 hmp hnp hdm hdn)).elim
  · intro hn'
    exact (hn' hn).elim

/-- The full second moment in any finite block of divisors beyond N is
only a diagonal cost. No distribution assertion is needed for this range. -/
theorem large_divisor_block_secondMoment {α : ℝ} (hα : 1 ≤ α) (N : ℕ)
    (T : Finset ℕ) (hT : ∀ d ∈ T, N ≤ d ∧ α < (d:ℝ)) :
    (∑ d ∈ T, (row (Ioc 0 N) primeWeight (floorMul α) d)^2) ≤
      (Real.log N)^2*(floorMul α N:ℝ)*(1+Real.log (floorMul α N)) := by
  classical
  have he : (∑ d ∈ T, (row (Ioc 0 N) primeWeight (floorMul α) d)^2) =
      ∑ n ∈ Ioc 0 N, (primeWeight n)^2*
        ((T.filter (fun d => d ∣ floorMul α n)).card:ℝ) := by
    rw [sum_congr rfl (fun d hd => large_divisor_row_square hα (hT d hd).2 (hT d hd).1), sum_comm]
    apply sum_congr rfl
    intro n hn
    rw [← sum_filter, sum_const, nsmul_eq_mul, mul_comm]
  rw [he]
  have hbound : (∑ n ∈ Ioc 0 N, (primeWeight n)^2*
      ((T.filter (fun d => d ∣ floorMul α n)).card:ℝ)) ≤
        (Real.log N)^2*(∑ n ∈ Ioc 0 N, ((floorMul α n).divisors.card:ℝ)) := by
    rw [mul_sum]
    apply sum_le_sum
    intro n hn
    have hcard : (T.filter (fun d => d ∣ floorMul α n)).card ≤
        (floorMul α n).divisors.card := by
      apply card_le_card
      intro d hd
      exact Nat.mem_divisors.mpr ⟨(mem_filter.mp hd).2,
        (floorMul_pos hα (mem_Ioc.mp hn).1).ne'⟩
    have hp : primeWeight n ≤ Real.log N := by
      unfold primeWeight
      split_ifs
      · exact log_input_le hn
      · exact Real.log_natCast_nonneg _
    exact mul_le_mul (pow_le_pow_left₀ (primeWeight_nonneg n) hp 2)
      (Nat.cast_le.mpr hcard) (Nat.cast_nonneg _) (sq_nonneg _)
  apply hbound.trans
  have hh := mul_le_mul_of_nonneg_left
    (Erdos972SmoothCorrelationApprox.sum_output_divisors_le hα N) (sq_nonneg (Real.log N))
  convert hh using 1
  ring

#print axioms common_divisor_determinant
#print axioms common_output_divisor_lt_max
#print axioms large_divisor_row_square
#print axioms large_divisor_block_secondMoment
end Erdos972PrimeOutputGcdDeterminant
