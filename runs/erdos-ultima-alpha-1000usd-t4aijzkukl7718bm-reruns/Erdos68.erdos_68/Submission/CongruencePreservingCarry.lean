import Submission.LambertPrimeBand
import Submission.IndexDependentTelescoping

/-!
Congruence-preserving carries for the actual series in Erdős 68.
This is an auxiliary representation, not an irrationality proof.
-/

namespace CongruencePreservingCarry

open Erdos68Development Filter
open scoped Topology

lemma lambertPrefix_succ (n : ℕ) :
    lambertPrefix (n+1) = (n+1)*lambertPrefix n+lambertCoeff (n+1) := by
  unfold lambertPrefix
  rw [Finset.sum_range_succ, Finset.mul_sum]
  simp only [Nat.div_self (Nat.factorial_pos _), mul_one]
  congr 1
  apply Finset.sum_congr rfl
  intro m hm
  have hd := Nat.factorial_dvd_factorial (show m ≤ n by simpa using Finset.mem_range.mp hm)
  rw [Nat.factorial_succ, Nat.mul_div_assoc _ hd]
  ring

lemma lambertPrefix_three : lambertPrefix 3 = 4 := by decide

/-- `y r` is the rational Lambert residual at index `r+3`. -/
def y (r : ℕ) : ℚ := scaledSumQ (r+2)-lambertPrefix (r+3)

def delta (r : ℕ) : ℚ := 1/((r+4).factorial-1 : ℚ)

lemma delta_pos (r : ℕ) : 0 < delta r := by
  apply one_div_pos.mpr
  have h : (2 : ℚ) ≤ (r+4).factorial := by
    exact_mod_cast factorial_ge_two (r+2)
  linarith

lemma y_zero : y 0 = 16/5 := by
  norm_num [y, scaledSumQ, lambertPrefix_three, Finset.sum_range_succ, Nat.factorial]

lemma y_succ (r : ℕ) :
    y (r+1) = (r+4)*y r+1+delta r-lambertCoeff (r+4) := by
  unfold y delta
  rw [show r+1+2 = (r+2)+1 by omega, scaledSumQ_succ,
    show r+1+3 = (r+3)+1 by omega, lambertPrefix_succ]
  push_cast
  ring

/-- Carries preserve coefficient one at prime indices and the predecessor
congruence at all other indices. -/
def carry : ℕ → ℤ
  | 0 => 0
  | r+1 => if (r+4).Prime then (r+4)*carry r else
      carry r+(r+3)*⌊(y (r+1)-carry r)/(r+3)⌋

def z (r : ℕ) : ℚ := y r-carry r

def coeffRow (r : ℕ) : ℤ := lambertCoeff (r+4)+carry (r+1)-(r+4)*carry r

def coeff (n : ℕ) : ℤ := if n < 4 then lambertCoeff n else coeffRow (n-4)

lemma coeff_add_four (r : ℕ) : coeff (r+4) = coeffRow r := by simp [coeff]

lemma coeffRow_prime (r : ℕ) (hp : (r+4).Prime) : coeffRow r = 1 := by
  simp [coeffRow, carry, hp, lambertCoeff_prime hp]

lemma coeff_prime (p : ℕ) (hp : p.Prime) : coeff p = 1 := by
  by_cases h : p < 4
  · simp [coeff, h, lambertCoeff_prime hp]
  · obtain ⟨r, rfl⟩ : ∃ r, p = r+4 := ⟨p-4, by omega⟩
    exact (coeff_add_four r).trans (coeffRow_prime r hp)

lemma z_zero : z 0 = 16/5 := by simp [z, carry, y_zero]

lemma z_prime (r : ℕ) (hp : (r+4).Prime) :
    z (r+1) = (r+4)*z r+delta r := by
  simp only [z, carry, if_pos hp, y_succ, lambertCoeff_prime hp]
  push_cast
  ring

lemma z_nonprime_bounds (r : ℕ) (hp : ¬(r+4).Prime) :
    0 ≤ z (r+1) ∧ z (r+1) < r+3 := by
  have hpos : (0 : ℚ) < r+3 := by positivity
  have hlo := Int.sub_floor_div_mul_nonneg (y (r+1)-(carry r : ℚ)) hpos
  have hhi := Int.sub_floor_div_mul_lt (y (r+1)-(carry r : ℚ)) hpos
  simp only [z, carry, if_neg hp]
  push_cast
  constructor <;> nlinarith

lemma z_nonneg (r : ℕ) : 0 ≤ z r := by
  induction r with
  | zero => rw [z_zero]; norm_num
  | succ r ih =>
    by_cases hp : (r+4).Prime
    · rw [z_prime r hp]
      exact add_nonneg (mul_nonneg (by positivity) ih) (delta_pos r).le
    · exact (z_nonprime_bounds r hp).1

lemma coeffRow_congruence (r : ℕ) : (r+3 : ℤ) ∣ coeffRow r-1 := by
  have ha : (r+3 : ℤ) ∣ (lambertCoeff (r+4) : ℤ)-1 := by
    have h := (Nat.modEq_iff_dvd' (lambertCoeff_one_le (show 2 ≤ r+4 by omega))).mp
      (lambertCoeff_modEq_pred (show 2 ≤ r+4 by omega)).symm
    simpa only [show r+4-1 = r+3 by omega,
      Nat.cast_sub (lambertCoeff_one_le (show 2 ≤ r+4 by omega)), Nat.cast_one] using
        (Int.natCast_dvd_natCast.mpr h)
  by_cases hp : (r+4).Prime
  · rw [coeffRow_prime r hp, sub_self]
    exact dvd_zero _
  · unfold coeffRow
    rw [carry, if_neg hp]
    convert dvd_add ha (dvd_mul_right (r+3 : ℤ)
      (⌊(y (r+1)-carry r)/(r+3)⌋-carry r)) using 1
    ring

lemma coeffRow_identity (r : ℕ) :
    (coeffRow r : ℚ) = 1+delta r+(r+4)*z r-z (r+1) := by
  simp only [coeffRow, z, y_succ]
  push_cast
  ring

lemma coeffRow_positive (r : ℕ) : 0 < coeffRow r := by
  by_cases hp : (r+4).Prime
  · rw [coeffRow_prime r hp]; omega
  · have hlo := z_nonneg r
    have hhi := (z_nonprime_bounds r hp).2
    have hdelta := delta_pos r
    have hb : -(r+2 : ℚ) < coeffRow r := by
      rw [coeffRow_identity]
      have hm := mul_nonneg (show (0 : ℚ) ≤ r+4 by positivity) hlo
      linarith
    have hb' : -(r+2 : ℤ) < coeffRow r := by exact_mod_cast hb
    obtain ⟨k, hk⟩ := coeffRow_congruence r
    have hk0 : 0 ≤ k := by
      by_contra hn
      have hkn : k ≤ -1 := by omega
      have hm := mul_le_mul_of_nonneg_left hkn (show (0 : ℤ) ≤ r+3 by positivity)
      nlinarith
    have hm := mul_nonneg (show (0 : ℤ) ≤ r+3 by positivity) hk0
    omega

noncomputable def tail (r : ℕ) : ℝ :=
  (r+3).factorial*(∑' n : ℕ, term n)-(lambertPrefix (r+3)+carry r : ℤ)

lemma tail_split (r : ℕ) :
    tail r = (r+3).factorial*((∑' n : ℕ, term n)-
      ∑ k ∈ Finset.range (r+2), term k)+(z r : ℝ) := by
  simp only [tail, z, y, Rat.cast_sub, Rat.cast_intCast, Rat.cast_natCast,
    Int.cast_add, Int.cast_natCast]
  rw [cast_scaledSumQ]
  ring

lemma tail_pos (r : ℕ) : 0 < tail r := by
  rw [tail_split]
  have h := (scaled_partial_sum_error (r+2)).1
  have hz : (0 : ℝ) ≤ z r := by exact_mod_cast z_nonneg r
  simpa only [Nat.add_assoc] using add_pos_of_pos_of_nonneg h hz

lemma tail_succ (r : ℕ) :
    tail (r+1) = (r+4)*tail r-(coeffRow r : ℝ) := by
  simp only [tail, coeffRow, show r+1+3 = (r+3)+1 by omega, lambertPrefix_succ,
    Nat.factorial_succ]
  push_cast
  ring

lemma tail_nonprime_lt (r : ℕ) (hp : ¬(r+4).Prime) : tail (r+1) < r+4 := by
  rw [tail_split]
  have hu := (scaled_partial_sum_error (r+1+2)).2
  have hz : (z (r+1) : ℝ) < r+3 := by exact_mod_cast (z_nonprime_bounds r hp).2
  have hdiv : (3 : ℝ)/(r+1+2+2) < 1 := by
    apply (div_lt_one (by positivity)).mpr
    linarith [Nat.cast_nonneg (α := ℝ) r]
  push_cast at hu
  linarith

lemma tail_zero_bounds : 0 < tail 0 ∧ tail 0 < 9 := by
  refine ⟨tail_pos 0, ?_⟩
  have hb := sum_bounds.2
  simp only [tail, zero_add, carry, lambertPrefix_three]
  norm_num
  linarith

lemma tail_lt_square (r : ℕ) : tail r < (r+3 : ℝ)^2 := by
  cases r with
  | zero => simpa using (show tail 0 < (0+3 : ℝ)^2 by norm_num; exact tail_zero_bounds.2)
  | succ r =>
    by_cases hp : (r+4).Prime
    · have hr : 0 < r := by
        by_contra hn
        have hr0 : r = 0 := by omega
        subst r
        norm_num at hp
      obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr.ne'
      have hnp : ¬(s+4).Prime := by
        have hodd := hp.eq_two_or_odd.resolve_left (by omega)
        intro hq
        have hqodd := hq.eq_two_or_odd.resolve_left (by omega)
        omega
      have ht := tail_nonprime_lt s hnp
      rw [tail_succ, coeffRow_prime (s+1) hp]
      push_cast
      have hmul := mul_lt_mul_of_pos_left ht (show (0 : ℝ) < s+5 by positivity)
      nlinarith [Nat.cast_nonneg (α := ℝ) s]
    · have ht := tail_nonprime_lt r hp
      push_cast at *
      nlinarith [Nat.cast_nonneg (α := ℝ) r]


noncomputable def normalizedTail (r : ℕ) : ℝ := tail r/(r+3).factorial

lemma summable_normalizedTail : Summable normalizedTail := by
  apply ((summable_nat_add_iff 3).mpr
    (IndexDependentTelescoping.summable_nat_pow_div_factorial 2)).of_norm_bounded
  intro r
  simp only [normalizedTail, Real.norm_eq_abs,
    abs_of_pos (div_pos (tail_pos r) (by positivity : (0 : ℝ) < (r+3).factorial))]
  apply div_le_div_of_nonneg_right _ (by positivity)
  simpa only [Nat.cast_add, Nat.cast_ofNat] using (tail_lt_square r).le

lemma coeffRow_div (r : ℕ) :
    (coeffRow r : ℝ)/(r+4).factorial = normalizedTail r-normalizedTail (r+1) := by
  have hf : ((r+3).factorial : ℝ) ≠ 0 := by positivity
  have hn : (r+4 : ℝ) ≠ 0 := by positivity
  simp only [normalizedTail, tail_succ, show r+1+3 = r+4 by omega]
  rw [show r+4 = (r+3)+1 by omega, Nat.factorial_succ]
  push_cast
  field_simp
  ring

lemma normalizedTail_zero : normalizedTail 0 = (∑' k : ℕ, term k)-2/3 := by
  norm_num [normalizedTail, tail, carry, lambertPrefix_three]
  ring

lemma hasSum_coeffRow :
    HasSum (fun r : ℕ => (coeffRow r : ℝ)/(r+4).factorial)
      ((∑' k : ℕ, term k)-2/3) := by
  have hs := summable_normalizedTail
  have ht := (summable_nat_add_iff 1).mpr hs
  have he := hs.sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_one, normalizedTail_zero] at he
  have he' : (∑' r, normalizedTail r)-(∑' r, normalizedTail (r+1)) =
      (∑' k : ℕ, term k)-2/3 := by linarith
  simpa only [coeffRow_div, he'] using hs.hasSum.sub ht.hasSum

lemma summable_coeff : Summable (fun n : ℕ => (coeff n : ℝ)/n.factorial) := by
  apply (summable_nat_add_iff 4).mp
  simpa only [coeff_add_four] using hasSum_coeffRow.summable

lemma initial_coeffs : (∑ k ∈ Finset.range 4, (coeff k : ℝ)/k.factorial) = 2/3 := by
  have h0 : coeff 0 = 0 := by decide
  have h1 : coeff 1 = 0 := by decide
  have h2 : coeff 2 = 1 := coeff_prime 2 (by decide)
  have h3 : coeff 3 = 1 := coeff_prime 3 (by decide)
  norm_num [Finset.sum_range_succ, h0, h1, h2, h3]

/-- The carries preserve the exact original sum, not merely its congruences. -/
theorem sum_coeff : (∑' n : ℕ, (coeff n : ℝ)/n.factorial) = ∑' n : ℕ, term n := by
  have he := summable_coeff.sum_add_tsum_nat_add 4
  simp only [initial_coeffs, coeff_add_four, hasSum_coeffRow.tsum_eq] at he
  linarith

lemma prefix_identity (r : ℕ) :
    (∑ k ∈ Finset.range (r+4), (coeff k : ℝ)/k.factorial) =
      (∑' n : ℕ, term n)-normalizedTail r := by
  induction r with
  | zero => rw [zero_add, initial_coeffs, normalizedTail_zero]; ring
  | succ r ih =>
    rw [show r+1+4 = (r+4)+1 by omega, Finset.sum_range_succ, ih,
      coeff_add_four, coeffRow_div]
    ring

/-- `tail r` is the actual factorial-scaled tail of the modified series. -/
lemma scaled_tail_identity (r : ℕ) :
    (r+3).factorial*((∑' n : ℕ, (coeff n : ℝ)/n.factorial)-
      ∑ k ∈ Finset.range (r+4), (coeff k : ℝ)/k.factorial) = tail r := by
  rw [sum_coeff, prefix_identity]
  simp only [sub_sub_cancel, normalizedTail]
  exact mul_div_cancel₀ _ (by positivity)

lemma coeff_positive (n : ℕ) (hn : 2 ≤ n) : 0 < coeff n := by
  by_cases h : n < 4
  · have he : n = 2 ∨ n = 3 := by omega
    rcases he with rfl | rfl <;> rw [coeff_prime _ (by decide)] <;> omega
  · obtain ⟨r, rfl⟩ : ∃ r, n = r+4 := ⟨n-4, by omega⟩
    simpa only [coeff_add_four] using coeffRow_positive r

lemma predecessor_congruence (n : ℕ) (hn : 4 ≤ n) : (n-1 : ℤ) ∣ coeff n-1 := by
  obtain ⟨r, rfl⟩ : ∃ r, n = r+4 := ⟨n-4, by omega⟩
  simpa only [coeff_add_four, Nat.cast_add, Nat.cast_ofNat,
    show (r : ℤ)+4-1 = r+3 by ring] using coeffRow_congruence r

/-- A target representation at the quadratic boundary. These hypotheses do
NOT suffice for the existing subquadratic-tail irrationality criteria. -/
theorem representation_properties :
    (∑' n : ℕ, (coeff n : ℝ)/n.factorial) = (∑' n : ℕ, term n) ∧
    (∀ n ≥ 2, 0 < coeff n) ∧
    (∀ p : ℕ, p.Prime → coeff p = 1) ∧
    (∀ n : ℕ, 4 ≤ n → (n-1 : ℤ) ∣ coeff n-1) ∧
    (∀ r : ℕ, 0 < tail r ∧ tail r < (r+3 : ℝ)^2) ∧
    (∀ r : ℕ, ¬(r+4).Prime → tail (r+1) < r+4) := by
  exact ⟨sum_coeff, coeff_positive, coeff_prime, predecessor_congruence,
    fun r => ⟨tail_pos r, tail_lt_square r⟩, tail_nonprime_lt⟩

#print axioms representation_properties
#print axioms scaled_tail_identity

end CongruencePreservingCarry
