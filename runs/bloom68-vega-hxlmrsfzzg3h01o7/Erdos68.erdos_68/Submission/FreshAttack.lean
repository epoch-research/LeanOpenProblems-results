import Mathlib

/-!
An independent, partial attack on the real series sum 1/(n! - 1).
This file does not import Submission.Spec, and does not claim irrationality.
The indexing is: `partialSum n` sums the original terms 2,...,n+1.
-/

namespace FreshFactorialAttack

noncomputable def term (n : ℕ) : ℝ := 1 / ((n + 2).factorial - 1 : ℝ)
noncomputable def series : ℝ := ∑' n : ℕ, term n
noncomputable def partialSum (n : ℕ) : ℝ := ∑ k ∈ Finset.range n, term k
noncomputable def tail (n : ℕ) : ℝ := ∑' k : ℕ, term (n + k)
noncomputable def scaledPartial (n : ℕ) : ℝ := (n + 1).factorial * partialSum n

lemma factorial_ge_two (n : ℕ) : 2 ≤ (n + 2).factorial := by
  simpa using Nat.factorial_le (show 2 ≤ n + 2 by omega)

lemma denominator_pos (n : ℕ) : 0 < ((n + 2).factorial - 1 : ℝ) := by
  have h : (2 : ℝ) ≤ (n + 2).factorial := by exact_mod_cast factorial_ge_two n
  linarith

lemma denominator_ne_zero (n : ℕ) : ((n + 2).factorial - 1 : ℝ) ≠ 0 :=
  ne_of_gt (denominator_pos n)

lemma term_pos (n : ℕ) : 0 < term n := one_div_pos.mpr (denominator_pos n)

lemma denominator_succ (n : ℕ) :
    ((n + 1 + 2).factorial - 1 : ℝ) =
      (n + 3 : ℝ) * ((n + 2).factorial - 1 : ℝ) + (n + 2 : ℝ) := by
  rw [show n + 1 + 2 = (n + 2) + 1 by omega, Nat.factorial_succ]
  push_cast
  ring

lemma term_succ_le_div (n k : ℕ) :
    term (n + k + 1) ≤ term (n + k) / (n + 3 : ℝ) := by
  have hd := denominator_pos (n + k)
  have hn : (0 : ℝ) < n + 3 := by positivity
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have hle : (n + 3 : ℝ) * ((n + k + 2).factorial - 1 : ℝ) ≤
      ((n + k + 1 + 2).factorial - 1 : ℝ) := by
    rw [denominator_succ (n + k)]
    push_cast
    nlinarith
  calc
    term (n + k + 1) ≤ 1 / ((n + 3 : ℝ) * ((n + k + 2).factorial - 1 : ℝ)) :=
      one_div_le_one_div_of_le (mul_pos hn hd) hle
    _ = term (n + k) / (n + 3 : ℝ) := by simp [term, div_eq_mul_inv, mul_comm]

lemma term_tail_le_geometric (n k : ℕ) :
    term (n + k) ≤ term n * (1 / (n + 3 : ℝ)) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      calc
        term (n + (k + 1)) ≤ term (n + k) / (n + 3 : ℝ) := by
          simpa [Nat.add_assoc] using term_succ_le_div n k
        _ ≤ (term n * (1 / (n + 3 : ℝ)) ^ k) / (n + 3 : ℝ) :=
          div_le_div_of_nonneg_right ih (by positivity)
        _ = term n * (1 / (n + 3 : ℝ)) ^ (k + 1) := by rw [pow_succ]; ring

lemma summable_tail (n : ℕ) : Summable (fun k : ℕ => term (n + k)) := by
  have hr0 : (0 : ℝ) ≤ 1 / (n + 3 : ℝ) := by positivity
  have hr1 : 1 / (n + 3 : ℝ) < 1 := by
    rw [div_lt_one (by positivity : (0 : ℝ) < n + 3)]
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    linarith
  exact Summable.of_nonneg_of_le (fun k => le_of_lt (term_pos _))
    (term_tail_le_geometric n) ((summable_geometric_of_lt_one hr0 hr1).mul_left (term n))

lemma summable_term : Summable term := by simpa using summable_tail 0

lemma series_eq_partialSum_add_tail (n : ℕ) : series = partialSum n + tail n := by
  simpa [series, partialSum, tail, Nat.add_comm] using
    (summable_term.sum_add_tsum_nat_add n).symm

lemma tail_ge_term (n : ℕ) : term n ≤ tail n := by
  simpa [tail] using (summable_tail n).le_tsum 0 (fun k _ => le_of_lt (term_pos _))

lemma tail_pos (n : ℕ) : 0 < tail n := (term_pos n).trans_le (tail_ge_term n)

lemma tail_le_geometric (n : ℕ) :
    tail n ≤ term n * (1 - 1 / (n + 3 : ℝ))⁻¹ := by
  have hr0 : (0 : ℝ) ≤ 1 / (n + 3 : ℝ) := by positivity
  have hr1 : 1 / (n + 3 : ℝ) < 1 := by
    rw [div_lt_one (by positivity : (0 : ℝ) < n + 3)]
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    linarith
  calc
    tail n ≤ ∑' k : ℕ, term n * (1 / (n + 3 : ℝ)) ^ k := by
      exact (summable_tail n).tsum_le_tsum (term_tail_le_geometric n)
        ((summable_geometric_of_lt_one hr0 hr1).mul_left (term n))
    _ = term n * (1 - 1 / (n + 3 : ℝ))⁻¹ := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]

lemma factorial_gt_add_two (n : ℕ) (hn : 2 ≤ n) : n + 2 < (n + 1).factorial := by
  have hfac : 2 ≤ n.factorial := by
    simpa using Nat.factorial_le hn
  rw [Nat.factorial_succ]
  nlinarith

lemma scaled_tail_lower (n : ℕ) :
    1 / (n + 2 : ℝ) < (n + 1).factorial * tail n := by
  have hf : (0 : ℝ) < (n + 1).factorial := by exact_mod_cast Nat.factorial_pos (n + 1)
  have hd := denominator_pos n
  have hn : (0 : ℝ) < n + 2 := by positivity
  have heq : ((n + 2).factorial : ℝ) = (n + 2 : ℝ) * (n + 1).factorial := by
    rw [show n + 2 = (n + 1) + 1 by omega, Nat.factorial_succ]
    push_cast
    ring
  have hlt : 1 / (n + 2 : ℝ) < (n + 1).factorial * term n := by
    unfold term
    rw [mul_one_div, div_lt_div_iff₀ hn hd]
    nlinarith [heq]
  exact hlt.trans_le (mul_le_mul_of_nonneg_left (tail_ge_term n) hf.le)

lemma scaled_tail_upper (n : ℕ) (hn : 2 ≤ n) :
    (n + 1).factorial * tail n < 1 / (n + 1 : ℝ) := by
  have hf : (0 : ℝ) < (n + 1).factorial := by exact_mod_cast Nat.factorial_pos (n + 1)
  have hd := denominator_pos n
  have hn1 : (0 : ℝ) < n + 1 := by positivity
  have hn2 : (0 : ℝ) < n + 2 := by positivity
  have hn3 : (0 : ℝ) < n + 3 := by positivity
  have hfgt : (n + 2 : ℝ) < (n + 1).factorial := by
    exact_mod_cast factorial_gt_add_two n hn
  have heq : ((n + 2).factorial : ℝ) = (n + 2 : ℝ) * (n + 1).factorial := by
    rw [show n + 2 = (n + 1) + 1 by omega, Nat.factorial_succ]
    push_cast
    ring
  have hgeom : 1 - 1 / (n + 3 : ℝ) = (n + 2 : ℝ) / (n + 3 : ℝ) := by
    field_simp
    ring
  have hlt : (n + 1).factorial * (term n * (1 - 1 / (n + 3 : ℝ))⁻¹) <
      1 / (n + 1 : ℝ) := by
    rw [hgeom]
    unfold term
    rw [inv_div]
    have h1 : (n + 1 : ℝ) ≠ 0 := ne_of_gt hn1
    have h2 : (n + 2 : ℝ) ≠ 0 := ne_of_gt hn2
    have h3 : ((n + 2).factorial - 1 : ℝ) ≠ 0 := ne_of_gt hd
    apply (lt_div_iff₀ hn1).2
    field_simp
    nlinarith [heq]
  exact (mul_le_mul_of_nonneg_left (tail_le_geometric n) hf.le).trans_lt hlt


/-- Integer denominators, never zero on this indexing. -/
def denominator (n : ℕ) : ℕ := (n + 2).factorial - 1

lemma denominator_nat_pos (n : ℕ) : 0 < denominator n := by
  have := factorial_ge_two n
  unfold denominator
  omega

lemma denominator_cast (n : ℕ) : (denominator n : ℝ) = ((n + 2).factorial - 1 : ℝ) := by
  unfold denominator
  rw [Nat.cast_sub (by have := factorial_ge_two n; omega)]
  norm_num

lemma denominator_nat_succ (n : ℕ) :
    denominator (n + 1) = (n + 3) * denominator n + (n + 2) := by
  have hf := factorial_ge_two n
  unfold denominator
  rw [show n + 1 + 2 = (n + 2) + 1 by omega, Nat.factorial_succ]
  have hsub : (n + 2).factorial - 1 + 1 = (n + 2).factorial := by omega
  rw [← hsub, Nat.mul_add]
  simp only [Nat.mul_one, Nat.add_sub_cancel]
  omega

lemma common_divisor_eq_one (n d : ℕ) (h0 : d ∣ denominator n)
    (h1 : d ∣ denominator (n + 1)) : d = 1 := by
  have hsmall : d ∣ n + 2 := by
    have h := Nat.dvd_sub h1 (dvd_mul_of_dvd_right h0 (n + 3))
    simpa [denominator_nat_succ] using h
  have hfac : d ∣ (n + 2).factorial :=
    hsmall.trans (Nat.dvd_factorial (by omega) (le_refl _))
  have h := Nat.dvd_sub hfac h0
  have heq : (n + 2).factorial - denominator n = 1 := by
    have := factorial_ge_two n
    unfold denominator
    omega
  rw [heq] at h
  exact Nat.dvd_one.mp h

lemma consecutive_denominators_coprime (n : ℕ) :
    (denominator n).Coprime (denominator (n + 1)) := by
  apply Nat.coprime_iff_gcd_eq_one.mpr
  exact common_divisor_eq_one n _ (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_right _ _)

lemma clearing_two_denominators_lower_bound (n D : ℕ) (hD : 0 < D)
    (h0 : denominator n ∣ D) (h1 : denominator (n + 1) ∣ D) :
    (denominator n : ℝ) / (n + 5 : ℝ) < (D : ℝ) * tail (n + 2) := by
  have hprod : denominator n * denominator (n + 1) ≤ D :=
    Nat.le_of_dvd hD ((consecutive_denominators_coprime n).mul_dvd_of_dvd_of_dvd h0 h1)
  have hp : (0 : ℝ) < denominator n := by exact_mod_cast denominator_nat_pos n
  have hp1 : (0 : ℝ) < denominator (n + 1) := by exact_mod_cast denominator_nat_pos (n + 1)
  have hd := denominator_pos (n + 2)
  have hn5 : (0 : ℝ) < n + 5 := by positivity
  have hfgt : (n + 4 : ℝ) < (n + 3).factorial := by
    have h := factorial_gt_add_two (n + 2) (by omega)
    exact_mod_cast h
  have heq : ((n + 4).factorial : ℝ) = (n + 4 : ℝ) * (n + 3).factorial := by
    rw [show n + 4 = (n + 3) + 1 by omega, Nat.factorial_succ]
    push_cast
    ring
  have hratio : 1 / (n + 5 : ℝ) < (denominator (n + 1) : ℝ) * term (n + 2) := by
    rw [denominator_cast]
    unfold term
    rw [mul_one_div, div_lt_div_iff₀ hn5 hd]
    norm_num [Nat.add_assoc] at *
    nlinarith [heq]
  calc
    (denominator n : ℝ) / (n + 5 : ℝ) = (denominator n : ℝ) * (1 / (n + 5 : ℝ)) := by ring
    _ < (denominator n : ℝ) * ((denominator (n + 1) : ℝ) * term (n + 2)) :=
      mul_lt_mul_of_pos_left hratio hp
    _ = ((denominator n * denominator (n + 1) : ℕ) : ℝ) * term (n + 2) := by push_cast; ring
    _ ≤ (D : ℝ) * term (n + 2) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hprod) (term_pos _).le
    _ ≤ (D : ℝ) * tail (n + 2) := by
      gcongr
      exact tail_ge_term (n + 2)

lemma clearing_two_denominators_tail_gt_one (n D : ℕ) (hn : 2 ≤ n) (hD : 0 < D)
    (h0 : denominator n ∣ D) (h1 : denominator (n + 1) ∣ D) :
    1 < (D : ℝ) * tail (n + 2) := by
  have hfac : 6 ≤ (n + 1).factorial := by
    simpa using Nat.factorial_le (show 3 ≤ n + 1 by omega)
  have hfactor : (n + 2).factorial = (n + 2) * (n + 1).factorial := by
    simpa [Nat.add_assoc] using Nat.factorial_succ (n + 1)
  have hnum : n + 5 < denominator n := by
    have hf := factorial_ge_two n
    unfold denominator
    have hsub : (n + 2).factorial - 1 + 1 = (n + 2).factorial := by omega
    nlinarith
  have hlt : 1 < (denominator n : ℝ) / (n + 5 : ℝ) := by
    rw [one_lt_div (by positivity : (0 : ℝ) < n + 5)]
    exact_mod_cast hnum
  exact hlt.trans (clearing_two_denominators_lower_bound n D hD h0 h1)

/-- The finite-arithmetic window forced by rationality. -/
def InRationalityWindow (n : ℕ) : Prop :=
  1 - 1 / (n + 1 : ℝ) < Int.fract (scaledPartial n) ∧
    Int.fract (scaledPartial n) < 1 - 1 / (n + 2 : ℝ)

lemma rational_scaled_is_integer (q : ℚ) (n : ℕ) (hn : q.den ≤ n + 1) :
    ∃ z : ℤ, ((n + 1).factorial : ℝ) * (q : ℝ) = z := by
  obtain ⟨k, hk⟩ := Nat.dvd_factorial q.den_pos hn
  refine ⟨q.num * (k : ℤ), ?_⟩
  have hq : (q.den : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt q.den_pos)
  rw [Rat.cast_def, hk]
  push_cast
  field_simp

lemma scaled_integer_implies_window (n : ℕ) (hn : 2 ≤ n) (z : ℤ)
    (hz : ((n + 1).factorial : ℝ) * series = z) : InRationalityWindow n := by
  have hlow := scaled_tail_lower n
  have hupp := scaled_tail_upper n hn
  have ht0 : (0 : ℝ) < (n + 1).factorial * tail n := by
    exact mul_pos (by exact_mod_cast Nat.factorial_pos (n + 1)) (tail_pos n)
  have ht1 : ((n + 1).factorial : ℝ) * tail n < 1 := by
    have hle : 1 / (n + 1 : ℝ) ≤ 1 := by
      rw [div_le_one (by positivity : (0 : ℝ) < n + 1)]
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg _
      linarith
    exact hupp.trans_le hle
  have hsum : scaledPartial n + (n + 1).factorial * tail n = (z : ℝ) := by
    rw [scaledPartial, ← mul_add, ← series_eq_partialSum_add_tail, hz]
  have hfract : Int.fract (scaledPartial n) = 1 - (n + 1).factorial * tail n := by
    apply Int.fract_eq_iff.mpr
    refine ⟨by linarith, by linarith, z - 1, ?_⟩
    push_cast
    linarith
  unfold InRationalityWindow
  rw [hfract]
  constructor <;> linarith

lemma rational_implies_eventual_window (h : ¬ Irrational series) :
    ∃ N : ℕ, ∀ n ≥ N, InRationalityWindow n := by
  obtain ⟨q, hq⟩ := exists_rat_of_not_irrational h
  refine ⟨max 2 q.den, ?_⟩
  intro n hn
  obtain ⟨z, hz⟩ := rational_scaled_is_integer q n (by omega)
  apply scaled_integer_implies_window n (by omega) z
  rw [hq]
  exact hz

/-- This is a proved reduction, NOT an assertion of its hypothesis. -/
theorem irrational_of_arbitrarily_large_window_failures
    (h : ∀ N : ℕ, ∃ n ≥ N, ¬ InRationalityWindow n) : Irrational series := by
  by_contra hr
  obtain ⟨N, hN⟩ := rational_implies_eventual_window hr
  obtain ⟨n, hn, hbad⟩ := h N
  exact hbad (hN n hn)


noncomputable def rounded (n : ℕ) : ℤ := ⌊scaledPartial n⌋ + 1

lemma rounded_error_bound (n : ℕ) (hn : 2 ≤ n) (hw : InRationalityWindow n) :
    |((n + 1).factorial : ℝ) * series - (rounded n : ℝ)| <
      1 / ((n + 1 : ℝ) * (n + 2 : ℝ)) := by
  have hlow := scaled_tail_lower n
  have hupp := scaled_tail_upper n hn
  rcases hw with ⟨hwlow, hwupp⟩
  have hsum : scaledPartial n + (n + 1).factorial * tail n =
      ((n + 1).factorial : ℝ) * series := by
    rw [scaledPartial, ← mul_add, ← series_eq_partialSum_add_tail]
  have hdiff : 1 / (n + 1 : ℝ) - 1 / (n + 2 : ℝ) =
      1 / ((n + 1 : ℝ) * (n + 2 : ℝ)) := by
    field_simp
    ring
  unfold Int.fract at hwlow hwupp
  unfold rounded
  push_cast
  rw [abs_lt, ← hdiff]
  constructor <;> linarith

lemma scaled_factorial_succ (n : ℕ) (x : ℝ) :
    ((n + 1 + 1).factorial : ℝ) * x =
      (n + 2 : ℝ) * (((n + 1).factorial : ℝ) * x) := by
  rw [Nat.factorial_succ]
  push_cast
  ring

lemma window_forces_zero_carry (n : ℕ) (hn : 2 ≤ n)
    (hw : InRationalityWindow n) (hw1 : InRationalityWindow (n + 1)) :
    rounded (n + 1) = (n + 2 : ℤ) * rounded n := by
  have h0 := rounded_error_bound n hn hw
  have h1 := rounded_error_bound (n + 1) (by omega) hw1
  have hsmall : (n + 2 : ℝ) / ((n + 1 : ℝ) * (n + 2 : ℝ)) +
      1 / ((n + 2 : ℝ) * (n + 3 : ℝ)) < 1 := by
    have hnreal : (2 : ℝ) ≤ n := by exact_mod_cast hn
    field_simp
    nlinarith [sq_nonneg (n : ℝ)]
  have hEq : ((rounded (n + 1) - (n + 2 : ℤ) * rounded n : ℤ) : ℝ) =
      (n + 2 : ℝ) * (((n + 1).factorial : ℝ) * series - (rounded n : ℝ)) -
      (((n + 1 + 1).factorial : ℝ) * series - (rounded (n + 1) : ℝ)) := by
    rw [scaled_factorial_succ]
    push_cast
    ring
  have hbound : |((rounded (n + 1) - (n + 2 : ℤ) * rounded n : ℤ) : ℝ)| < 1 := by
    rw [hEq]
    calc
      _ ≤ |(n + 2 : ℝ) * (((n + 1).factorial : ℝ) * series - (rounded n : ℝ))| +
          |((n + 1 + 1).factorial : ℝ) * series - (rounded (n + 1) : ℝ)| := abs_sub _ _
      _ = (n + 2 : ℝ) * |((n + 1).factorial : ℝ) * series - (rounded n : ℝ)| +
          |((n + 1 + 1).factorial : ℝ) * series - (rounded (n + 1) : ℝ)| := by
        rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < n + 2)]
      _ < (n + 2 : ℝ) / ((n + 1 : ℝ) * (n + 2 : ℝ)) +
          1 / ((n + 2 : ℝ) * (n + 3 : ℝ)) := by
        have hh := add_lt_add (mul_lt_mul_of_pos_left h0 (by positivity : (0 : ℝ) < n + 2)) h1
        convert hh using 1
        norm_num [Nat.cast_add, Nat.cast_one, add_assoc, div_eq_mul_inv]
      _ < 1 := hsmall
  have hz : |rounded (n + 1) - (n + 2 : ℤ) * rounded n| < 1 := by
    exact_mod_cast hbound
  exact sub_eq_zero.mp (Int.abs_lt_one_iff.mp hz)

lemma eventual_window_implies_rational
    (h : ∃ N : ℕ, ∀ n ≥ N, InRationalityWindow n) : ¬ Irrational series := by
  obtain ⟨N0, hN0⟩ := h
  let N := max 2 N0
  let q : ℚ := (rounded N : ℚ) / ((N + 1).factorial : ℚ)
  have hN : ∀ n ≥ N, InRationalityWindow n := by
    intro n hn
    exact hN0 n (le_trans (le_max_right _ _) hn)
  have hNtwo : 2 ≤ N := le_max_left _ _
  have hstart : (rounded N : ℝ) = ((N + 1).factorial : ℝ) * (q : ℝ) := by
    dsimp [q]
    push_cast
    have hf : ((N + 1).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (N + 1)
    field_simp
  have hround : ∀ n ≥ N, (rounded n : ℝ) = ((n + 1).factorial : ℝ) * (q : ℝ) := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => exact hstart
    | succ n hn ih =>
      have hc := window_forces_zero_carry n (le_trans hNtwo hn) (hN n hn) (hN (n + 1) (by omega))
      rw [hc]
      push_cast
      rw [ih, scaled_factorial_succ]
  have hseries : series = (q : ℝ) := by
    by_contra hne
    have hpos : 0 < |series - (q : ℝ)| := abs_pos.mpr (sub_ne_zero.mpr hne)
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt hpos
    let n := max N m
    have hn : N ≤ n := le_max_left _ _
    have hnm : m ≤ n := le_max_right _ _
    have herr := rounded_error_bound n (le_trans hNtwo hn) (hN n hn)
    rw [hround n hn, ← mul_sub, abs_mul] at herr
    have hf : (0 : ℝ) < (n + 1).factorial := by exact_mod_cast Nat.factorial_pos (n + 1)
    rw [abs_of_pos hf] at herr
    have hfacge : (1 : ℝ) ≤ (n + 1).factorial := by
      exact_mod_cast (Nat.succ_le_of_lt (Nat.factorial_pos (n + 1)))
    have hnreal : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    have hwidth : 1 / ((n + 1 : ℝ) * (n + 2 : ℝ)) ≤ 1 / (n + 1 : ℝ) := by
      apply one_div_le_one_div_of_le (by positivity)
      nlinarith
    have herror : |series - (q : ℝ)| < 1 / (n + 1 : ℝ) := by
      have hprod : |series - (q : ℝ)| ≤
          ((n + 1).factorial : ℝ) * |series - (q : ℝ)| := by nlinarith
      exact (hprod.trans_lt herr).trans_le hwidth
    have hrecip : 1 / (n + 1 : ℝ) ≤ 1 / (m + 1 : ℝ) := by
      apply one_div_le_one_div_of_le (by positivity)
      exact_mod_cast Nat.add_le_add_right hnm 1
    exact (not_lt_of_ge (le_trans hrecip hm.le)) herror
  intro hi
  exact hi ⟨q, hseries.symm⟩

/-- Exact reduction of irrationality to a statement about finite rational sums. -/
theorem irrational_iff_arbitrarily_large_window_failures :
    Irrational series ↔ ∀ N : ℕ, ∃ n ≥ N, ¬ InRationalityWindow n := by
  constructor
  · intro hi
    by_contra h
    push_neg at h
    exact (eventual_window_implies_rational h) hi
  · exact irrational_of_arbitrarily_large_window_failures


/-- The geometric expansion has a strictly positive, explicitly nonzero remainder. -/
lemma finite_geometric_expansion (n K : ℕ) :
    term n = (∑ j ∈ Finset.range K, 1 / (((n + 2).factorial : ℝ) ^ (j + 1))) +
      1 / ((((n + 2).factorial : ℝ) ^ K) * ((n + 2).factorial - 1 : ℝ)) := by
  have hf : ((n + 2).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (n + 2)
  have hd := denominator_ne_zero n
  induction K with
  | zero => simp [term]
  | succ K ih =>
    rw [Finset.sum_range_succ, ih]
    have heq : 1 / ((((n + 2).factorial : ℝ) ^ K) * ((n + 2).factorial - 1 : ℝ)) =
        1 / (((n + 2).factorial : ℝ) ^ (K + 1)) +
        1 / ((((n + 2).factorial : ℝ) ^ (K + 1)) * ((n + 2).factorial - 1 : ℝ)) := by
      rw [pow_succ]
      field_simp
      ring
    linarith

lemma finite_geometric_remainder_pos (n K : ℕ) :
    0 < term n - ∑ j ∈ Finset.range K, 1 / (((n + 2).factorial : ℝ) ^ (j + 1)) := by
  rw [finite_geometric_expansion n K, add_sub_cancel_left]
  apply one_div_pos.mpr
  apply mul_pos
  · apply pow_pos
    exact_mod_cast Nat.factorial_pos (n + 2)
  · exact denominator_pos n


/-- The reduction with the exact expression occurring in the original target. -/
theorem original_series_criterion :
    Irrational (∑' n : ℕ, 1 / ((n + 2).factorial - 1 : ℝ)) ↔
      ∀ N : ℕ, ∃ n ≥ N, ¬ InRationalityWindow n := by
  simpa only [series, term] using irrational_iff_arbitrarily_large_window_failures

end FreshFactorialAttack
