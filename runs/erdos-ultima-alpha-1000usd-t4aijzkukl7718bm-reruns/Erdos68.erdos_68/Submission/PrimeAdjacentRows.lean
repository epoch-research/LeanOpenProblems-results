import Submission.PrimeMultiplierRowRemainder
import Submission.RowGcdEquality

/-!
Two adjacent rows give a rowwise remainder strictly greater than one on an
infinite prime subsequence. This does not by itself settle Erdős 68.
-/

namespace PrimeAdjacentRows

open Erdos68Development RowRemainderBounds PrimeRowRemainder

lemma catalan_even_at_odd_prime (p : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p) :
    2 ∣ catalan (p-1) := by
  have h := Nat.two_dvd_centralBinom_of_one_le (show 0 < p-1 by omega)
  rw [← succ_mul_catalan_eq_centralBinom, Nat.sub_add_cancel hp.pos] at h
  rcases Nat.prime_two.dvd_mul.mp h with h | h
  · have ho := hp.eq_two_or_odd.resolve_left (by omega)
    have := Nat.mod_eq_zero_of_dvd h
    omega
  · exact h

lemma successor_dvd_catalan (p : ℕ) (hp : p.Prime) (hm : p % 12 = 1) :
    p+1 ∣ catalan (p-1) := by
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  obtain ⟨d, hd⟩ := catalan_even_at_odd_prime p hp hp3
  let k := p/12
  let m := 6*k+1
  have hpform : p = 12*k+1 := by dsimp [k]; omega
  have hp1 : p+1 = 2*m := by dsimp [m]; omega
  have hp2 : 2*p-1 = 24*k+1 := by omega
  have hcentral := central_eq_catalan p hp.pos
  have hdiv : p+1 ∣ 2*(2*p-1)*catalan (p-1) := by
    rw [← hcentral, ← succ_mul_catalan_eq_centralBinom p]
    exact dvd_mul_right _ _
  have hmain : m ∣ 2*(24*k+1)*d := by
    rw [hp1, hp2, hd] at hdiv
    have he : 2*(24*k+1)*(2*d) = 2*(2*(24*k+1)*d) := by ring
    rw [he] at hdiv
    exact (Nat.mul_dvd_mul_iff_left (by decide : 0 < 2)).mp hdiv
  have h6 : m ∣ 6*d := by
    have hmul : m ∣ 8*m*d := by exact ⟨8*d, by ring⟩
    have he : 8*m*d = 2*(24*k+1)*d+6*d := by dsimp [m]; ring
    rw [he] at hmul
    exact (Nat.dvd_add_iff_right hmain).mpr hmul
  have hmd : m ∣ d := by
    have hmul : m ∣ m*d := dvd_mul_right _ _
    have he : m*d = k*(6*d)+d := by dsimp [m]; ring
    rw [he] at hmul
    exact (Nat.dvd_add_iff_right (dvd_mul_of_dvd_right h6 k)).mpr hmul
  rw [hp1, hd]
  exact Nat.mul_dvd_mul_left 2 hmd

lemma successor_quotient_properties (p : ℕ) (hp : p.Prime) (hm : p % 12 = 1) :
    ∃ a : ℕ, catalan (p-1) = (p+1)*a ∧ p ∣ a+1 ∧
      a < (p+1).factorial-1 := by
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  obtain ⟨a, ha⟩ := successor_dvd_catalan p hp hm
  refine ⟨a, ha, ?_, ?_⟩
  · have h := catalan_add_one_dvd p hp (by omega)
    rw [ha, show (p+1)*a+1 = p*a+(a+1) by ring] at h
    exact (Nat.dvd_add_iff_right (dvd_mul_right p a)).mpr h
  · have h := central_lt_factorial p hp3
    rw [← succ_mul_catalan_eq_centralBinom (p-1), Nat.sub_add_cancel hp.pos] at h
    have hc : catalan (p-1) < p.factorial-1 := Nat.lt_of_mul_lt_mul_left h
    have hle : a ≤ catalan (p-1) := by rw [ha]; nlinarith
    have hf := Nat.factorial_le (show p ≤ p+1 by omega)
    omega

lemma factorial_ratio_successor (p a : ℕ) (hp : 0 < p)
    (ha : catalan (p-1) = (p+1)*a) :
    ((2*p-2).factorial : ℝ) / ((p+1).factorial : ℝ)^2 =
      (a : ℝ)/((p : ℝ)*(p+1)) := by
  have he := factorial_ratio_eq p hp
  rw [ha, Nat.cast_mul, Nat.cast_add, Nat.cast_one] at he
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have hpR : (p : ℝ) ≠ 0 := by positivity
  have hfR : (p.factorial : ℝ) ≠ 0 := by positivity
  have hp1R : (p : ℝ)+1 ≠ 0 := by positivity
  field_simp at he ⊢
  nlinarith

/-- The next row also has a uniformly controlled positive residue. -/
theorem successor_row_lower (p : ℕ) (hp : p.Prime) (hm : p % 12 = 1) :
    ((p : ℝ)-1)/((p : ℝ)*(p+1)) < rowRemainder (2*p-2) (p+1) := by
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  obtain ⟨a, ha, hap, hasmall⟩ := successor_quotient_properties p hp hm
  let D := p*(p+1)
  let r := a % D
  have hDpos : 0 < D := by dsimp [D]; positivity
  have hpD : p ∣ D := dvd_mul_right _ _
  have har : p ∣ r+1 := by
    have he := Nat.mod_add_div a D
    have h : p ∣ (r+1)+D*(a/D) := by
      convert hap using 1
      dsimp [r]
      omega
    exact (Nat.dvd_add_iff_left (dvd_mul_of_dvd_left hpD (a/D))).mpr h
  have hrlo : p-1 ≤ r := by
    have h := Nat.le_of_dvd (by omega : 0 < r+1) har
    omega
  have hrhi : r+1 ≤ D := by dsimp [r]; have := Nat.mod_lt a hDpos; omega
  have hratio := factorial_ratio_successor p a hp.pos ha
  have hDR : (0 : ℝ) < D := by exact_mod_cast hDpos
  have hf2 : (2 : ℝ) ≤ (p+1).factorial := by
    exact_mod_cast (show 2 ≤ (p+1).factorial by simpa using Nat.factorial_le (show 2 ≤ p+1 by omega))
  have hfpos : (0 : ℝ) < (p+1).factorial-1 := by linarith
  let eps : ℝ := ((2*p-2).factorial : ℝ) /
    (((p+1).factorial : ℝ)^2*((p+1).factorial-1))
  have heps0 : 0 < eps := by dsimp [eps]; positivity
  have heps : eps = (a : ℝ)/((D : ℝ)*((p+1).factorial-1)) := by
    dsimp [eps]
    rw [← div_div, hratio, div_div]
    simp [D]
  have heps1 : eps < 1/(D : ℝ) := by
    have hsmall : (a : ℝ) < (p+1).factorial-1 := by
      have hh : (a : ℝ)+1 < (p+1).factorial := by
        exact_mod_cast (show a+1 < (p+1).factorial by omega)
      linarith
    rw [heps]
    apply (div_lt_div_iff₀ (mul_pos hDR hfpos) hDR).mpr
    nlinarith
  have hdiv : (a : ℝ)/(D : ℝ) = (a/D : ℕ)+(r : ℝ)/(D : ℝ) := by
    have he : (r : ℝ)+(D : ℝ)*(a/D : ℕ) = (a : ℝ) := by
      exact_mod_cast Nat.mod_add_div a D
    apply (div_eq_iff hDR.ne').mpr
    field_simp
    nlinarith
  obtain ⟨I, hI⟩ := PrimeMultiplierRowRemainder.geometric_decomposition
    (2*p-2) (p+1) 2 (by omega) (by omega) (by omega)
  have htotal : ((2*p-2).factorial : ℝ)/((p+1).factorial-1) =
      ((I+a/D : ℕ) : ℝ)+((r : ℝ)/(D : ℝ)+eps) := by
    rw [hI, hratio]
    change (I : ℝ)+(a : ℝ)/((p : ℝ)*(p+1))+eps = _
    have hcast : (D : ℝ) = (p : ℝ)*(p+1) := by simp [D]
    rw [← hcast, hdiv, Nat.cast_add]
    ring
  have hfrac0 : 0 ≤ (r : ℝ)/(D : ℝ)+eps := by positivity
  have hfrac1 : (r : ℝ)/(D : ℝ)+eps < 1 := by
    have hr : (r : ℝ)+1 ≤ D := by exact_mod_cast hrhi
    have hh : (r : ℝ)/(D : ℝ)+1/(D : ℝ) ≤ 1 := by
      rw [← add_div]
      exact (div_le_one hDR).mpr hr
    linarith
  have hrow : rowRemainder (2*p-2) (p+1) = (r : ℝ)/(D : ℝ)+eps := by
    unfold rowRemainder
    rw [htotal, Int.fract_natCast_add, Int.fract_eq_self.mpr ⟨hfrac0, hfrac1⟩]
  rw [hrow]
  have hr : (p : ℝ)-1 ≤ r := by
    have hh : ((p-1 : ℕ) : ℝ) ≤ r := by exact_mod_cast hrlo
    simpa only [Nat.cast_sub hp.pos, Nat.cast_one] using hh
  have hle := div_le_div_of_nonneg_right hr hDR.le
  have hcast : (D : ℝ) = (p : ℝ)*(p+1) := by simp [D]
  rw [hcast] at hle
  rw [hcast]
  linarith


lemma scaled_omitted_tail_lower (n : ℕ) (hn : 2 ≤ n) :
    1/(n+1 : ℝ) < (n.factorial : ℝ)*
      ((∑' k : ℕ, term k)-∑ k ∈ Finset.range (n-1), term k) := by
  have h := (partial_sum_error n).1
  rw [show n = (n-1)+1 by omega, Finset.sum_range_succ] at h
  have hterm : term (n-1) <
      (∑' k : ℕ, term k)-∑ k ∈ Finset.range (n-1), term k := by linarith
  have hmul := mul_lt_mul_of_pos_left hterm (show (0 : ℝ) < n.factorial by positivity)
  have hden : (0 : ℝ) < (n+1).factorial-1 := by
    have hh : (2 : ℝ) ≤ (n+1).factorial := by
      exact_mod_cast (show 2 ≤ (n+1).factorial by simpa using Nat.factorial_le (show 2 ≤ n+1 by omega))
    linarith
  have hn1 : (0 : ℝ) < n+1 := by positivity
  have hfirst : 1/(n+1 : ℝ) < (n.factorial : ℝ)*term (n-1) := by
    simp only [term, show n-1+2 = n+1 by omega, mul_one_div]
    apply (div_lt_div_iff₀ hn1 hden).mpr
    rw [Nat.factorial_succ]
    push_cast
    nlinarith
  exact hfirst.trans hmul

lemma two_rows_tail_lower (n a b : ℕ) (hn : 2 ≤ n)
    (ha : a ∈ Finset.Ico 2 (n+1)) (hb : b ∈ Finset.Ico 2 (n+1)) (hab : a ≠ b) :
    rowRemainder n a + rowRemainder n b + 1/(n+1 : ℝ) < rowTail n := by
  have hsub : ({a,b} : Finset ℕ) ⊆ Finset.Ico 2 (n+1) := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl
    · exact ha
    · exact hb
  have hs := Finset.sum_le_sum_of_subset_of_nonneg (f := rowRemainder n) hsub
    (fun _ _ _ => Int.fract_nonneg _)
  rw [Finset.sum_pair hab, rowRemainder_sum n hn] at hs
  have ht := scaled_omitted_tail_lower n hn
  unfold rowTail
  nlinarith

/-- On this prime progression the actual rowwise remainder is strictly
larger than one. Positive integral remainders are still possible. -/
theorem tail_gt_one (p : ℕ) (hp : p.Prime) (hm : p % 12 = 1) :
    1 < rowTail (2*p-2) := by
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hpR : (0 : ℝ) < p := by positivity
  have hp1R : (0 : ℝ) < p+1 := by positivity
  have hp2R : (0 : ℝ) < 2*(p : ℝ)-1 := by exact_mod_cast (show (0 : ℤ) < 2*(p : ℤ)-1 by omega)
  have ht := two_rows_tail_lower (2*p-2) p (p+1) (by omega)
    (Finset.mem_Ico.mpr ⟨by omega, by omega⟩)
    (Finset.mem_Ico.mpr ⟨by omega, by omega⟩) (by omega)
  have hfirst := row_gt_one_sub_inv p hp (by omega)
  have hsecond := successor_row_lower p hp hm
  have hcast : ((2*p-2 : ℕ) : ℝ)+1 = 2*(p : ℝ)-1 := by
    rw [Nat.cast_sub (by omega : 2 ≤ 2*p)]
    push_cast
    ring
  rw [hcast] at ht
  have he : -1/(p : ℝ) + ((p : ℝ)-1)/((p : ℝ)*(p+1)) =
      -2/((p : ℝ)*(p+1)) := by field_simp; ring
  have hi : 2/((p : ℝ)*(p+1)) < 1/(2*(p : ℝ)-1) := by
    apply (div_lt_div_iff₀ (mul_pos hpR hp1R) hp2R).mpr
    have hp3R : (3 : ℝ) ≤ p := by exact_mod_cast hp3
    nlinarith
  simp only [neg_div] at he
  linarith

/-- Dirichlet's theorem supplies arbitrarily late indices for the strict
lower bound. This is not an infinite GCD-defect theorem. -/
theorem frequently_tail_gt_one (N : ℕ) :
    ∃ p ≥ N, p.Prime ∧ p % 12 = 1 ∧ 1 < rowTail (2*p-2) := by
  obtain ⟨p, hlarge, hp, hm⟩ := Nat.forall_exists_prime_gt_and_modEq N
    (q := 12) (a := 1) (by decide) (by decide)
  have hm' : p % 12 = 1 := by simpa only [Nat.ModEq, Nat.reduceMod] using hm
  exact ⟨p, hlarge.le, hp, hm', tail_gt_one p hp hm'⟩

/-- A remaining sufficient arithmetic condition, NOT proved here. -/
theorem irrational_of_frequent_coprime_rows
    (h : ∀ M : ℕ, ∃ p ≥ M, p.Prime ∧ p % 12 = 1 ∧
      RowGcdCriterion.rowGcd (2*p-2) = 1) :
    Irrational (∑' k : ℕ, term k) := by
  rintro ⟨q, hq⟩
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    (RowGcdEquality.rowGcd_eventually_eq_tail_of_rational q hq.symm)
  obtain ⟨p, hlarge, hp, hm, hg⟩ := h (N+2)
  have he := hN (2*p-2) (by omega)
  have ht := tail_gt_one p hp hm
  rw [hg] at he
  norm_num only [Nat.cast_one] at he
  linarith

#print axioms successor_dvd_catalan
#print axioms successor_row_lower
#print axioms tail_gt_one
#print axioms frequently_tail_gt_one
#print axioms irrational_of_frequent_coprime_rows

end PrimeAdjacentRows
