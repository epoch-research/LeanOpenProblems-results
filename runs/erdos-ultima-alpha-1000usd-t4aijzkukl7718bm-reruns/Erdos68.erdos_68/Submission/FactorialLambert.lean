import Submission.Development

/-!
# Factorial regrouping of the Erdős 68 series

This development proves an integer-coefficient factorial-series identity, with
coefficient 1 at every prime index. The coefficients exceed the allowed digit
range at every sufficiently large even index, so the usual bounded-digit
irrationality argument does not apply. This file does not settle the conjecture.
-/

set_option maxHeartbeats 1000000

namespace Erdos68Development

def lambertCoeff (m : ℕ) : ℕ :=
  ∑ d ∈ m.divisors, if 2 ≤ d then m.factorial / d.factorial ^ (m / d) else 0

lemma factorial_pow_dvd_factorial_mul (d k : ℕ) :
    d.factorial ^ k ∣ (d * k).factorial := by
  simpa [Nat.mul_comm] using
    Nat.prod_factorial_dvd_factorial_sum (Finset.range k) (fun _ => d)

lemma lambertCoeff_divisible {d m : ℕ} (hd : d ∣ m) :
    d.factorial ^ (m / d) ∣ m.factorial := by
  simpa [Nat.mul_div_cancel' hd] using factorial_pow_dvd_factorial_mul d (m / d)

lemma lambertCoeff_prime {p : ℕ} (hp : p.Prime) : lambertCoeff p = 1 := by
  simp [lambertCoeff, hp.divisors, hp.two_le, hp.ne_one.symm, Nat.div_self hp.pos,
    Nat.div_self (Nat.factorial_pos p)]

lemma lambertCoeff_even_lower (k : ℕ) (hk : 0 < k) :
    (2 * k).factorial / 2 ^ k ≤ lambertCoeff (2 * k) := by
  have hmem : 2 ∈ (2 * k).divisors :=
    Nat.mem_divisors.mpr ⟨by omega, by positivity⟩
  have h := Finset.single_le_sum
    (f := fun d => if 2 ≤ d then (2 * k).factorial / d.factorial ^ (2 * k / d) else 0)
    (fun d _ => Nat.zero_le _) hmem
  simpa [lambertCoeff, Nat.factorial] using h

lemma even_factorial_lower (k : ℕ) :
    2 * (k + 2) * 2 ^ (k + 2) ≤ (2 * (k + 2)).factorial := by
  induction k with
  | zero => norm_num [Nat.factorial]
  | succ k ih =>
    rw [show k + 1 + 2 = (k + 2) + 1 by omega, pow_succ]
    rw [show 2 * (k + 2 + 1) = (2 * (k + 2) + 1) + 1 by omega,
      Nat.factorial_succ, Nat.factorial_succ]
    calc
      _ ≤ (2 * (k + 2) + 1 + 1) * ((2 * (k + 2) + 1) *
          (2 * (k + 2) * 2 ^ (k + 2))) := by
        apply Nat.mul_le_mul_left
        have h : 2 ≤ (2 * (k + 2) + 1) * (2 * (k + 2)) := by nlinarith
        have hh := Nat.mul_le_mul_right (2 ^ (k + 2)) h
        simpa only [Nat.mul_assoc, Nat.mul_comm (2 ^ (k + 2)) 2] using hh
      _ ≤ _ := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ ih)

lemma lambertCoeff_even_ge (k : ℕ) :
    2 * (k + 2) ≤ lambertCoeff (2 * (k + 2)) := by
  calc
    _ ≤ (2 * (k + 2)).factorial / 2 ^ (k + 2) :=
      (Nat.le_div_iff_mul_le (by positivity)).mpr (even_factorial_lower k)
    _ ≤ _ := lambertCoeff_even_lower _ (by omega)

noncomputable def termNat (n : ℕ) : ℝ :=
  if 2 ≤ n then 1 / (n.factorial - 1 : ℝ) else 0

lemma termNat_add_two (n : ℕ) : termNat (n + 2) = term n := by
  simp [termNat, term]

lemma summable_termNat : Summable termNat := by
  apply (summable_nat_add_iff 2).mp
  simpa only [termNat_add_two] using summable_term

lemma tsum_termNat : (∑' n : ℕ, termNat n) = ∑' n : ℕ, term n := by
  have h := summable_termNat.sum_add_tsum_nat_add 2
  simpa [Finset.sum_range_succ, termNat_add_two, termNat, term] using h.symm

noncomputable def lambertPair (p : ℕ+ × ℕ+) : ℝ :=
  if 2 ≤ (p.1 : ℕ) then 1 / ((p.1 : ℕ).factorial : ℝ) ^ (p.2 : ℕ) else 0

lemma lambertPair_inner (d : ℕ+) :
    Summable (fun j : ℕ+ => lambertPair (d, j)) ∧
      (∑' j : ℕ+, lambertPair (d, j)) = termNat d := by
  by_cases hd : 2 ≤ (d : ℕ)
  · have he : (d : ℕ) = ((d : ℕ) - 2) + 2 := by omega
    simp only [lambertPair, if_pos hd]
    constructor
    · rw [summable_pnat_iff_summable_succ (f := fun j : ℕ => 1 / ((d : ℕ).factorial : ℝ) ^ j)]
      simpa [lambertPair, hd, powerTerm, ← he] using
        summable_powerTerm_orders ((d : ℕ) - 2)
    · rw [tsum_pnat_eq_tsum_succ (f := fun j : ℕ => 1 / ((d : ℕ).factorial : ℝ) ^ j)]
      simpa [lambertPair, hd, powerTerm, termNat, term, ← he] using
        sum_powerTerm_orders ((d : ℕ) - 2)
  · constructor
    · simpa [lambertPair, hd] using (summable_zero : Summable (fun _ : ℕ+ => (0 : ℝ)))
    · simp [lambertPair, termNat, hd]

lemma summable_lambertPair : Summable lambertPair := by
  apply (summable_prod_of_nonneg (fun p => by unfold lambertPair; split_ifs <;> positivity)).mpr
  refine ⟨fun d => (lambertPair_inner d).1, ?_⟩
  simp_rw [(lambertPair_inner _).2]
  exact summable_pnat_iff_summable_nat.mpr summable_termNat

lemma tsum_lambertPair : (∑' p, lambertPair p) = ∑' n : ℕ, term n := by
  rw [summable_lambertPair.tsum_prod]
  simp_rw [(lambertPair_inner _).2]
  have h := tsum_zero_pnat_eq_tsum_nat summable_termNat
  simp only [termNat, show ¬ 2 ≤ (0 : ℕ) by omega, if_false, zero_add] at h
  exact h.trans tsum_termNat

lemma lambertCoeff_cast_div (m : ℕ) :
    (lambertCoeff m : ℝ) / m.factorial =
      ∑ d ∈ m.divisors, if 2 ≤ d then 1 / (d.factorial : ℝ) ^ (m / d) else 0 := by
  unfold lambertCoeff
  rw [Nat.cast_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hd2 : 2 ≤ d
  · rw [if_pos hd2, if_pos hd2,
      Nat.cast_div_charZero (lambertCoeff_divisible (Nat.dvd_of_mem_divisors hd)), Nat.cast_pow]
    have hm : (m.factorial : ℝ) ≠ 0 := by positivity
    have hd' : (d.factorial : ℝ) ^ (m / d) ≠ 0 := by positivity
    field_simp
  · simp [hd2]

lemma lambertPair_antidiagonal (m : ℕ+) :
    (∑' d : (m : ℕ).divisorsAntidiagonal,
      lambertPair (sigmaAntidiagonalEquivProd ⟨m, d⟩)) =
      (lambertCoeff m : ℝ) / (m : ℕ).factorial := by
  rw [tsum_fintype, lambertCoeff_cast_div]
  change (∑ x : (m : ℕ).divisorsAntidiagonal,
    if 2 ≤ x.val.1 then 1 / (x.val.1.factorial : ℝ) ^ x.val.2 else 0) = _
  rw [Finset.univ_eq_attach,
    Finset.sum_attach _ (fun x : ℕ × ℕ => if 2 ≤ x.1 then 1 / (x.1.factorial : ℝ) ^ x.2 else 0),
    Nat.sum_divisorsAntidiagonal (fun d j => if 2 ≤ d then 1 / (d.factorial : ℝ) ^ j else 0)]

lemma sum_eq_factorial_lambert_pnat :
    (∑' n : ℕ, term n) =
      ∑' m : ℕ+, (lambertCoeff m : ℝ) / (m : ℕ).factorial := by
  rw [← tsum_lambertPair, ← sigmaAntidiagonalEquivProd.tsum_eq lambertPair]
  have hs : Summable (fun d => lambertPair (sigmaAntidiagonalEquivProd d)) :=
    summable_lambertPair.comp_injective sigmaAntidiagonalEquivProd.injective
  rw [hs.tsum_sigma]
  exact tsum_congr lambertPair_antidiagonal

lemma summable_factorial_lambert :
    Summable (fun m : ℕ => (lambertCoeff m : ℝ) / m.factorial) := by
  have hs := (summable_lambertPair.comp_injective
    sigmaAntidiagonalEquivProd.injective).sigma
  have hsp : Summable (fun m : ℕ+ => (lambertCoeff m : ℝ) / (m : ℕ).factorial) :=
    hs.congr lambertPair_antidiagonal
  exact summable_pnat_iff_summable_nat.mp hsp

lemma sum_eq_factorial_lambert :
    (∑' n : ℕ, term n) = ∑' m : ℕ, (lambertCoeff m : ℝ) / m.factorial := by
  rw [sum_eq_factorial_lambert_pnat]
  have h := tsum_zero_pnat_eq_tsum_nat summable_factorial_lambert
  simpa [lambertCoeff] using h

lemma lambertCoeff_not_eventually_digit :
    ¬ ∃ N : ℕ, ∀ m ≥ N, lambertCoeff m < m := by
  rintro ⟨N, hN⟩
  have h := hN (2 * (N + 2)) (by omega)
  have := lambertCoeff_even_ge N
  omega

end Erdos68Development

#print axioms Erdos68Development.sum_eq_factorial_lambert
#print axioms Erdos68Development.lambertCoeff_prime
#print axioms Erdos68Development.lambertCoeff_not_eventually_digit
