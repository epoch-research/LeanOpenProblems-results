import Submission.PrimeLeadingForms

/-!
A fixed nonzero rational shift operator cannot annihilate all sufficiently
late Lambert coefficients.  This is an auxiliary nonvanishing theorem, not
an irrationality proof: its prime cutoff depends on the operator's height.
-/

namespace LambertFixedOperatorNonvanishing

open Finset Erdos68Development PrimeLeadingForms

def coefficient (n : ℕ) : ℚ := (lambertCoeff n : ℚ) / n.factorial

def coefficientForm (w : ℕ → ℤ) (D n : ℕ) : ℚ :=
  ∑ i ∈ range (D + 1), (w i : ℚ) * coefficient (n + i)

lemma earlier_coefficients_integral (w : ℕ → ℤ) (D n p : ℕ)
    (hp : n + D = p) (hp0 : 0 < p) :
    ∃ z : ℤ, ((p - 1).factorial : ℚ) *
      (∑ i ∈ range D, (w i : ℚ) * coefficient (n + i)) = z := by
  rw [mul_sum]
  apply integer_sum
  intro i hi
  have hn : n + i ≤ p - 1 := by
    have := mem_range.mp hi
    omega
  have hd := Nat.factorial_dvd_factorial hn
  refine ⟨w i * (lambertCoeff (n + i) : ℤ) *
      ((p - 1).factorial / (n + i).factorial : ℕ), ?_⟩
  simp only [coefficient, Int.cast_mul, Int.cast_natCast]
  rw [Nat.cast_div_charZero hd]
  ring

/-- A prime final index detects a final weight not divisible by that prime. -/
theorem coefficientForm_ne_zero_at_prime (w : ℕ → ℤ) (D n p : ℕ)
    (hp : p.Prime) (hn : n + D = p) (hw : ¬(p : ℤ) ∣ w D) :
    coefficientForm w D n ≠ 0 := by
  obtain ⟨z, hz⟩ := earlier_coefficients_integral w D n p hn hp.pos
  have hp0 := hp.pos
  have hpQ : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hfac : (p.factorial : ℚ) = p * ((p - 1).factorial : ℚ) := by
    exact_mod_cast (by simpa [show p - 1 + 1 = p by omega]
      using Nat.factorial_succ (p - 1))
  intro he
  rw [coefficientForm, sum_range_succ, hn, coefficient,
    lambertCoeff_prime hp, Nat.cast_one] at he
  have hm := congrArg (fun y : ℚ => (p.factorial : ℚ) * y) he
  have hpn : (p.factorial : ℚ) ≠ 0 := by positivity
  have hh : (p : ℚ) * z + w D = 0 := by
    calc
      _ = (p.factorial : ℚ) *
          ((∑ i ∈ range D, (w i : ℚ) * coefficient (n + i)) +
            (w D : ℚ) * (1 / p.factorial)) := by
        rw [mul_add, hfac, ← hz]
        field_simp
      _ = 0 := by simpa using hm
  have hhZ : (p : ℤ) * z + w D = 0 := by exact_mod_cast hh
  exact hw ⟨-z, by linear_combination hhZ⟩

/-- Every fixed operator with a nonzero final coefficient is nonzero at
arbitrarily late indices.  The prime chosen here exceeds its final weight. -/
theorem integer_operator_frequently_ne_zero (w : ℕ → ℤ) (D : ℕ)
    (hw : w D ≠ 0) (H : ℕ) :
    ∃ n ≥ H, coefficientForm w D n ≠ 0 := by
  obtain ⟨p, hlarge, hp⟩ := Nat.exists_infinite_primes
    (H + D + (w D).natAbs + 1)
  have hpD : D ≤ p := by omega
  refine ⟨p - D, by omega, coefficientForm_ne_zero_at_prime w D (p-D) p hp
    (by omega) ?_⟩
  intro hd
  have ha : p ∣ (w D).natAbs := Int.natCast_dvd.mp hd
  have hpos : 0 < (w D).natAbs := Int.natAbs_pos.mpr hw
  have := Nat.le_of_dvd hpos ha
  omega

/-- Clear finitely many rational weights, without any assertion about the
size of the clearing multiplier. -/
lemma clear_weights (w : ℕ → ℚ) (D : ℕ) :
    ∃ C : ℕ, 0 < C ∧ ∃ z : ℕ → ℤ,
      ∀ i < D + 1, (C : ℚ) * w i = z i := by
  let C := ∏ i ∈ range (D + 1), (w i).den
  have hC : 0 < C := prod_pos (fun i _ => (w i).pos)
  let z : ℕ → ℤ := fun i => (w i).num * (C / (w i).den : ℕ)
  refine ⟨C, hC, z, ?_⟩
  intro i hi
  have hd : (w i).den ∣ C := dvd_prod_of_mem (fun i => (w i).den) (mem_range.mpr hi)
  simp only [z, Int.cast_mul, Int.cast_natCast]
  rw [Nat.cast_div_charZero hd]
  conv_lhs => rw [← Rat.num_div_den (w i)]
  ring

/-- No nonzero rational constant-coefficient recurrence holds eventually for
the rational Lambert coefficient sequence. -/
theorem rational_operator_frequently_ne_zero (w : ℕ → ℚ) (D : ℕ)
    (hw : w D ≠ 0) (H : ℕ) :
    ∃ n ≥ H, (∑ i ∈ range (D + 1), w i * coefficient (n + i)) ≠ 0 := by
  obtain ⟨C, hC, z, hz⟩ := clear_weights w D
  have hzD : z D ≠ 0 := by
    intro he
    have hc : (C : ℚ) ≠ 0 := by exact_mod_cast hC.ne'
    have hh := hz D (by omega)
    rw [he, Int.cast_zero] at hh
    exact hw ((mul_eq_zero.mp hh).resolve_left hc)
  obtain ⟨n, hn, hne⟩ := integer_operator_frequently_ne_zero z D hzD H
  refine ⟨n, hn, ?_⟩
  intro he
  apply hne
  unfold coefficientForm
  calc
    _ = ∑ i ∈ range (D + 1), ((C : ℚ) * w i) * coefficient (n + i) := by
      apply sum_congr rfl
      intro i hi
      rw [hz i (mem_range.mp hi)]
    _ = (C : ℚ) * (∑ i ∈ range (D + 1), w i * coefficient (n + i)) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro i hi
      ring
    _ = 0 := by rw [he, mul_zero]


/-- The shift operator applied to an arbitrary real constant minus the
Lambert prefixes.  In particular the constant can be the target sum. -/
noncomputable def tailForm (w : ℕ → ℚ) (D : ℕ) (x : ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ range (D + 1), (w i : ℝ) *
    (x - (partialSum (fun j => (lambertCoeff j : ℤ)) (n + i) : ℚ))

lemma partialSum_succ (n : ℕ) :
    partialSum (fun j => (lambertCoeff j : ℤ)) (n + 1) =
      partialSum (fun j => (lambertCoeff j : ℤ)) n + coefficient (n + 1) := by
  simp [partialSum, coefficient, sum_range_succ]

lemma tailForm_sub_succ (w : ℕ → ℚ) (D : ℕ) (x : ℝ) (n : ℕ) :
    tailForm w D x n - tailForm w D x (n + 1) =
      ((∑ i ∈ range (D + 1), w i * coefficient (n + 1 + i) : ℚ) : ℝ) := by
  simp only [tailForm, ← sum_sub_distrib, Rat.cast_sum, Rat.cast_mul]
  apply sum_congr rfl
  intro i hi
  have hs := partialSum_succ (n + i)
  rw [show n + i + 1 = n + 1 + i by omega] at hs
  rw [hs, Rat.cast_add]
  ring

/-- Even without rationality of x, a fixed nonzero operator cannot vanish
on all sufficiently late tails.  This is not uniform over growing operators. -/
theorem tail_operator_frequently_ne_zero (w : ℕ → ℚ) (D : ℕ)
    (hw : w D ≠ 0) (x : ℝ) (H : ℕ) :
    ∃ n ≥ H, tailForm w D x n ≠ 0 := by
  obtain ⟨n, hn, hne⟩ := rational_operator_frequently_ne_zero w D hw (H + 1)
  have hs := tailForm_sub_succ w D x (n - 1)
  rw [show n - 1 + 1 = n by omega] at hs
  by_cases hfirst : tailForm w D x (n - 1) = 0
  · refine ⟨n, by omega, ?_⟩
    intro hnext
    rw [hfirst, hnext, sub_self] at hs
    have hh : (∑ i ∈ range (D + 1), w i * coefficient (n + i)) = 0 := by
      exact_mod_cast hs.symm
    exact hne hh
  · exact ⟨n - 1, by omega, hfirst⟩

#print axioms tail_operator_frequently_ne_zero

#print axioms coefficientForm_ne_zero_at_prime
#print axioms integer_operator_frequently_ne_zero
#print axioms rational_operator_frequently_ne_zero

end LambertFixedOperatorNonvanishing
