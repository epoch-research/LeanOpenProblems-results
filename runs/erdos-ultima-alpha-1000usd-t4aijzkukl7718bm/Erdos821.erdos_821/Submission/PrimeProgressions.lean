import Submission.BalancedVaughanMean

/-!
# Von Mangoldt sums in residue one at prime moduli

Finite character orthogonality and the primitive-character mean estimate
control the average progression discrepancy over prime moduli.
-/

open scoped BigOperators
open Finset ArithmeticFunction

namespace Erdos821.AnalyticSieve

noncomputable def mangoldtSum (N : ℕ) : ℝ := ∑ n ∈ Icc 1 N, vonMangoldt n

noncomputable def residueOneMangoldt (q N : ℕ) : ℝ :=
  ∑ n ∈ Icc 1 N, if (n : ZMod q) = 1 then vonMangoldt n else 0

noncomputable def omittedMangoldt (q N : ℕ) : ℝ :=
  ∑ n ∈ Icc 1 N, if q ∣ n then vonMangoldt n else 0

noncomputable def nonprincipalCharacters (q : ℕ) : Finset (DirichletCharacter ℂ q) :=
  by classical exact univ.erase 1

lemma nonprincipal_prime_isPrimitive {q : ℕ} (hq : q.Prime) {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) : χ.IsPrimitive := by
  rcases hq.eq_one_or_self_of_dvd χ.conductor χ.conductor_dvd_level with hc | hc
  · exact (hχ ((DirichletCharacter.eq_one_iff_conductor_eq_one hq.ne_zero).mpr hc)).elim
  · exact hc

lemma nonprincipalCharacters_primitive {q : ℕ} (hq : q.Prime)
    {χ : DirichletCharacter ℂ q} (hχ : χ ∈ nonprincipalCharacters q) : χ.IsPrimitive := by
  classical
  exact nonprincipal_prime_isPrimitive hq (Finset.mem_erase.mp hχ).1

lemma principal_character_prime {q : ℕ} (hq : q.Prime) (n : ℕ) :
    (1 : DirichletCharacter ℂ q) (n : ZMod q) = if q ∣ n then 0 else 1 := by
  letI : Fact q.Prime := ⟨hq⟩
  by_cases hn : q ∣ n
  · rw [if_pos hn, (ZMod.natCast_eq_zero_iff n q).mpr hn]
    exact DirichletCharacter.map_zero' _ hq.ne_one
  · rw [if_neg hn]
    exact MulChar.one_apply (isUnit_iff_ne_zero.mpr ((ZMod.natCast_eq_zero_iff n q).not.mpr hn))

lemma omittedMangoldt_nonneg (q N : ℕ) : 0 ≤ omittedMangoldt q N := by
  apply Finset.sum_nonneg
  intro n hn
  split_ifs
  · exact vonMangoldt_nonneg
  · rfl

lemma omittedMangoldt_le (q N : ℕ) : omittedMangoldt q N ≤ (N : ℝ) / q * Real.log N := by
  classical
  have hcard : ((Icc 1 N).filter (fun n => q ∣ n)).card = N / q := by
    have heq : (Icc 1 N).filter (fun n => q ∣ n) =
        (range (N + 1)).filter (fun n => n ≠ 0 ∧ q ∣ n) := by
      ext n
      simp only [mem_filter, mem_Icc, mem_range]
      omega
    rw [heq, Nat.card_multiples']
  calc
    _ ≤ ∑ n ∈ (Icc 1 N).filter (fun n => q ∣ n), Real.log N := by
      rw [omittedMangoldt, ← Finset.sum_filter]
      apply Finset.sum_le_sum
      intro n hn
      exact vonMangoldt_le_log.trans (log_nat_mono (mem_Icc.mp (mem_filter.mp hn).1).2)
    _ = ((N / q : ℕ) : ℝ) * Real.log N := by rw [Finset.sum_const, hcard, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right Nat.cast_div_le (Real.log_natCast_nonneg N)

lemma twisted_principal_mangoldt {q : ℕ} (hq : q.Prime) (N : ℕ) :
    twistedArithmeticSum (1 : DirichletCharacter ℂ q) vonMangoldt N =
      ((mangoldtSum N - omittedMangoldt q N : ℝ) : ℂ) := by
  simp only [twistedArithmeticSum, mangoldtSum, omittedMangoldt, Complex.ofReal_sub,
    Complex.ofReal_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  rw [principal_character_prime hq]
  by_cases h : q ∣ n <;> simp [h]

lemma residueOneMangoldt_orthogonality {q : ℕ} [NeZero q] (N : ℕ) :
    (∑ χ : DirichletCharacter ℂ q, twistedArithmeticSum χ vonMangoldt N) =
      (q.totient : ℂ) * (residueOneMangoldt q N : ℂ) := by
  simp only [twistedArithmeticSum]
  rw [Finset.sum_comm]
  calc
    _ = ∑ n ∈ Icc 1 N, (vonMangoldt n : ℂ) *
        (∑ χ : DirichletCharacter ℂ q, χ (n : ZMod q)) := by simp only [Finset.mul_sum]
    _ = _ := by
      simp only [DirichletCharacter.sum_characters_eq, residueOneMangoldt, Complex.ofReal_sum,
        apply_ite Complex.ofReal, Complex.ofReal_zero, Finset.mul_sum, mul_ite, mul_zero]
      apply Finset.sum_congr rfl
      intro n hn
      split_ifs <;> ring

lemma prime_progression_discrepancy {q : ℕ} [NeZero q] (hq : q.Prime) (N : ℕ) :
    |residueOneMangoldt q N - mangoldtSum N / q.totient| ≤
      ((∑ χ ∈ nonprincipalCharacters q, ‖twistedArithmeticSum χ vonMangoldt N‖) +
        omittedMangoldt q N) / q.totient := by
  classical
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr hq.pos
  have h := Finset.sum_erase_add (univ : Finset (DirichletCharacter ℂ q))
    (fun χ => twistedArithmeticSum χ vonMangoldt N) (mem_univ 1)
  dsimp only at h
  rw [residueOneMangoldt_orthogonality, twisted_principal_mangoldt hq] at h
  have heq : (((q.totient : ℝ) * residueOneMangoldt q N - mangoldtSum N : ℝ) : ℂ) =
      (∑ χ ∈ nonprincipalCharacters q, twistedArithmeticSum χ vonMangoldt N) -
        (omittedMangoldt q N : ℂ) := by
    have hs : nonprincipalCharacters q = (univ : Finset (DirichletCharacter ℂ q)).erase 1 := by
      ext χ
      simp only [nonprincipalCharacters, mem_erase, mem_univ, and_true]
    rw [hs]
    push_cast at h ⊢
    linear_combination -h
  have hb : |(q.totient : ℝ) * residueOneMangoldt q N - mangoldtSum N| ≤
      (∑ χ ∈ nonprincipalCharacters q, ‖twistedArithmeticSum χ vonMangoldt N‖) + omittedMangoldt q N := by
    calc
      _ = ‖(((q.totient : ℝ) * residueOneMangoldt q N - mangoldtSum N : ℝ) : ℂ)‖ := by
        rw [Complex.norm_real, Real.norm_eq_abs]
      _ ≤ _ := by
        rw [heq]
        apply (norm_sub_le _ _).trans
        apply add_le_add (norm_sum_le _ _)
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (omittedMangoldt_nonneg q N)]
  apply (le_div_iff₀ hφ).mpr
  calc
    _ = |(q.totient : ℝ) * residueOneMangoldt q N - mangoldtSum N| := by
      calc
        _ = |(residueOneMangoldt q N - mangoldtSum N / q.totient) * (q.totient : ℝ)| := by
          rw [abs_mul, abs_of_pos hφ]
        _ = _ := by congr 1; field_simp
    _ ≤ _ := hb

lemma omittedMangoldt_div_totient_le {q D : ℕ} (hq : q.Prime) (hD : 0 < D) (hDq : D ≤ q)
    (N : ℕ) : omittedMangoldt q N / q.totient ≤ 2 * (N : ℝ) / (D : ℝ) ^ 2 * Real.log N := by
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have hq' : (2 : ℝ) ≤ q := by exact_mod_cast hq.two_le
  have hDq' : (D : ℝ) ≤ q := by exact_mod_cast hDq
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr hq.pos
  have hφD : (D : ℝ) / 2 ≤ q.totient := by
    rw [Nat.totient_prime hq, Nat.cast_sub (by omega : 1 ≤ q), Nat.cast_one]
    linarith
  have hlog := Real.log_natCast_nonneg N
  calc
    _ ≤ ((N : ℝ) / D * Real.log N) / ((D : ℝ) / 2) := by
      apply div_le_div₀ (by positivity) _ (by positivity) hφD
      exact (omittedMangoldt_le q N).trans
        (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left (Nat.cast_nonneg N) hD' hDq') hlog)
    _ = _ := by field_simp

lemma positive_moduli_card_le (M : Finset ℕ+) (Q : ℕ) (hQ : 0 < Q)
    (hM : ∀ q ∈ M, (q : ℕ) ≤ Q) : M.card ≤ Q := by
  calc
    _ ≤ (Icc (1 : ℕ+) ⟨Q, hQ⟩).card := Finset.card_le_card (by
      intro q hq
      apply mem_Icc.mpr
      change 1 ≤ (q : ℕ) ∧ (q : ℕ) ≤ Q
      exact ⟨q.pos, hM q hq⟩)
    _ = Q := by simp [PNat.card_Icc]

noncomputable def primeProgressionError (U V N Q D : ℕ) : ℝ :=
  ((Q : ℝ) ^ 2 * vaughanShortMajorant U V N Q + balancedTypeIIMajorant N Q) / D +
    2 * Q * N / (D : ℝ) ^ 2 * Real.log N

/-- An explicit average residue-one discrepancy bound over prime moduli.
There is no small-conductor assumption: nonprincipal characters at these
moduli are primitive. -/
theorem prime_progression_average_error
    (M : Finset ℕ+) (D Q : ℕ) (hD : 0 < D) (hQ : 0 < Q)
    (hM : ∀ q ∈ M, (q : ℕ).Prime ∧ D ≤ (q : ℕ) ∧ (q : ℕ) ≤ Q)
    (U V N : ℕ) (hV : 1 ≤ V)
    (hNU : 2 * N ≤ (U + 1) * Q ^ 2) (hNV : 2 * N ≤ V * Q ^ 2) :
    (∑ q ∈ M, |residueOneMangoldt q N - mangoldtSum N / (q : ℕ).totient|) ≤
      primeProgressionError U V N Q D := by
  classical
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  let A (q : ℕ+) : ℝ := ∑ χ ∈ nonprincipalCharacters q, ‖twistedArithmeticSum χ vonMangoldt N‖
  have hmean := primitive_vonMangoldt_balanced_mean_bound M Q hQ
    (fun q hq => ⟨(hM q hq).1.two_le, (hM q hq).2.2⟩)
    (fun q => nonprincipalCharacters q)
    (fun q hq χ hχ => nonprincipalCharacters_primitive (hM q hq).1 hχ)
    U V N hV hNU hNV (fun _ _ => N) (fun _ _ _ _ => le_rfl)
  have hlocal (q : ℕ+) (hq : q ∈ M) :
      |residueOneMangoldt q N - mangoldtSum N / (q : ℕ).totient| ≤
        ((((q : ℕ) : ℝ) / (q : ℕ).totient) * A q) / D +
          2 * (N : ℝ) / (D : ℝ) ^ 2 * Real.log N := by
    apply (prime_progression_discrepancy (hM q hq).1 N).trans
    rw [add_div]
    apply add_le_add _ (omittedMangoldt_div_totient_le (hM q hq).1 hD (hM q hq).2.1 N)
    change A q / (q : ℕ).totient ≤ _
    have hqpos : (0 : ℝ) < (q : ℕ) := by exact_mod_cast q.pos
    have hφ : (0 : ℝ) < (q : ℕ).totient := by exact_mod_cast Nat.totient_pos.mpr q.pos
    calc
      _ = ((((q : ℕ) : ℝ) / (q : ℕ).totient) * A q) / (q : ℕ) := by field_simp
      _ ≤ _ := div_le_div_of_nonneg_left
        (by dsimp [A]; positivity) hD' (by exact_mod_cast (hM q hq).2.1)
  calc
    _ ≤ ∑ q ∈ M, (((((q : ℕ) : ℝ) / (q : ℕ).totient) * A q) / D +
        2 * (N : ℝ) / (D : ℝ) ^ 2 * Real.log N) := Finset.sum_le_sum hlocal
    _ = (∑ q ∈ M, (((q : ℕ) : ℝ) / (q : ℕ).totient) * A q) / D +
        (M.card : ℝ) * (2 * (N : ℝ) / (D : ℝ) ^ 2 * Real.log N) := by
      rw [Finset.sum_add_distrib, ← Finset.sum_div, Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((Q : ℝ) ^ 2 * vaughanShortMajorant U V N Q + balancedTypeIIMajorant N Q) / D +
        (Q : ℝ) * (2 * (N : ℝ) / (D : ℝ) ^ 2 * Real.log N) := by
      apply add_le_add (div_le_div_of_nonneg_right hmean hD'.le)
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast positive_moduli_card_le M Q hQ (fun q hq => (hM q hq).2.2)
      · have := Real.log_natCast_nonneg N
        positivity
    _ = _ := by unfold primeProgressionError; ring

/-- The corresponding lower bound for the total progression weight. -/
theorem prime_progression_total_lower
    (M : Finset ℕ+) (D Q : ℕ) (hD : 0 < D) (hQ : 0 < Q)
    (hM : ∀ q ∈ M, (q : ℕ).Prime ∧ D ≤ (q : ℕ) ∧ (q : ℕ) ≤ Q)
    (U V N : ℕ) (hV : 1 ≤ V)
    (hNU : 2 * N ≤ (U + 1) * Q ^ 2) (hNV : 2 * N ≤ V * Q ^ 2) :
    mangoldtSum N * (∑ q ∈ M, (((q : ℕ).totient : ℝ))⁻¹) - primeProgressionError U V N Q D ≤
      ∑ q ∈ M, residueOneMangoldt q N := by
  have he := prime_progression_average_error M D Q hD hQ hM U V N hV hNU hNV
  have hs : (∑ q ∈ M, (mangoldtSum N / (q : ℕ).totient - residueOneMangoldt q N)) ≤
      ∑ q ∈ M, |residueOneMangoldt q N - mangoldtSum N / (q : ℕ).totient| := by
    apply Finset.sum_le_sum
    intro q hq
    simpa only [neg_sub] using neg_le_abs (residueOneMangoldt q N - mangoldtSum N / (q : ℕ).totient)
  rw [Finset.sum_sub_distrib] at hs
  simp only [div_eq_mul_inv, ← Finset.mul_sum] at hs he
  linarith

end Erdos821.AnalyticSieve
