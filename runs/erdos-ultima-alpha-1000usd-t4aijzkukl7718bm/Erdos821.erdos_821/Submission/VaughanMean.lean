import Submission.DyadicTypeII

/-!
# A finite mean-value bound for primitive von Mangoldt sums

Vaughan's identity, Pólya–Vinogradov, and the adaptive Type II large sieve
are assembled here. The Type II bound retains its finite active-scale sum.
No assertion about prime counts in progressions is made in this file.
-/

open scoped BigOperators ArithmeticFunction.zeta ArithmeticFunction.Moebius
open Finset ArithmeticFunction

namespace Erdos821.AnalyticSieve

lemma character_family_mass_le (M : Finset ℕ+) (Q : ℕ) (hQ : 0 < Q)
    (hM : ∀ q ∈ M, (q : ℕ) ≤ Q)
    (C : ∀ q : ℕ+, Finset (DirichletCharacter ℂ (q : ℕ))) :
    (∑ q ∈ M, ((q : ℕ) : ℝ) / (q : ℕ).totient * ((C q).card : ℝ)) ≤ (Q : ℝ) ^ 2 := by
  have hcard : M.card ≤ Q := by
    calc
      _ ≤ (Icc (1 : ℕ+) ⟨Q, hQ⟩).card := Finset.card_le_card (by
        intro q hq
        apply mem_Icc.mpr
        change 1 ≤ (q : ℕ) ∧ (q : ℕ) ≤ Q
        exact ⟨q.pos, hM q hq⟩)
      _ = Q := by simp [PNat.card_Icc]
  calc
    _ ≤ ∑ q ∈ M, ((q : ℕ) : ℝ) := by
      apply Finset.sum_le_sum
      intro q hq
      have hc : (C q).card ≤ (q : ℕ).totient := by
        have h := Finset.card_le_univ (C q)
        rw [← Nat.card_eq_fintype_card,
          DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ (q : ℕ)] at h
        exact h
      have hφ : (0 : ℝ) < (q : ℕ).totient := by exact_mod_cast Nat.totient_pos.mpr q.pos
      calc
        _ ≤ ((q : ℕ) : ℝ) / (q : ℕ).totient * ((q : ℕ).totient : ℝ) :=
          mul_le_mul_of_nonneg_left (by exact_mod_cast hc) (by positivity)
        _ = _ := by field_simp
    _ ≤ ∑ q ∈ M, (Q : ℝ) := Finset.sum_le_sum (fun q hq => by exact_mod_cast hM q hq)
    _ ≤ (Q : ℝ) ^ 2 := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      have hc : (M.card : ℝ) ≤ Q := by exact_mod_cast hcard
      nlinarith [Nat.cast_nonneg (α := ℝ) Q]

lemma character_family_sum_le_constant (M : Finset ℕ+) (Q : ℕ) (hQ : 0 < Q)
    (hM : ∀ q ∈ M, (q : ℕ) ≤ Q)
    (C : ∀ q : ℕ+, Finset (DirichletCharacter ℂ (q : ℕ)))
    (F : (q : ℕ+) → DirichletCharacter ℂ (q : ℕ) → ℝ)
    (B : ℝ) (hB : 0 ≤ B) (hF : ∀ q ∈ M, ∀ χ ∈ C q, F q χ ≤ B) :
    (∑ q ∈ M, ((q : ℕ) : ℝ) / (q : ℕ).totient * ∑ χ ∈ C q, F q χ) ≤ (Q : ℝ) ^ 2 * B := by
  calc
    _ ≤ ∑ q ∈ M, ((q : ℕ) : ℝ) / (q : ℕ).totient * ∑ χ ∈ C q, B := by
      apply Finset.sum_le_sum
      intro q hq
      exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum (hF q hq)) (by positivity)
    _ = (∑ q ∈ M, ((q : ℕ) : ℝ) / (q : ℕ).totient * ((C q).card : ℝ)) * B := by
      simp only [Finset.sum_const, nsmul_eq_mul, Finset.sum_mul, mul_assoc]
    _ ≤ _ := mul_le_mul_of_nonneg_right (character_family_mass_le M Q hQ hM C) hB

lemma norm_twisted_one_le {q : ℕ} (χ : DirichletCharacter ℂ q) (N : ℕ) :
    ‖twistedArithmeticSum χ 1 N‖ ≤ 1 := by
  simp only [twistedArithmeticSum, ArithmeticFunction.one_apply, apply_ite Complex.ofReal,
    Complex.ofReal_one, Complex.ofReal_zero, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
    Nat.cast_one, map_one]
  split_ifs <;> norm_num

lemma norm_twisted_short_vonMangoldt_le {q : ℕ} (χ : DirichletCharacter ℂ q) (U N : ℕ) :
    ‖twistedArithmeticSum χ (shortPart vonMangoldt U) N‖ ≤ (U : ℝ) * Real.log U := by
  have h := norm_twisted_convolution_le χ (shortPart vonMangoldt U) 1 N U (Real.log U) 1
    (Real.log_natCast_nonneg U) (by norm_num) (fun n hn => ?_)
    (fun n hn => by simp only [shortPart_apply, if_neg (not_le.mpr hn)])
    (fun L hL => norm_twisted_one_le χ L)
  · simpa only [mul_one] using h
  · rw [abs_of_nonneg (shortPart_vonMangoldt_nonneg U n), shortPart_apply]
    split_ifs with hnU
    · exact vonMangoldt_le_log.trans (log_nat_mono hnU)
    · exact Real.log_natCast_nonneg U

noncomputable def pvMajorant (Q : ℕ) : ℝ := Real.sqrt Q * (1 + Real.log Q)

lemma pvMajorant_nonneg (Q : ℕ) : 0 ≤ pvMajorant Q := by
  unfold pvMajorant
  have := Real.log_natCast_nonneg Q
  positivity

lemma pvMajorant_mono {q Q : ℕ} (hqQ : q ≤ Q) : pvMajorant q ≤ pvMajorant Q := by
  unfold pvMajorant
  exact mul_le_mul (Real.sqrt_le_sqrt (by exact_mod_cast hqQ))
    (add_le_add le_rfl (log_nat_mono hqQ))
    (by linarith [Real.log_natCast_nonneg q]) (Real.sqrt_nonneg _)

noncomputable def vaughanShortMajorant (U V N Q : ℕ) : ℝ :=
  (U : ℝ) * Real.log U + ((U : ℝ) * V + 2 * V) * pvMajorant Q * Real.log N

lemma vaughanShortMajorant_nonneg (U V N Q : ℕ) : 0 ≤ vaughanShortMajorant U V N Q := by
  unfold vaughanShortMajorant
  have := Real.log_natCast_nonneg U
  have := Real.log_natCast_nonneg N
  have := pvMajorant_nonneg Q
  positivity

lemma norm_twisted_vonMangoldt_le_short_add_typeII {q : ℕ} [NeZero q]
    (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
    (U V N Q R : ℕ) (hqQ : q ≤ Q) (hRN : R ≤ N) :
    ‖twistedArithmeticSum χ vonMangoldt R‖ ≤ vaughanShortMajorant U V N Q +
      ‖twistedArithmeticSum χ (vaughanTypeII V * longPart vonMangoldt U) R‖ := by
  have hμ : ‖twistedArithmeticSum χ (shortPart (μ : ArithmeticFunction ℝ) V * log) R‖ ≤
      2 * (V : ℝ) * pvMajorant Q * Real.log N := by
    apply (norm_vaughan_mu_log_le hq hχ V R).trans
    calc
      _ = (2 * (V : ℝ) * pvMajorant q) * Real.log R := by unfold pvMajorant; ring
      _ ≤ _ := mul_le_mul
        (mul_le_mul_of_nonneg_left (pvMajorant_mono hqQ) (by positivity))
        (log_nat_mono hRN) (Real.log_natCast_nonneg R)
        (by have := pvMajorant_nonneg Q; positivity)
  have hI : ‖twistedArithmeticSum χ (vaughanTypeI U V * (ζ : ArithmeticFunction ℝ)) R‖ ≤
      (U : ℝ) * V * pvMajorant Q * Real.log N := by
    apply (norm_vaughan_typeI_le hq hχ U V R).trans
    calc
      _ = ((U : ℝ) * V * pvMajorant q) * Real.log R := by unfold pvMajorant; ring
      _ ≤ _ := mul_le_mul
        (mul_le_mul_of_nonneg_left (pvMajorant_mono hqQ) (by positivity))
        (log_nat_mono hRN) (Real.log_natCast_nonneg R)
        (by have := pvMajorant_nonneg Q; positivity)
  rw [twisted_vaughan_identity χ U V R]
  have htri : ∀ a b c d : ℂ, ‖a + b - c + d‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ := by
    intro a b c d
    calc
      _ ≤ ‖a + b - c‖ + ‖d‖ := norm_add_le _ _
      _ ≤ (‖a + b‖ + ‖c‖) + ‖d‖ := add_le_add (norm_sub_le _ _) le_rfl
      _ ≤ _ := add_le_add (add_le_add (norm_add_le _ _) le_rfl) le_rfl
  apply (htri _ _ _ _).trans
  have hS := norm_twisted_short_vonMangoldt_le χ U R
  unfold vaughanShortMajorant
  nlinarith

/-- A finite primitive-character von Mangoldt mean-value estimate, with
separate endpoints and an explicit active-scale Type II remainder. -/
theorem primitive_vonMangoldt_mean_bound
    (M : Finset ℕ+) (Q : ℕ) (hQ : 0 < Q)
    (hM : ∀ q ∈ M, 2 ≤ (q : ℕ) ∧ (q : ℕ) ≤ Q)
    (C : ∀ q : ℕ+, Finset (DirichletCharacter ℂ (q : ℕ)))
    (hC : ∀ q ∈ M, ∀ χ ∈ C q, χ.IsPrimitive)
    (U V N : ℕ) (hV : 1 ≤ V)
    (R : (q : ℕ+) → DirichletCharacter ℂ (q : ℕ) → ℕ)
    (hR : ∀ q ∈ M, ∀ χ ∈ C q, R q χ ≤ N) :
    (∑ q ∈ M, ((q : ℕ) : ℝ) / (q : ℕ).totient * ∑ χ ∈ C q,
      ‖twistedArithmeticSum χ vonMangoldt (R q χ)‖) ≤
      (Q : ℝ) ^ 2 * vaughanShortMajorant U V N Q +
      (6 + 2 * Real.log ((N : ℝ) + 1)) *
        ∑ j ∈ typeIILevels N U V, typeIIBlockMajorant Q (2 ^ (j + 1)) (N / 2 ^ j) := by
  calc
    _ ≤ ∑ q ∈ M, ((q : ℕ) : ℝ) / (q : ℕ).totient * ∑ χ ∈ C q,
        (vaughanShortMajorant U V N Q +
          ‖twistedArithmeticSum χ (vaughanTypeII V * longPart vonMangoldt U) (R q χ)‖) := by
      apply Finset.sum_le_sum
      intro q hq
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Finset.sum_le_sum (fun χ hχ => norm_twisted_vonMangoldt_le_short_add_typeII
        (hM q hq).1 (hC q hq χ hχ) U V N Q (R q χ) (hM q hq).2 (hR q hq χ hχ))
    _ = (∑ q ∈ M, ((q : ℕ) : ℝ) / (q : ℕ).totient * ∑ χ ∈ C q, vaughanShortMajorant U V N Q) +
        (∑ q ∈ M, ((q : ℕ) : ℝ) / (q : ℕ).totient * ∑ χ ∈ C q,
          ‖twistedArithmeticSum χ (vaughanTypeII V * longPart vonMangoldt U) (R q χ)‖) := by
      simp only [Finset.sum_add_distrib, mul_add]
    _ ≤ _ := add_le_add
      (character_family_sum_le_constant M Q hQ (fun q hq => (hM q hq).2) C
        (fun _ _ => vaughanShortMajorant U V N Q) _ (vaughanShortMajorant_nonneg U V N Q)
        (fun _ _ _ _ => le_rfl))
      (vaughan_typeII_dyadic_bound M Q hQ (fun q hq => (hM q hq).2) C hC U V N hV R hR)

end Erdos821.AnalyticSieve
