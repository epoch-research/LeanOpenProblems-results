import Submission.CofactorCharacterCancellation

/-!
# Character orthogonality after averaging the cofactor

The principal term retains the exact count of coprime cofactors. In the
nonprincipal remainder the cofactor sum is kept inside the absolute value.
This is a finite identity and estimate for actual Mangoldt weights.
-/
open Nat Finset ArithmeticFunction
open scoped Classical BigOperators Topology
namespace Erdos821.AnalyticSieve
set_option maxHeartbeats 2000000

noncomputable def cofactorCongruenceWeight (d : ℕ) (u : (ZMod d)ˣ) (A B N : ℕ) : ℝ :=
  ∑ a ∈ Icc (A+1) B, ∑ n ∈ Icc 1 N,
    if (u : ZMod d)*(a : ZMod d)*(n : ZMod d)=1 then vonMangoldt n else 0

def coprimeCofactorCount (d A B : ℕ) : ℕ :=
  ((Icc (A+1) B).filter (fun a => a.Coprime d)).card

lemma cofactor_congruence_orthogonality (d : ℕ) [NeZero d] (u : (ZMod d)ˣ) (A B N : ℕ) :
    (∑ χ : DirichletCharacter ℂ d, χ u*(∑ a ∈ Icc (A+1) B, χ (a : ZMod d))*
      twistedArithmeticSum χ vonMangoldt N) =
      (d.totient : ℂ)*(cofactorCongruenceWeight d u A B N : ℂ) := by
  calc
    _ = ∑ a ∈ Icc (A+1) B, ∑ n ∈ Icc 1 N, (vonMangoldt n : ℂ)*
        (∑ χ : DirichletCharacter ℂ d, χ ((u : ZMod d)*(a : ZMod d)*(n : ZMod d))) := by
      simp only [twistedArithmeticSum,mul_sum,sum_mul]
      rw [sum_comm]
      conv_rhs => rw [sum_comm]
      apply sum_congr rfl
      intro n hn
      rw [sum_comm]
      apply sum_congr rfl
      intro a ha
      apply sum_congr rfl
      intro χ hχ
      simp only [map_mul]
      ring
    _ = _ := by
      simp only [DirichletCharacter.sum_characters_eq,cofactorCongruenceWeight,
        Complex.ofReal_sum,apply_ite Complex.ofReal,Complex.ofReal_zero,mul_sum,
        mul_ite,mul_zero]
      apply sum_congr rfl
      intro a ha
      apply sum_congr rfl
      intro n hn
      split_ifs <;> ring

lemma principal_cofactor_character_sum (d A B : ℕ) :
    (∑ a ∈ Icc (A+1) B, (1 : DirichletCharacter ℂ d) (a : ZMod d)) =
      (coprimeCofactorCount d A B : ℂ) := by
  simp only [principal_character_nat,← sum_filter,sum_const,nsmul_eq_mul,mul_one,
    coprimeCofactorCount]

lemma norm_twisted_mangoldt_le (d : ℕ) (χ : DirichletCharacter ℂ d) (N : ℕ) :
    ‖twistedArithmeticSum χ vonMangoldt N‖ ≤ mangoldtSum N := by
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro n hn
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg vonMangoldt_nonneg]
  exact (mul_le_mul_of_nonneg_left (χ.norm_le_one _) vonMangoldt_nonneg).trans_eq (mul_one _)

lemma cofactor_character_sum_trivial {d : ℕ} (χ : DirichletCharacter ℂ d) (A B : ℕ) :
    ‖∑ a ∈ Icc (A+1) B, χ (a : ZMod d)‖ ≤ ((B-A : ℕ) : ℝ) := by
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _a ∈ Icc (A+1) B, (1 : ℝ) := sum_le_sum (fun a _ => χ.norm_le_one _)
    _ = _ := by simp

/-- Averaging precedes the triangle inequality; the individual cofactor
phases have not been discarded. -/
theorem cofactor_congruence_discrepancy (d : ℕ) [NeZero d] (u : (ZMod d)ˣ) (A B N : ℕ) :
    |cofactorCongruenceWeight d u A B N-
      (coprimeCofactorCount d A B : ℝ)*(mangoldtSum N-nonunitMangoldt d N)/(d.totient : ℝ)| ≤
      (∑ χ ∈ nonprincipalCharacters d, ‖∑ a ∈ Icc (A+1) B, χ (a : ZMod d)‖*
        ‖twistedArithmeticSum χ vonMangoldt N‖)/(d.totient : ℝ) := by
  classical
  have hφ : (0 : ℝ) < d.totient := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos d)
  have h := Finset.sum_erase_add (univ : Finset (DirichletCharacter ℂ d))
    (fun χ => χ u*(∑ a ∈ Icc (A+1) B, χ (a : ZMod d))*twistedArithmeticSum χ vonMangoldt N)
    (mem_univ 1)
  dsimp only at h
  rw [cofactor_congruence_orthogonality,principal_cofactor_character_sum,
    twisted_principal_mangoldt_composite,MulChar.one_apply u.isUnit,one_mul] at h
  have he : (((d.totient : ℝ)*cofactorCongruenceWeight d u A B N-
      (coprimeCofactorCount d A B : ℝ)*(mangoldtSum N-nonunitMangoldt d N) : ℝ) : ℂ) =
      ∑ χ ∈ nonprincipalCharacters d, χ u*(∑ a ∈ Icc (A+1) B, χ (a : ZMod d))*
        twistedArithmeticSum χ vonMangoldt N := by
    have hs : nonprincipalCharacters d = (univ : Finset (DirichletCharacter ℂ d)).erase 1 := by
      ext χ
      simp only [nonprincipalCharacters,mem_erase,mem_univ,and_true]
    rw [hs]
    push_cast at h ⊢
    linear_combination -h
  have hb : |(d.totient : ℝ)*cofactorCongruenceWeight d u A B N-
      (coprimeCofactorCount d A B : ℝ)*(mangoldtSum N-nonunitMangoldt d N)| ≤
      ∑ χ ∈ nonprincipalCharacters d, ‖∑ a ∈ Icc (A+1) B, χ (a : ZMod d)‖*
        ‖twistedArithmeticSum χ vonMangoldt N‖ := by
    calc
      _ = ‖(((d.totient : ℝ)*cofactorCongruenceWeight d u A B N-
          (coprimeCofactorCount d A B : ℝ)*(mangoldtSum N-nonunitMangoldt d N) : ℝ) : ℂ)‖ := by
        rw [Complex.norm_real,Real.norm_eq_abs]
      _ ≤ _ := by
        rw [he]
        apply (norm_sum_le _ _).trans_eq
        simp only [norm_mul,DirichletCharacter.unit_norm_eq_one,one_mul]
  apply (le_div_iff₀ hφ).mpr
  calc
    _ = |(d.totient : ℝ)*cofactorCongruenceWeight d u A B N-
        (coprimeCofactorCount d A B : ℝ)*(mangoldtSum N-nonunitMangoldt d N)| := by
      calc
        _ = |(cofactorCongruenceWeight d u A B N-
            (coprimeCofactorCount d A B : ℝ)*(mangoldtSum N-nonunitMangoldt d N)/(d.totient : ℝ))*(d.totient : ℝ)| := by
          rw [abs_mul,abs_of_pos hφ]
        _ = _ := by congr 1; field_simp
    _ ≤ _ := hb

/-- The conductor-sensitive estimate can now be inserted without any
pointwise cancellation hypothesis on prime-weighted character sums. -/
theorem cofactor_congruence_conductor_bound (d : ℕ) [NeZero d]
    (u : (ZMod d)ˣ) (A B N : ℕ) :
    |cofactorCongruenceWeight d u A B N-
      (coprimeCofactorCount d A B : ℝ)*(mangoldtSum N-nonunitMangoldt d N)/(d.totient : ℝ)| ≤
      (2 : ℝ)^d.primeFactors.card/(d.totient : ℝ)*
        ∑ χ ∈ nonprincipalCharacters d, (Real.sqrt χ.conductor*(1+Real.log χ.conductor))*
          ‖twistedArithmeticSum χ vonMangoldt N‖ := by
  classical
  apply (cofactor_congruence_discrepancy d u A B N).trans
  calc
    _ ≤ (∑ χ ∈ nonprincipalCharacters d,
        ((2 : ℝ)^d.primeFactors.card*(Real.sqrt χ.conductor*(1+Real.log χ.conductor)))*
          ‖twistedArithmeticSum χ vonMangoldt N‖)/(d.totient : ℝ) := by
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      apply sum_le_sum
      intro χ hχ
      have hχne : χ ≠ 1 := by simpa [nonprincipalCharacters] using hχ
      exact mul_le_mul_of_nonneg_right
        (cofactor_character_interval_bound (NeZero.ne d) χ hχne A B) (norm_nonneg _)
    _ = _ := by simp_rw [mul_assoc]; rw [← mul_sum]; ring

end Erdos821.AnalyticSieve
