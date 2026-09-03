import Submission.MultiplicativeCofactorPrimitive
import Submission.RestrictedCofactorWeights

/-!
# Exact pool orthogonality and unit-supported lifting

Both the multiplier pool and the arithmetic weight may be supported on
units of the sieve modulus. Their lifting then has no deleted-prime error.
These finite identities do not assert a prime-successor lower bound.
-/
open Nat Finset ArithmeticFunction
open scoped Classical BigOperators Topology
namespace Erdos821.AnalyticSieve
set_option maxHeartbeats 4000000

noncomputable def poolCofactorWeight (f : ArithmeticFunction ℝ) (P : Finset ℕ)
    (d : ℕ) (u : (ZMod d)ˣ) (A B N : ℕ) : ℝ :=
  ∑ c ∈ P, ∑ a ∈ Icc (A+1) B, ∑ n ∈ Icc 1 N,
    if ((u : ZMod d)*(c : ZMod d))*(a : ZMod d)*(n : ZMod d)=1 then f n else 0

lemma unit_supported_twisted_changeLevel (f : ArithmeticFunction ℝ)
    {c d : ℕ} (hcd : c ∣ d) (ψ : DirichletCharacter ℂ c) (N : ℕ)
    (hf : ∀ n ∈ Icc 1 N, f n ≠ 0 → n.Coprime d) :
    twistedArithmeticSum (DirichletCharacter.changeLevel hcd ψ) f N =
      twistedArithmeticSum ψ f N := by
  apply sum_congr rfl
  intro n hn
  rw [changeLevel_apply_nat]
  by_cases hn0 : f n = 0
  · simp [hn0]
  · rw [if_pos (hf n hn hn0)]

lemma unit_pool_character_changeLevel (P : Finset ℕ)
    {c d : ℕ} (hcd : c ∣ d) (ψ : DirichletCharacter ℂ c)
    (hP : ∀ n ∈ P, n.Coprime d) :
    (∑ n ∈ P, (DirichletCharacter.changeLevel hcd ψ) (n : ZMod d)) =
      ∑ n ∈ P, ψ (n : ZMod c) := by
  apply sum_congr rfl
  intro n hn
  rw [changeLevel_apply_nat,if_pos (hP n hn)]

lemma unit_supported_nonunitMass_zero (f : ArithmeticFunction ℝ) (d N : ℕ)
    (hf : ∀ n ∈ Icc 1 N, f n ≠ 0 → n.Coprime d) :
    restrictedNonunitMass f d N = 0 := by
  apply sum_eq_zero
  intro n hn
  by_cases h : n.Coprime d
  · simp [h]
  · have hz : f n = 0 := by by_contra hz; exact h (hf n hn hz)
    simp [hz]

lemma unit_pool_principal_sum (P : Finset ℕ) (d : ℕ)
    (hP : ∀ n ∈ P, n.Coprime d) :
    (∑ n ∈ P, (1 : DirichletCharacter ℂ d) (n : ZMod d)) = (P.card : ℂ) := by
  have hh : (∑ n ∈ P, (1 : DirichletCharacter ℂ d) (n : ZMod d)) = ∑ _n ∈ P, (1 : ℂ) := by
    apply sum_congr rfl
    intro n hn
    rw [principal_character_nat,if_pos (hP n hn)]
  simpa using hh

lemma cofactor_coefficient_orthogonality (f : ArithmeticFunction ℝ)
    (d : ℕ) [NeZero d] (v : ZMod d) (A B N : ℕ) :
    (∑ χ : DirichletCharacter ℂ d, χ v*(∑ a ∈ Icc (A+1) B, χ (a : ZMod d))*
      twistedArithmeticSum χ f N) =
      (d.totient : ℂ)*((∑ a ∈ Icc (A+1) B, ∑ n ∈ Icc 1 N,
        if v*(a : ZMod d)*(n : ZMod d)=1 then f n else 0 : ℝ) : ℂ) := by
  calc
    _ = ∑ a ∈ Icc (A+1) B, ∑ n ∈ Icc 1 N, (f n : ℂ)*
        (∑ χ : DirichletCharacter ℂ d, χ (v*(a : ZMod d)*(n : ZMod d))) := by
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
      simp only [DirichletCharacter.sum_characters_eq,
        Complex.ofReal_sum,apply_ite Complex.ofReal,Complex.ofReal_zero,mul_sum,
        mul_ite,mul_zero]
      apply sum_congr rfl
      intro a ha
      apply sum_congr rfl
      intro n hn
      split_ifs <;> ring

lemma pool_cofactor_orthogonality (f : ArithmeticFunction ℝ) (P : Finset ℕ)
    (d : ℕ) [NeZero d] (u : (ZMod d)ˣ) (A B N : ℕ) :
    (∑ χ : DirichletCharacter ℂ d, χ u*(∑ c ∈ P, χ (c : ZMod d))*
      (∑ a ∈ Icc (A+1) B, χ (a : ZMod d))*twistedArithmeticSum χ f N) =
      (d.totient : ℂ)*(poolCofactorWeight f P d u A B N : ℂ) := by
  have hx (χ : DirichletCharacter ℂ d) :
      χ u*(∑ c ∈ P, χ (c : ZMod d))*(∑ a ∈ Icc (A+1) B, χ (a : ZMod d))*
        twistedArithmeticSum χ f N =
      ∑ c ∈ P, χ ((u : ZMod d)*(c : ZMod d))*(∑ a ∈ Icc (A+1) B, χ (a : ZMod d))*
        twistedArithmeticSum χ f N := by
    rw [mul_sum (s := P),sum_mul,sum_mul]
    exact sum_congr rfl (fun c hc => by rw [map_mul])
  simp_rw [hx]
  rw [sum_comm]
  simp_rw [cofactor_coefficient_orthogonality]
  simp only [poolCofactorWeight,Complex.ofReal_sum,mul_sum]

/-- Averaging over the multiplier pool precedes taking absolute values. -/
theorem pool_cofactor_discrepancy (f : ArithmeticFunction ℝ) (P : Finset ℕ)
    (d : ℕ) [NeZero d] (u : (ZMod d)ˣ) (A B N : ℕ)
    (hP : ∀ c ∈ P, c.Coprime d)
    (hf : ∀ n ∈ Icc 1 N, f n ≠ 0 → n.Coprime d) :
    |poolCofactorWeight f P d u A B N-
      (P.card : ℝ)*(coprimeCofactorCount d A B : ℝ)*restrictedMass f N/(d.totient : ℝ)| ≤
      (∑ χ ∈ nonprincipalCharacters d,
        ‖∑ c ∈ P, χ (c : ZMod d)‖*‖∑ a ∈ Icc (A+1) B, χ (a : ZMod d)‖*
          ‖twistedArithmeticSum χ f N‖)/(d.totient : ℝ) := by
  have hφ : (0 : ℝ) < d.totient := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos d)
  have h := Finset.sum_erase_add (univ : Finset (DirichletCharacter ℂ d))
    (fun χ => χ u*(∑ c ∈ P, χ (c : ZMod d))*
      (∑ a ∈ Icc (A+1) B, χ (a : ZMod d))*twistedArithmeticSum χ f N) (mem_univ 1)
  dsimp only at h
  rw [pool_cofactor_orthogonality,unit_pool_principal_sum P d hP,principal_cofactor_character_sum,
    restricted_twisted_principal,unit_supported_nonunitMass_zero f d N hf,sub_zero,
    MulChar.one_apply u.isUnit,one_mul] at h
  have he : (((d.totient : ℝ)*poolCofactorWeight f P d u A B N-
      (P.card : ℝ)*(coprimeCofactorCount d A B : ℝ)*restrictedMass f N : ℝ) : ℂ) =
      ∑ χ ∈ nonprincipalCharacters d, χ u*(∑ c ∈ P, χ (c : ZMod d))*
        (∑ a ∈ Icc (A+1) B, χ (a : ZMod d))*twistedArithmeticSum χ f N := by
    have hs : nonprincipalCharacters d = (univ : Finset (DirichletCharacter ℂ d)).erase 1 := by
      ext χ
      simp only [nonprincipalCharacters,mem_erase,mem_univ,and_true]
    rw [hs]
    push_cast at h ⊢
    linear_combination -h
  have hb : |(d.totient : ℝ)*poolCofactorWeight f P d u A B N-
      (P.card : ℝ)*(coprimeCofactorCount d A B : ℝ)*restrictedMass f N| ≤
      ∑ χ ∈ nonprincipalCharacters d,
        ‖∑ c ∈ P, χ (c : ZMod d)‖*‖∑ a ∈ Icc (A+1) B, χ (a : ZMod d)‖*
          ‖twistedArithmeticSum χ f N‖ := by
    calc
      _ = ‖(((d.totient : ℝ)*poolCofactorWeight f P d u A B N-
          (P.card : ℝ)*(coprimeCofactorCount d A B : ℝ)*restrictedMass f N : ℝ) : ℂ)‖ := by
        rw [Complex.norm_real,Real.norm_eq_abs]
      _ ≤ _ := by
        rw [he]
        apply (norm_sum_le _ _).trans_eq
        simp only [norm_mul,DirichletCharacter.unit_norm_eq_one,one_mul]
  apply (le_div_iff₀ hφ).mpr
  calc
    _ = |(d.totient : ℝ)*poolCofactorWeight f P d u A B N-
        (P.card : ℝ)*(coprimeCofactorCount d A B : ℝ)*restrictedMass f N| := by
      calc
        _ = |(poolCofactorWeight f P d u A B N-
            (P.card : ℝ)*(coprimeCofactorCount d A B : ℝ)*restrictedMass f N/(d.totient : ℝ))*
              (d.totient : ℝ)| := by rw [abs_mul,abs_of_pos hφ]
        _ = _ := by congr 1; field_simp
    _ ≤ _ := hb

end Erdos821.AnalyticSieve
