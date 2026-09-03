import FormalConjecturesUtil

/-!
# Quadratic characters and finite extension norms

Auxiliary finite-field results only; this file does not settle Erdős Problem 66.
-/

namespace Erdos66CharacterNorm

variable {K L : Type*} [Field K] [Field L] [Fintype K] [Fintype L]
  [DecidableEq K] [DecidableEq L] [Algebra K L]

lemma ringChar_eq_of_algebra : ringChar L = ringChar K := by
  letI : CharP L (ringChar K) := charP_of_injective_algebraMap' K (ringChar K)
  exact ringChar.eq L _

lemma half_card_norm_exponent (hK : ringChar K ≠ 2) (hL : ringChar L ≠ 2) :
    ((Fintype.card L - 1) / (Fintype.card K - 1)) * (Fintype.card K / 2) =
      Fintype.card L / 2 := by
  have hd : Fintype.card K - 1 ∣ Fintype.card L - 1 := by
    rw [Module.card_eq_pow_finrank (K := K) (V := L)]
    exact Nat.sub_one_dvd_pow_sub_one _ _
  have hk := FiniteField.odd_card_of_char_ne_two hK
  have hl := FiniteField.odd_card_of_char_ne_two hL
  have hmul := Nat.div_mul_cancel hd
  have hk' : Fintype.card K - 1 = 2 * (Fintype.card K / 2) := by omega
  have hl' : Fintype.card L - 1 = 2 * (Fintype.card L / 2) := by omega
  rw [hk', hl'] at hmul ⊢
  nlinarith

lemma quadraticChar_norm (hK : ringChar K ≠ 2) (hL : ringChar L ≠ 2) (x : L) :
    quadraticChar L x = quadraticChar K (Algebra.norm K x) := by
  apply MulChar.IsQuadratic.eq_of_eq_coe (quadraticChar_isQuadratic L)
    (quadraticChar_isQuadratic K) hL
  calc
    (quadraticChar L x : L) = x ^ (Fintype.card L / 2) :=
      quadraticChar_eq_pow_of_char_ne_two' hL x
    _ = (algebraMap K L (Algebra.norm K x)) ^ (Fintype.card K / 2) := by
      rw [FiniteField.algebraMap_norm_eq_pow,
        Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
      rw [← pow_mul, half_card_norm_exponent hK hL]
    _ = algebraMap K L ((quadraticChar K (Algebra.norm K x) : K)) := by
      rw [quadraticChar_eq_pow_of_char_ne_two' hK, map_pow]
    _ = (quadraticChar K (Algebra.norm K x) : L) := by simp

lemma quadraticChar_odd_extension (hK : ringChar K ≠ 2) (hL : ringChar L ≠ 2)
    (hdeg : Odd (Module.finrank K L)) (x : K) :
    quadraticChar L (algebraMap K L x) = quadraticChar K x := by
  rw [quadraticChar_norm hK hL, Algebra.norm_algebraMap, map_pow]
  rcases quadraticChar_isQuadratic K x with h | h | h
  · rw [h, zero_pow hdeg.pos.ne']
  · simp [h]
  · rw [h, hdeg.neg_one_pow]

lemma quadratic_root_frobenius (hK : ringChar K ≠ 2) (ν : K) (hν : ¬IsSquare ν)
    (α : L) (hα : α ^ 2 = algebraMap K L ν) :
    α ^ Fintype.card K = -α := by
  have hk := FiniteField.odd_card_of_char_ne_two hK
  have hp : Fintype.card K = 2 * (Fintype.card K / 2) + 1 := by omega
  have hpow : ν ^ (Fintype.card K / 2) = -1 := by
    rw [← quadraticChar_eq_pow_of_char_ne_two' hK,
      quadraticChar_neg_one_iff_not_isSquare.mpr hν]
    simp
  rw [hp, pow_succ, pow_mul, hα, ← map_pow, hpow]
  simp

lemma norm_quadratic_coset (hK : ringChar K ≠ 2)
    (hcard : Fintype.card L = Fintype.card K ^ 2)
    (ν : K) (hν : ¬IsSquare ν) (α : L) (hα : α ^ 2 = algebraMap K L ν) (x : K) :
    Algebra.norm K (α + algebraMap K L x) = x ^ 2 - ν := by
  have hq : (Fintype.card L - 1) / (Fintype.card K - 1) = Fintype.card K + 1 := by
    have hk := Fintype.one_lt_card (α := K)
    have hh : Fintype.card K ^ 2 - 1 =
        (Fintype.card K + 1) * (Fintype.card K - 1) := by
      cases Fintype.card K with
      | zero => omega
      | succ k => simp; ring_nf; omega
    rw [hcard, hh, Nat.mul_div_left _ (by omega)]
  apply (algebraMap K L).injective
  rw [FiniteField.algebraMap_norm_eq_pow,
    Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, hq, pow_succ]
  have hf : (α + algebraMap K L x) ^ Fintype.card K = -α + algebraMap K L x := by
    calc
      _ = FiniteField.frobeniusAlgHom K L (α + algebraMap K L x) := rfl
      _ = FiniteField.frobeniusAlgHom K L α + algebraMap K L x := by
        rw [map_add, AlgHom.commutes]
      _ = _ := by rw [FiniteField.frobeniusAlgHom_apply, quadratic_root_frobenius hK ν hν α hα]
  rw [hf, map_sub, map_pow, ← hα]
  ring

lemma quadraticChar_quadratic_coset (hK : ringChar K ≠ 2) (hL : ringChar L ≠ 2)
    (hcard : Fintype.card L = Fintype.card K ^ 2)
    (ν : K) (hν : ¬IsSquare ν) (α : L) (hα : α ^ 2 = algebraMap K L ν) (x : K) :
    quadraticChar L (α + algebraMap K L x) = quadraticChar K (x ^ 2 - ν) := by
  rw [quadraticChar_norm hK hL, norm_quadratic_coset hK hcard ν hν α hα]

end Erdos66CharacterNorm
