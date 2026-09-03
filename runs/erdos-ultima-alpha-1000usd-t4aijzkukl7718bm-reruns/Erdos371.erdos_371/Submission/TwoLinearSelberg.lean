import FormalConjecturesUtil
import Submission.ResidueSelberg
import Submission.SieveEulerProduct

/-! A coefficient-uniform two-linear-form sieve with a polynomial threshold.
The estimate is unsigned and makes no assertion about prime-factor orientation. -/

namespace Erdos371TwoLinearSelberg

open Finset Erdos371FiniteBrun Erdos371ResidueSieve Erdos371ResidueSelberg
  Erdos371TwoLinearSieve Erdos371SieveEulerProduct

attribute [local instance] Classical.propDecidable

noncomputable def oddPrimes (w : ℕ) := w.primesBelow.erase 2

lemma mem_oddPrimes {p w : ℕ} : p ∈ oddPrimes w ↔ p < w ∧ p.Prime ∧ p ≠ 2 := by
  simp [oddPrimes, Nat.mem_primesBelow, and_comm, and_left_comm, and_assoc]

lemma oddPrimes_subset (w : ℕ) : oddPrimes w ⊆ w.primesBelow := erase_subset _ _

lemma oddPrimes_prime {p w : ℕ} (hp : p ∈ oddPrimes w) : p.Prime := (mem_oddPrimes.mp hp).2.1

lemma oddPrimes_gt_two {p w : ℕ} (hp : p ∈ oddPrimes w) : 2 < p := by
  have hh := mem_oddPrimes.mp hp
  have h2 := hh.2.1.two_le
  omega

lemma euler_oddPrimes {w : ℕ} (hw : 2 < w) :
    euler (oddPrimes w) = 2*euler w.primesBelow := by
  have h2 : 2 ∈ w.primesBelow := Nat.mem_primesBelow.mpr ⟨hw, Nat.prime_two⟩
  have hh : euler w.primesBelow = (1/2:ℝ)*euler (oddPrimes w) := by
    conv_lhs => rw [← insert_erase h2]
    simp only [euler, prod_insert (notMem_erase _ _), oddPrimes]
    norm_num
  linarith

lemma euler_oddPrimes_le {w : ℕ} (hw : 2 < w) :
    euler (oddPrimes w) ≤ 2/Real.log w := by
  rw [euler_oddPrimes hw]
  have hh := euler_le_inverse_log (by omega : 1<w)
  simp only [div_eq_mul_inv] at hh ⊢
  linarith

lemma weight_one_le {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) (a : ℕ) :
    1 ≤ weight s a := by
  calc
    _ = ∏ _p ∈ s, (1:ℝ) := prod_const_one.symm
    _ ≤ _ := by
      apply prod_le_prod (fun _ _ => zero_le_one)
      intro p hp
      split_ifs
      · exact (one_le_inv₀ (prime_factor_pos (hs p hp))).mpr prime_factor_le_one
      · rfl

lemma linear_product_bound {w : ℕ} (hw : 2 < w) (a c : ℕ) :
    (∏ p ∈ oddPrimes w, (1-linearDensity a c p)) ≤
      4*weight (oddPrimes w) a * weight (oddPrimes w) c / (Real.log w)^2 := by
  have hs : ∀ p ∈ oddPrimes w, p.Prime := fun p hp => oddPrimes_prime hp
  have he := euler_oddPrimes_le hw
  have he0 := (euler_pos hs).le
  have hwac := weight_nonneg hs (a*c)
  calc
    _ ≤ (euler (oddPrimes w))^2 * weight (oddPrimes w) (a*c) := linear_euler_le hs a c
    _ ≤ (2/Real.log w)^2 * (weight (oddPrimes w) a * weight (oddPrimes w) c) :=
      mul_le_mul (pow_le_pow_left₀ he0 he 2) (weight_mul_le hs a c) hwac (sq_nonneg _)
    _ = _ := by ring

/-- Finite Selberg bound before absorbing the cutoff error. -/
theorem two_linear_selberg_finite {a b c d w : ℕ} (hw : 2 < w)
    (hdet : determinantOne a b c d) (N : ℕ) :
    (primeInputs (oddPrimes w) a b c d N).card ≤
      8*(N:ℝ)*weight (oddPrimes w) a * weight (oddPrimes w) c/(Real.log w)^2 +
        (4*(w:ℝ))^16 := by
  have hs : ∀ p ∈ oddPrimes w, p.Prime := fun p hp => oddPrimes_prime hp
  have hb := residue_selberg_upper (by omega : 0<w) (oddPrimes_subset w)
    (linearResidues a b c d)
    (fun p hp => linearResidues_subset _ _ _ _ _)
    (by intro p hp; rw [linearResidues_card (hs p hp) hdet]; split_ifs <;> omega)
    (by intro p hp; rw [linearResidues_card (hs p hp) hdet]; have := oddPrimes_gt_two hp; split_ifs <;> omega)
    (by intro p hp; rw [linearResidues_card (hs p hp) hdet]; split_ifs <;> omega) N
  have hprod : (∏ p ∈ oddPrimes w, (1-localDensity (linearResidues a b c d) p)) =
      ∏ p ∈ oddPrimes w, (1-linearDensity a c p) := by
    apply prod_congr rfl
    intro p hp
    rw [localDensity_linearResidues (hs p hp) hdet]
  rw [hprod] at hb
  apply (Nat.cast_le.mpr (card_le_card (primeInputs_subset_survivors hs a b c d N))).trans
  apply hb.trans
  have hh := mul_le_mul_of_nonneg_left (linear_product_bound hw a c)
    (show (0:ℝ) ≤ 2*N by positivity)
  simp only [div_eq_mul_inv] at hh ⊢
  nlinarith

lemma error_absorbed {w N : ℕ} (hw : 2 < w) (hN : (4*w)^20 ≤ N) :
    (4*(w:ℝ))^16 ≤ (N:ℝ)/(Real.log w)^2 := by
  have hw0 : (0:ℝ) < w := Nat.cast_pos.mpr (by omega)
  have hw1 : (1:ℝ) ≤ w := by exact_mod_cast (show 1≤w by omega)
  have hl0 : 0 < Real.log w := Real.log_pos (by exact_mod_cast (show 1<w by omega))
  have hl : Real.log w ≤ (w:ℝ) := (Real.log_le_sub_one_of_pos hw0).trans (by linarith)
  have hlsq : (Real.log w)^2 ≤ (w:ℝ)^2 := pow_le_pow_left₀ hl0.le hl 2
  have hpow : (w:ℝ)^2 ≤ (4*(w:ℝ))^4 := by nlinarith [sq_nonneg ((w:ℝ)^2-1)]
  apply (le_div_iff₀ (sq_pos_of_pos hl0)).mpr
  calc
    _ ≤ (4*(w:ℝ))^16 * (4*(w:ℝ))^4 :=
      mul_le_mul_of_nonneg_left (hlsq.trans hpow) (by positivity)
    _ = (4*(w:ℝ))^20 := by ring
    _ ≤ _ := by exact_mod_cast hN

/-- An upper sieve with no iterated-logarithm loss. The only threshold is
`N ≥ (4w)^20`, and the coefficient factors have a bounded average. -/
theorem two_linear_selberg_upper {a b c d w N : ℕ} (hw : 2 < w)
    (hdet : determinantOne a b c d) (hN : (4*w)^20 ≤ N) :
    (primeInputs (oddPrimes w) a b c d N).card ≤
      9*(N:ℝ)*weight (oddPrimes w) a * weight (oddPrimes w) c/(Real.log w)^2 := by
  have hb := two_linear_selberg_finite hw hdet N
  have he := error_absorbed hw hN
  have hs : ∀ p ∈ oddPrimes w, p.Prime := fun p hp => oddPrimes_prime hp
  have hwa := weight_one_le hs a
  have hwc := weight_one_le hs c
  have hwac : 1 ≤ weight (oddPrimes w) a * weight (oddPrimes w) c := by nlinarith
  have hratio0 : (0:ℝ) ≤ (N:ℝ)/(Real.log w)^2 := by positivity
  have hh := mul_le_mul_of_nonneg_left hwac hratio0
  simp only [div_eq_mul_inv] at hb he hh ⊢
  nlinarith

end Erdos371TwoLinearSelberg

#print axioms Erdos371TwoLinearSelberg.two_linear_selberg_upper
