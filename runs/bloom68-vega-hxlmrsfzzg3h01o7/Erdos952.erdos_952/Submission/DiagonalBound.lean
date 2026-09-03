import Submission.DiagonalArithmetic
import Submission.DiagonalCertificate

/-!
# A diagonal-step obstruction for Gaussian-prime walks

There is no injective Gaussian-prime sequence with squared step norms `< C`
when `C ≤ 4`. After removing finitely many primes of norms 2, 5 and 13,
parity leaves only diagonal steps. A kernel-checked exact potential on
`Fin 65 × Fin 65` rules out an injective walk using those steps.

This is a partial small-bound result, not a claim about arbitrary step bounds
or a solution of the Gaussian moat problem. None of these modules imports
`Submission.Spec`.
-/

namespace Erdos952
namespace DiagonalBound

@[simp]
theorem reduce_val (x : ℤ) : ((reduce x).val : ℤ) = x % 65 := by
  exact Int.toNat_of_nonneg (Int.emod_nonneg x (by norm_num : (65 : ℤ) ≠ 0))

/-- Reduction commutes with translation, including negative coordinates. -/
theorem reduce_add (x y : ℤ) : reduce (x + y) = reduce ((reduce x).val + y) := by
  apply Fin.ext
  apply Int.ofNat_inj.mp
  simp only [reduce_val, Int.add_emod, Int.emod_emod]

/-- Actual diagonal steps induce precisely the transitions used in the table. -/
theorem residue_add_step (p : GaussianInt) (u v : Bool) :
    residue (p + step u v) = next (residue p) u v := by
  change (reduce (p.re + sign u), reduce (p.im + sign v)) =
    (reduce ((reduce p.re).val + sign u), reduce ((reduce p.im).val + sign v))
  exact Prod.ext (reduce_add _ _) (reduce_add _ _)

/-- The arithmetic congruences descend to the 65-by-65 residue type. Parity
need not descend: it is used separately to classify the possible steps. -/
theorem sieved_of_prime {p : GaussianInt} (hp : Prime p) (he : p ∉ exceptions) :
    Sieved (residue p) := by
  have hre5 : p.re % 65 ≡ p.re [ZMOD 5] :=
    (Int.mod_modEq p.re 65).of_dvd (by norm_num : (5 : ℤ) ∣ 65)
  have him5 : p.im % 65 ≡ p.im [ZMOD 5] :=
    (Int.mod_modEq p.im 65).of_dvd (by norm_num : (5 : ℤ) ∣ 65)
  have hre13 : p.re % 65 ≡ p.re [ZMOD 13] :=
    (Int.mod_modEq p.re 65).of_dvd (by norm_num : (13 : ℤ) ∣ 65)
  have him13 : p.im % 65 ≡ p.im [ZMOD 13] :=
    (Int.mod_modEq p.im 65).of_dvd (by norm_num : (13 : ℤ) ∣ 65)
  have h₁ : (p.re % 65 + 2 * (p.im % 65)) % 5 = (p.re + 2 * p.im) % 5 :=
    hre5.add ((Int.ModEq.refl 2).mul him5)
  have h₂ : (p.re % 65 - 2 * (p.im % 65)) % 5 = (p.re - 2 * p.im) % 5 :=
    hre5.sub ((Int.ModEq.refl 2).mul him5)
  have h₃ : (p.re % 65 + 5 * (p.im % 65)) % 13 = (p.re + 5 * p.im) % 13 :=
    hre13.add ((Int.ModEq.refl 5).mul him13)
  have h₄ : (p.re % 65 - 5 * (p.im % 65)) % 13 = (p.re - 5 * p.im) % 13 :=
    hre13.sub ((Int.ModEq.refl 5).mul him13)
  simpa only [Sieved, residue, reduce_val, h₁, h₂, h₃, h₄] using prime_congruences hp he

/-- The finite certificate lifted back to actual Gaussian integers. -/
theorem potential_difference_of_step {p q : GaussianInt} {u v : Bool}
    (hp : Sieved (residue p)) (hq : Sieved (residue q))
    (hs : q - p = step u v) :
    q - p = potential (residue q) - potential (residue p) := by
  have hqeq : q = p + step u v := by
    simpa only [add_comm] using sub_eq_iff_eq_add.mp hs
  have hres : residue q = next (residue p) u v := by
    rw [hqeq]
    exact residue_add_step _ _ _
  rw [hres] at hq ⊢
  exact hs.trans (certificate _ _ _ _ hp hq).symm

/-- Local exact-potential identity for any two nonexceptional Gaussian primes
at squared distance less than four, including the zero-displacement case. -/
theorem prime_potential_difference {p q : GaussianInt} (hp : Prime p) (hq : Prime q)
    (hpe : p ∉ exceptions) (hqe : q ∉ exceptions) (hs : (q - p).norm < 4) :
    q - p = potential (residue q) - potential (residue p) := by
  have hpS := sieved_of_prime hp hpe
  have hqS := sieved_of_prime hq hqe
  have he := even_sub_of_odd (prime_odd hp hpe) (prime_odd hq hqe)
  rcases zero_or_diagonal_of_even_of_norm_lt_four he hs with hz | h₁ | h₂ | h₃ | h₄
  · rw [sub_eq_zero.mp hz]
    simp
  · exact potential_difference_of_step (u := true) (v := true) hpS hqS
      (by simpa only [step, sign, Bool.true_eq, ↓reduceIte] using h₁)
  · exact potential_difference_of_step (u := true) (v := false) hpS hqS
      (by simpa only [step, sign, Bool.true_eq, Bool.false_eq_true, ↓reduceIte] using h₂)
  · exact potential_difference_of_step (u := false) (v := true) hpS hqS
      (by simpa only [step, sign, Bool.true_eq, Bool.false_eq_true, ↓reduceIte] using h₃)
  · exact potential_difference_of_step (u := false) (v := false) hpS hqS
      (by simpa only [step, sign, Bool.false_eq_true, ↓reduceIte] using h₄)

end DiagonalBound

/-- Unconditional diagonal-bound obstruction. This is only the case `C ≤ 4`,
not an assertion excluding every constant in the Gaussian moat problem. -/
theorem no_bounded_step_sequence_of_bound_le_four {C : ℤ} (hC : C ≤ 4) :
    ¬ ∃ x : ℕ → GaussianInt, Function.Injective x ∧
      ∀ n, Prime (x n) ∧ (x (n + 1) - x n).norm < C := by
  apply no_bounded_step_sequence_of_finite_potential
    DiagonalBound.residue DiagonalBound.potential
    DiagonalBound.exceptions DiagonalBound.finite_exceptions C
  intro p q hp hq hpe hqe hs
  exact DiagonalBound.prime_potential_difference hp hq hpe hqe (lt_of_lt_of_le hs hC)

/-- Any injective bounded-step Gaussian-prime sequence would require an
integral strict squared-norm bound of at least five. -/
theorem five_le_bound_of_witness {C : ℤ}
    (h : ∃ x : ℕ → GaussianInt, Function.Injective x ∧
      ∀ n, Prime (x n) ∧ (x (n + 1) - x n).norm < C) : 5 ≤ C := by
  by_contra hC
  exact no_bounded_step_sequence_of_bound_le_four (by omega) h

end Erdos952
