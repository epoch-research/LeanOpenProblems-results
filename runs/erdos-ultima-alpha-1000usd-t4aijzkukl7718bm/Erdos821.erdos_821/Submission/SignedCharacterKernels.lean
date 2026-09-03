import Submission.CompositeCharacterErrors

/-!
# Exact local signed character kernels

The local nonprincipal character aggregate has an elementary real formula.
Products retain signs, unlike the absolute-character bounds. An exact example
shows that even-order products need not have nonnegative Mangoldt-weighted
averages; no positivity hypothesis is available for free.
-/

open Nat Finset ArithmeticFunction
open scoped Classical BigOperators

namespace Erdos821.AnalyticSieve

noncomputable def localNonprincipalKernel (q n : ℕ) : ℝ :=
  (if (n : ZMod q) = 1 then (q.totient : ℝ) else 0) -
    (if n.Coprime q then 1 else 0)

lemma localNonprincipalKernel_eq_mod (q n : ℕ) :
    localNonprincipalKernel q n =
      (if n % q = 1 % q then (q.totient : ℝ) else 0) - (if n.Coprime q then 1 else 0) := by
  unfold localNonprincipalKernel
  have he : (n : ZMod q) = 1 ↔ n % q = 1 % q := by
    simpa only [Nat.cast_one] using ZMod.natCast_eq_natCast_iff' n 1 q
  simp only [he]

/-- The principal character subtraction is essential, including at nonunits. -/
theorem nonprincipal_character_sum_eq_kernel (q n : ℕ) [NeZero q] :
    (∑ χ ∈ nonprincipalCharacters q, χ (n : ZMod q)) =
      (localNonprincipalKernel q n : ℂ) := by
  have h := sum_erase_add (univ : Finset (DirichletCharacter ℂ q))
    (fun χ => χ (n : ZMod q)) (mem_univ 1)
  have hs : nonprincipalCharacters q = (univ : Finset (DirichletCharacter ℂ q)).erase 1 := by
    ext χ
    simp only [nonprincipalCharacters, mem_erase, mem_univ, and_true]
  dsimp only at h
  rw [← hs, DirichletCharacter.sum_characters_eq, principal_character_nat] at h
  unfold localNonprincipalKernel
  push_cast
  split_ifs at h ⊢ <;> push_cast <;> linear_combination h

noncomputable def signedLocalKernelSum (P : Finset ℕ) (N : ℕ) : ℝ :=
  ∑ n ∈ Icc 1 N, vonMangoldt n * ∏ q ∈ P, localNonprincipalKernel q n

/-- Finite signed products may be formed before estimating their averages. -/
theorem product_nonprincipal_sums_eq_kernel (P : Finset ℕ)
    (hP : ∀ q ∈ P, 0 < q) (n : ℕ) :
    (∏ q ∈ P, ∑ χ ∈ nonprincipalCharacters q, χ (n : ZMod q)) =
      ((∏ q ∈ P, localNonprincipalKernel q n : ℝ) : ℂ) := by
  rw [Complex.ofReal_prod]
  apply prod_congr rfl
  intro q hq
  letI : NeZero q := ⟨(hP q hq).ne'⟩
  exact nonprincipal_character_sum_eq_kernel q n

/-- Even a product of two prime-modulus kernels can have a negative
Mangoldt-weighted average. This is not a disproof of the original conjecture. -/
theorem signed_local_kernel_sum_three_five :
    signedLocalKernelSum {3, 5} 7 = -Real.log 7 := by
  have hI : Icc 1 7 = ({1, 2, 3, 4, 5, 6, 7} : Finset ℕ) := by decide
  have hφ3 : Nat.totient 3 = 2 := by simpa using Nat.totient_prime (by decide : Nat.Prime 3)
  have hφ5 : Nat.totient 5 = 4 := by simpa using Nat.totient_prime (by decide : Nat.Prime 5)
  have hΛ2 := vonMangoldt_apply_prime Nat.prime_two
  have hΛ4 : vonMangoldt 4 = Real.log 2 := by
    rw [show 4 = 2 ^ 2 by norm_num, vonMangoldt_apply_pow (by decide : (2 : ℕ) ≠ 0)]
    exact hΛ2
  have hΛ7 := vonMangoldt_apply_prime (by decide : Nat.Prime 7)
  unfold signedLocalKernelSum
  rw [hI]
  norm_num [localNonprincipalKernel_eq_mod, hφ3, hφ5, hΛ2, hΛ4, hΛ7]

lemma signed_local_kernel_sum_three_five_neg :
    signedLocalKernelSum {3, 5} 7 < 0 := by
  rw [signed_local_kernel_sum_three_five]
  have h := Real.log_pos (by norm_num : (1 : ℝ) < 7)
  linarith

end Erdos821.AnalyticSieve
