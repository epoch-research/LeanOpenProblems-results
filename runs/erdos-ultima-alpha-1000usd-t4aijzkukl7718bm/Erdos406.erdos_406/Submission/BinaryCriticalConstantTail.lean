import Submission.BinaryCriticalNonflatZeroTail

/-! When the critical linear slopes cancel, the constant terms still impose
necessary conditions. No certificate or settlement of Erdős 406 is asserted. -/
namespace Erdos406BinaryCriticalRecurrence
open scoped Matrix BigOperators

lemma transient_constant_le (C E τ : ℝ) (hτ : 0 ≤ τ) (hτ1 : τ < 1)
    (h : ∀ k : ℕ, C + E*τ^k ≤ 0) : C ≤ 0 := by
  have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one hτ hτ1).const_mul E
  have hl := ht.const_add C
  simp only [mul_zero, add_zero] at hl
  exact le_of_tendsto' hl h

/-- After cancellation of the leading slopes, boundedness alone is not enough:
the residual mode must tend to zero to compare the constant terms. -/
lemma equal_slope_constant_le (L C E D F τ : ℝ)
    (hτ : 0 ≤ τ) (hτ1 : τ < 1)
    (h : ∀ k : ℕ, L*k+C+E*τ^k ≤ L*k+D+F*τ^k) : C ≤ D := by
  have hh := transient_constant_le (C-D) (E-F) τ hτ hτ1 (by
    intro k
    have hk := h k
    nlinarith)
  linarith
end Erdos406BinaryCriticalRecurrence

namespace Erdos406BinaryCriticalZeroTail
open Erdos406BinaryCriticalGuard Erdos406BinaryCriticalRecurrence
open scoped Matrix BigOperators

/-- Constant-term necessity on the actual binary family 3*2^(6k+6)+1.
The common leading eigenvector may exist, but equality of the resulting
slopes does not remove this next obstruction. -/
theorem zero_tail_equal_slope_constant {N : ℕ}
    (v : ℕ → Fin N → ℝ) (D R : Matrix (Fin N) (Fin N) ℝ)
    (O : Fin 9 → Matrix (Fin N) (Fin N) ℝ)
    (a b z3 z9 u : Fin N → ℝ) (X3 Y3 X9 τ : ℝ)
    (hz : ∀ n, 0 < n → v (2*n) = D *ᵥ v n)
    (ho : ∀ n, 0 < n → v (2*n+1) = O (residueState 2 n) *ᵥ v n)
    (hD : D^6 = (64:ℝ) • R)
    (ha : R *ᵥ a = a) (hb : R *ᵥ b = b + (6:ℝ) • a)
    (hz3 : R *ᵥ z3 = τ • z3) (hz9 : R *ᵥ z9 = τ • z9)
    (hv3 : v 3 = X3 • a + Y3 • b + z3)
    (hv9 : v 9 = X9 • a + (3*Y3) • b + z9)
    (hBp : (O 6*D^5) *ᵥ a = (64:ℝ) • a)
    (hBc : (D^2*O 0*D^3) *ᵥ a = (64:ℝ) • a)
    (hτ : 0 ≤ τ) (hτ1 : τ < 1)
    (hconstruct : ∀ n : ℕ, 0 < n → n%9 = 4 →
      u ⬝ᵥ v (3*n+1) ≤ 3*(u ⬝ᵥ v n)) :
    64*X9*(u ⬝ᵥ a) + 3*Y3*(u ⬝ᵥ ((D^2*O 0*D^3) *ᵥ b)) ≤
      3*(64*X3*(u ⬝ᵥ a) + Y3*(u ⬝ᵥ ((O 6*D^5) *ᵥ b))) := by
  let BP := O 6*D^5
  let BC := D^2*O 0*D^3
  have hmatch (k : ℕ) :
      u ⬝ᵥ (BC *ᵥ ((R^k) *ᵥ v 9)) ≤
        3*(u ⬝ᵥ (BP *ᵥ ((R^k) *ᵥ v 3))) := by
    have hi := hconstruct (tailInput k) (by unfold tailInput; positivity) (tail_residue k)
    obtain ⟨hp, hc⟩ := tail_values v D R O hz ho hD k
    rw [hp, hc, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul] at hi
    apply (mul_le_mul_iff_right₀ (show (0:ℝ) < 64^k by positivity)).mp
    dsimp [BP, BC]
    nlinarith
  apply equal_slope_constant_le (1152*Y3*(u ⬝ᵥ a))
    (64*X9*(u ⬝ᵥ a) + 3*Y3*(u ⬝ᵥ (BC *ᵥ b))) (u ⬝ᵥ (BC *ᵥ z9))
    (3*(64*X3*(u ⬝ᵥ a) + Y3*(u ⬝ᵥ (BP *ᵥ b))))
    (3*(u ⬝ᵥ (BP *ᵥ z3))) τ hτ hτ1
  intro k
  have hi := hmatch k
  rw [hv3, hv9] at hi
  rw [suffix_jordan_scalar N R BC a b z9 u X9 (3*Y3) 6 τ 64 ha hb hz9 hBc,
    suffix_jordan_scalar N R BP a b z3 u X3 Y3 6 τ 64 ha hb hz3 hBp] at hi
  nlinarith

#print axioms Erdos406BinaryCriticalRecurrence.transient_constant_le
#print axioms Erdos406BinaryCriticalRecurrence.equal_slope_constant_le
#print axioms zero_tail_equal_slope_constant
end Erdos406BinaryCriticalZeroTail
