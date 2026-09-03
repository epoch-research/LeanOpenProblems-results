import Submission.BinaryCriticalZeroTailNecessity

/-! Zero-tail slope constraints without a common leading eigenvector.
These are necessary conditions on certificate models, not a proof of Erdős 406. -/
namespace Erdos406BinaryCriticalRecurrence
open scoped Matrix BigOperators

/-- A suffix need not preserve the leading eigenvector. -/
lemma suffix_jordan_scalar_general (N : ℕ) (R B : Matrix (Fin N) (Fin N) ℝ)
    (a b z u : Fin N → ℝ) (X Y β τ : ℝ)
    (ha : R *ᵥ a = a) (hb : R *ᵥ b = b + β • a) (hz : R *ᵥ z = τ • z)
    (n : ℕ) :
    u ⬝ᵥ (B *ᵥ ((R^n) *ᵥ (X • a + Y • b + z))) =
      β*Y*(u ⬝ᵥ (B *ᵥ a))*n +
        (X*(u ⬝ᵥ (B *ᵥ a)) + Y*(u ⬝ᵥ (B *ᵥ b))) +
        τ^n*(u ⬝ᵥ (B *ᵥ z)) := by
  rw [jordan_vector_power N R a b z X Y β τ ha hb hz n]
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add,
    dotProduct_smul, smul_eq_mul]
  ring

/-- For finite minima of affine functions with bounded transients, the
smallest child slope cannot exceed the smallest parent slope. No sign
conditions or proportionality between the slopes are required. -/
theorem finite_affine_transient_slope {ι κ : Type*}
    [Fintype ι] [Nonempty ι] [Fintype κ] [Nonempty κ]
    (a AG EG : ι → ℝ) (c AP EP : κ → ℝ) (τ : ℝ)
    (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hmatch : ∀ n : ℕ, ∀ j, ∃ i,
      a i*n + AG i + EG i*τ^n ≤ c j*n + AP j + EP j*τ^n) :
    ∃ i, ∀ j, a i ≤ c j := by
  classical
  obtain ⟨i₀, _, hi₀⟩ := (Finset.univ : Finset ι).exists_min_image a
    Finset.univ_nonempty
  obtain ⟨i₁, _, hi₁⟩ := (Finset.univ : Finset ι).exists_max_image
    (fun i => |AG i| + |EG i|) Finset.univ_nonempty
  refine ⟨i₀, fun j => ?_⟩
  apply affine_slope_le (a i₀) (|AG i₁| + |EG i₁|) (c j) (AP j + |EP j|)
  intro n
  obtain ⟨i, hi⟩ := hmatch n j
  have hlo := (affine_transient_bounds (a i) (AG i) (EG i) τ hτ hτ1 n).1
  have hup := (affine_transient_bounds (c j) (AP j) (EP j) τ hτ hτ1 n).2
  have hmin := mul_le_mul_of_nonneg_right (hi₀ i (Finset.mem_univ i))
    (Nat.cast_nonneg (α := ℝ) n)
  have hmax := hi₁ i (Finset.mem_univ i)
  have hab := neg_abs_le (AG i)
  linarith

end Erdos406BinaryCriticalRecurrence

namespace Erdos406BinaryCriticalZeroTail
open Erdos406BinaryCriticalGuard Erdos406BinaryCriticalRecurrence
open scoped Matrix BigOperators

/-- The existing all-k binary bridge also applies to non-flat suffixes.
The child and parent may have different finite observer families. -/
theorem zero_tail_suffix_necessary {N : ℕ} {ι κ : Type*}
    [Fintype ι] [Nonempty ι] [Fintype κ] [Nonempty κ]
    (v : ℕ → Fin N → ℝ) (D R : Matrix (Fin N) (Fin N) ℝ)
    (O : Fin 9 → Matrix (Fin N) (Fin N) ℝ)
    (a b z3 z9 : Fin N → ℝ) (X3 Y3 X9 Y9 τ : ℝ)
    (uC : ι → Fin N → ℝ) (uP : κ → Fin N → ℝ)
    (hz : ∀ n, 0 < n → v (2*n) = D *ᵥ v n)
    (ho : ∀ n, 0 < n → v (2*n+1) = O (residueState 2 n) *ᵥ v n)
    (hD : D^6 = (64:ℝ) • R)
    (ha : R *ᵥ a = a) (hb : R *ᵥ b = b + (6:ℝ) • a)
    (hz3 : R *ᵥ z3 = τ • z3) (hz9 : R *ᵥ z9 = τ • z9)
    (hv3 : v 3 = X3 • a + Y3 • b + z3)
    (hv9 : v 9 = X9 • a + Y9 • b + z9)
    (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hconstruct : ∀ n : ℕ, 0 < n → n%9 = 4 → ∀ j, ∃ i,
      uC i ⬝ᵥ v (3*n+1) ≤ 3*(uP j ⬝ᵥ v n)) :
    ∃ i, ∀ j, Y9*(uC i ⬝ᵥ ((D^2*O 0*D^3) *ᵥ a)) ≤
      3*Y3*(uP j ⬝ᵥ ((O 6*D^5) *ᵥ a)) := by
  let BP := O 6*D^5
  let BC := D^2*O 0*D^3
  have hmatch (k : ℕ) (j : κ) : ∃ i,
      uC i ⬝ᵥ (BC *ᵥ ((R^k) *ᵥ v 9)) ≤
        3*(uP j ⬝ᵥ (BP *ᵥ ((R^k) *ᵥ v 3))) := by
    obtain ⟨i, hi⟩ := hconstruct (tailInput k) (by unfold tailInput; positivity)
      (tail_residue k) j
    obtain ⟨hp, hc⟩ := tail_values v D R O hz ho hD k
    rw [hp, hc, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul] at hi
    refine ⟨i, ?_⟩
    apply (mul_le_mul_iff_right₀ (show (0:ℝ) < 64^k by positivity)).mp
    dsimp [BP, BC]
    nlinarith
  obtain ⟨i, hi⟩ := finite_affine_transient_slope
    (fun i => 6*Y9*(uC i ⬝ᵥ (BC *ᵥ a)))
    (fun i => X9*(uC i ⬝ᵥ (BC *ᵥ a)) + Y9*(uC i ⬝ᵥ (BC *ᵥ b)))
    (fun i => uC i ⬝ᵥ (BC *ᵥ z9))
    (fun j => 18*Y3*(uP j ⬝ᵥ (BP *ᵥ a)))
    (fun j => 3*(X3*(uP j ⬝ᵥ (BP *ᵥ a)) + Y3*(uP j ⬝ᵥ (BP *ᵥ b))))
    (fun j => 3*(uP j ⬝ᵥ (BP *ᵥ z3))) τ hτ hτ1 (by
      intro k j
      obtain ⟨i, hi⟩ := hmatch k j
      rw [hv3, hv9] at hi
      rw [suffix_jordan_scalar_general N R BC a b z9 (uC i) X9 Y9 6 τ ha hb hz9,
        suffix_jordan_scalar_general N R BP a b z3 (uP j) X3 Y3 6 τ ha hb hz3] at hi
      exact ⟨i, by nlinarith⟩)
  refine ⟨i, fun j => ?_⟩
  have h := hi j
  change Y9*(uC i ⬝ᵥ (BC *ᵥ a)) ≤ 3*Y3*(uP j ⬝ᵥ (BP *ᵥ a))
  linarith

#print axioms Erdos406BinaryCriticalRecurrence.suffix_jordan_scalar_general
#print axioms Erdos406BinaryCriticalRecurrence.finite_affine_transient_slope
#print axioms zero_tail_suffix_necessary
end Erdos406BinaryCriticalZeroTail
