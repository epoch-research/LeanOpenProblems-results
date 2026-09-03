import Submission.BinaryCriticalPhaseCycleSlope

/-! Affine-plus-decaying-mode slope comparisons for long binary zero blocks.
These are generic obstruction lemmas, not a settlement of Erdős 406. -/
namespace Erdos406BinaryCriticalRecurrence
open scoped Matrix BigOperators

lemma affine_transient_bounds (D A E τ : ℝ) (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (n : ℕ) :
    D*n+A-|E| ≤ D*n+A+E*τ^n ∧ D*n+A+E*τ^n ≤ D*n+A+|E| := by
  have hp : 0 ≤ τ^n := pow_nonneg hτ n
  have hp1 : τ^n ≤ 1 := pow_le_one₀ hτ hτ1
  have hab : |E*τ^n| ≤ |E| := by
    rw [abs_mul, abs_of_nonneg hp]
    simpa using mul_le_mul_of_nonneg_left hp1 (abs_nonneg E)
  have hh := abs_le.mp hab
  constructor <;> linarith [hh.1,hh.2]

/-- A finite family may use different observers at different inputs, but
bounded transient terms cannot defeat the least-leading-coefficient test. -/
theorem affine_transient_minimum_slope {ι : Type*} [Fintype ι] [Nonempty ι]
    (x AP EP AG EG : ι → ℝ) (hx : ∀ i, 0 < x i)
    (a c τ : ℝ) (ha : 0 ≤ a) (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hmatch : ∀ n : ℕ, ∀ j, ∃ i,
      a*x i*n+AG i+EG i*τ^n ≤ c*x j*n+AP j+EP j*τ^n) : a ≤ c := by
  classical
  obtain ⟨j,_,hj⟩ := (Finset.univ : Finset ι).exists_max_image
    (fun i => |AG i|+|EG i|) Finset.univ_nonempty
  let B : ℝ := |AG j|+|EG j|
  apply minimum_coefficient_slope_lower x hx a c B ha
    (fun i n => c*x i*n+AP i+EP i*τ^n)
    (fun i n => a*x i*n+AG i+EG i*τ^n)
    (fun i => AP i+|EP i|) ?_ ?_ hmatch
  · intro i n
    have hb : |AG i|+|EG i| ≤ B := hj i (Finset.mem_univ i)
    have hh := (affine_transient_bounds (a*x i) (AG i) (EG i) τ hτ hτ1 n).1
    have hA := neg_abs_le (AG i)
    linarith
  · intro i n
    have hh := (affine_transient_bounds (c*x i) (AP i) (EP i) τ hτ hτ1 n).2
    linarith

/-- An exact critical Jordan block plus one decaying vector mode. The vector
`z` can have arbitrarily many coordinates; it need only be a τ-eigenvector. -/
lemma jordan_vector_power (N : ℕ) (R : Matrix (Fin N) (Fin N) ℝ)
    (a b z : Fin N → ℝ) (X Y β τ : ℝ)
    (ha : R *ᵥ a=a) (hb : R *ᵥ b=b+β • a) (hz : R *ᵥ z=τ • z)
    (n : ℕ) :
    (R^n)*ᵥ (X • a+Y • b+z) =
      (X+n*β*Y) • a+Y • b+τ^n • z := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec, ih]
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, ha, hb, hz,
      smul_add, smul_smul, Nat.cast_add, Nat.cast_one, pow_succ']
    module

/-- A fixed suffix preserving the leading eigenvector preserves its linear
coefficient. This is the algebra behind zero-block slope extraction. -/
lemma suffix_jordan_scalar (N : ℕ) (R B : Matrix (Fin N) (Fin N) ℝ)
    (a b z u : Fin N → ℝ) (X Y β τ κ : ℝ)
    (ha : R *ᵥ a=a) (hb : R *ᵥ b=b+β • a) (hz : R *ᵥ z=τ • z)
    (hB : B *ᵥ a=κ • a) (n : ℕ) :
    u ⬝ᵥ (B *ᵥ ((R^n)*ᵥ (X • a+Y • b+z))) =
      κ*β*Y*(u ⬝ᵥ a)*n +
        (κ*X*(u ⬝ᵥ a)+Y*(u ⬝ᵥ (B *ᵥ b))) + τ^n*(u ⬝ᵥ (B *ᵥ z)) := by
  rw [jordan_vector_power N R a b z X Y β τ ha hb hz n]
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, hB, dotProduct_add,
    dotProduct_smul, smul_smul, smul_eq_mul]
  ring

#print axioms affine_transient_minimum_slope
#print axioms jordan_vector_power
#print axioms suffix_jordan_scalar
end Erdos406BinaryCriticalRecurrence
