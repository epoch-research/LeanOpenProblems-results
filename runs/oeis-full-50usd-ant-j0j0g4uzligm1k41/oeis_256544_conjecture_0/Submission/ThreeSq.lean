import Mathlib

open scoped BigOperators

/-!
Attempt at the class-number-1 fact for determinant-1 positive-definite integral ternary forms,
as the core of Gauss's three-square theorem.

We represent a symmetric integral Gram matrix by its 6 entries
  Gram = [[a, f, e], [f, b, d], [e, d, c]]
and the associated quadratic form
  Q(x,y,z) = a x² + b y² + c z² + 2 d y z + 2 e x z + 2 f x y.
-/

namespace ThreeSq

/-- Quadratic form value of a 6-coefficient symmetric integral ternary form. -/
def Q (a b c d e f : ℤ) (x y z : ℤ) : ℤ :=
  a*x^2 + b*y^2 + c*z^2 + 2*d*y*z + 2*e*x*z + 2*f*x*y

/-- Determinant of the Gram matrix `[[a,f,e],[f,b,d],[e,d,c]]`. -/
def D (a b c d e f : ℤ) : ℤ :=
  a*(b*c - d^2) - f*(f*c - d*e) + e*(f*d - b*e)

/-- Basic sanity: the standard form is `x²+y²+z²`. -/
example (x y z : ℤ) : Q 1 1 1 0 0 0 x y z = x^2 + y^2 + z^2 := by
  unfold Q; ring

example : D 1 1 1 0 0 0 = 1 := by unfold D; ring

/-- Binary quadratic form value `a x² + 2f xy + b y²`. -/
def Q2 (a b f x y : ℤ) : ℤ := a*x^2 + 2*f*x*y + b*y^2

/-- Reduction of the cross term: there is `k` and `f' = f - a*k` with `2*|f'| ≤ a` (for `a > 0`). -/
lemma reduce_cross (a f : ℤ) (ha : 0 < a) :
    ∃ k : ℤ, 2 * |f - a * k| ≤ a := by
  -- choose k = round(f/a): take r = f % a ∈ [0,a); if 2r ≤ a use k=f/a else k=f/a+1
  refine ⟨if 2 * (f % a) ≤ a then f / a else f / a + 1, ?_⟩
  have hmod : f % a + a * (f / a) = f := by
    have := Int.emod_add_ediv f a; linarith [this]
  have h0 : 0 ≤ f % a := Int.emod_nonneg f (by positivity)
  have h1 : f % a < a := Int.emod_lt_of_pos f ha
  have hexp : a * (f / a + 1) = a * (f / a) + a := by ring
  by_cases hc : 2 * (f % a) ≤ a
  · simp only [hc, if_true]
    have he : f - a * (f / a) = f % a := by omega
    rw [he, abs_of_nonneg h0]; omega
  · simp only [hc, if_false]
    push_neg at hc
    have he : f - a * (f / a + 1) = f % a - a := by omega
    rw [he, abs_of_nonpos (by omega)]; omega

/-- **Binary class number 1 (represents 1).** A positive-definite integral binary form of
determinant 1 represents the value `1`.  Proof by reduction of the leading coefficient. -/
theorem binary_repr_one : ∀ (N : ℕ) (a b f : ℤ), a.toNat = N → 0 < a → a * b - f ^ 2 = 1 →
    ∃ x y : ℤ, Q2 a b f x y = 1 := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro a b f hN ha hdet
    by_cases ha1 : a = 1
    · exact ⟨1, 0, by subst ha1; unfold Q2; ring⟩
    · have ha2 : 2 ≤ a := by omega
      obtain ⟨k, hk⟩ := reduce_cross a f ha
      have hsq : 4 * (f - a * k) ^ 2 ≤ a ^ 2 := by
        nlinarith [hk, abs_nonneg (f - a * k), sq_abs (f - a * k)]
      -- new coefficients after base change (x,y) ↦ (x - k y, y)
      set f' := f - a * k with hf'
      set b'' := a * k ^ 2 - 2 * f * k + b with hb''
      have hdet' : b'' * a - f' ^ 2 = 1 := by rw [hb'', hf']; nlinarith [hdet]
      have hf'sq : 4 * f' ^ 2 ≤ a ^ 2 := by rw [hf']; exact hsq
      have hb''pos : 0 < b'' := by nlinarith [hdet', sq_nonneg f', ha]
      have hb''lt : b'' < a := by nlinarith [hdet', hf'sq, ha2, ha]
      have hlt : b''.toNat < N := by omega
      obtain ⟨X', Y', hXY⟩ := ih b''.toNat hlt b'' a f' rfl hb''pos hdet'
      refine ⟨Y' - k * X', X', ?_⟩
      have e1 : Q2 a b f (Y' - k * X') X' = Q2 a b'' f' Y' X' := by
        rw [hb'', hf']; unfold Q2; ring
      have e2 : Q2 a b'' f' Y' X' = Q2 b'' a f' X' Y' := by unfold Q2; ring
      rw [e1, e2, hXY]

end ThreeSq
