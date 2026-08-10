import FormalConjectures.Util.ProblemImports

open Nat

namespace TSQ

/-- Centered remainder: there is `k` with `c - a*k` small. -/
theorem centered (a c : ℤ) (ha : 0 < a) :
    ∃ k : ℤ, -a < 2*(c - a*k) ∧ 2*(c - a*k) ≤ a := by
  have hr : 0 ≤ c % a := Int.emod_nonneg c (ne_of_gt ha)
  have hr2 : c % a < a := Int.emod_lt_of_pos c ha
  have hdm : a * (c / a) + c % a = c := Int.ediv_add_emod c a
  by_cases h : 2 * (c % a) ≤ a
  · exact ⟨c / a, by omega⟩
  · exact ⟨c / a + 1, by constructor <;> nlinarith [hr, hr2, hdm, h]⟩

/-- A positive-definite integral binary form `a x² + 2c xy + b y²` of determinant 1
represents 1. -/
theorem binary_repr_one : ∀ N : ℕ, ∀ a b c : ℤ, a.toNat = N → 0 < a → a * b - c^2 = 1 →
    ∃ x y : ℤ, a * x^2 + 2*c*x*y + b * y^2 = 1 := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro a b c hN ha hdet
    -- a ≥ 1
    by_cases h1 : a = 1
    · exact ⟨1, 0, by subst h1; ring⟩
    · -- a ≥ 2
      have ha2 : 2 ≤ a := by omega
      obtain ⟨k, hk1, hk2⟩ := centered a c ha
      set c' : ℤ := c - a * k with hc'
      set b'' : ℤ := b - 2*c*k + a*k^2 with hb''
      -- new form (a, b'', c') has det 1
      have hdet' : a * b'' - c'^2 = 1 := by rw [hb'', hc']; linear_combination hdet
      -- b'' positive
      have hb''pos : 0 < b'' := by nlinarith [hdet', sq_nonneg c']
      -- b'' < a
      have hcsq : 4 * c'^2 ≤ a^2 := by nlinarith [hk1, hk2]
      have hb''lt : b'' < a := by nlinarith [hdet', hcsq, ha2, hb''pos]
      -- recurse on swapped form (b'', a, c')
      have hb''nat : b''.toNat < N := by omega
      obtain ⟨X, Y, hXY⟩ := ih b''.toNat hb''nat b'' a c' rfl hb''pos (by linear_combination hdet')
      -- (b'', a, c') represents 1 at (X,Y);  (a, b'', c') represents 1 at (Y,X)
      -- original represents 1 at (Y - k*X, X)
      refine ⟨Y - k*X, X, ?_⟩
      have : a * (Y - k*X)^2 + 2*c*(Y - k*X)*X + b * X^2
           = b'' * X^2 + 2*c'*X*Y + a * Y^2 := by rw [hb'', hc']; ring
      rw [this]; linarith [hXY]
