import FormalConjectures.Util.ProblemImports

open Nat Finset BigOperators

namespace A357674dev

/-- Pure algebra reduction: if S1 ≡ 3, S2 ≡ 3 mod p^3 and 4 S1 + 3 S2 ≡ 21 mod p^5,
then S1^4 * S2^3 ≡ 2187 mod p^5, over ℤ. -/
theorem reduction (p s1 s2 : ℤ) (hp : p ≠ 0)
    (h1 : p ^ 3 ∣ (s1 - 3)) (h2 : p ^ 3 ∣ (s2 - 3))
    (h3 : p ^ 5 ∣ (4 * s1 + 3 * s2 - 21)) :
    p ^ 5 ∣ (s1 ^ 4 * s2 ^ 3 - 2187) := by
  obtain ⟨X, hX⟩ := h1
  obtain ⟨Y, hY⟩ := h2
  -- s1 = 3 + p^3 X, s2 = 3 + p^3 Y
  have hs1 : s1 = 3 + p ^ 3 * X := by linarith [hX]
  have hs2 : s2 = 3 + p ^ 3 * Y := by linarith [hY]
  -- 4 s1 + 3 s2 - 21 = p^3 (4X + 3Y)
  have hlin : 4 * s1 + 3 * s2 - 21 = p ^ 3 * (4 * X + 3 * Y) := by
    rw [hs1, hs2]; ring
  -- from h3 get p^2 ∣ (4X+3Y)
  rw [hlin] at h3
  obtain ⟨m, hm⟩ := h3
  have hcancel : 4 * X + 3 * Y = p ^ 2 * m := by
    have : p ^ 3 * (4 * X + 3 * Y) = p ^ 3 * (p ^ 2 * m) := by
      rw [hm]; ring
    exact mul_left_cancel₀ (pow_ne_zero 3 hp) this
  -- Now expand the difference
  rw [hs1, hs2]
  refine ⟨729 * m + p * (X^4*Y^3*p^15 + 9*X^4*Y^2*p^12 + 27*X^4*Y*p^9 + 27*X^4*p^6
      + 12*X^3*Y^3*p^12 + 108*X^3*Y^2*p^9 + 324*X^3*Y*p^6 + 324*X^3*p^3
      + 54*X^2*Y^3*p^9 + 486*X^2*Y^2*p^6 + 1458*X^2*Y*p^3 + 1458*X^2
      + 108*X*Y^3*p^6 + 972*X*Y^2*p^3 + 2916*X*Y + 81*Y^3*p^3 + 729*Y^2), ?_⟩
  linear_combination (729 * p^3) * hcancel

end A357674dev
