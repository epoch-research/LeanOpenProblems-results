import FormalConjectures.Util.ProblemImports

open Nat Finset BigOperators

/-- Algebraic reduction. -/
lemma reduction (p A B : ℤ) (h1 : p ^ 3 ∣ A) (h2 : p ^ 3 ∣ B)
    (h3 : p ^ 5 ∣ 4 * A + 3 * B) :
    p ^ 5 ∣ (3 + A) ^ 4 * (3 + B) ^ 3 - 3 ^ 7 := by
  obtain ⟨a, ha⟩ := h1
  obtain ⟨b, hb⟩ := h2
  obtain ⟨c, hc⟩ := h3
  subst ha hb
  have key : (3 + p ^ 3 * a) ^ 4 * (3 + p ^ 3 * b) ^ 3 - 3 ^ 7
      = 729 * (4 * (p ^ 3 * a) + 3 * (p ^ 3 * b)) + p ^ 6 *
        (a^4*b^3*p^15 + 9*a^4*b^2*p^12 + 27*a^4*b*p^9 + 27*a^4*p^6
         + 12*a^3*b^3*p^12 + 108*a^3*b^2*p^9 + 324*a^3*b*p^6 + 324*a^3*p^3
         + 54*a^2*b^3*p^9 + 486*a^2*b^2*p^6 + 1458*a^2*b*p^3 + 1458*a^2
         + 108*a*b^3*p^6 + 972*a*b^2*p^3 + 2916*a*b + 81*b^3*p^3 + 729*b^2) := by
    ring
  rw [key]
  apply dvd_add
  · rw [hc]; exact ⟨729 * c, by ring⟩
  · exact ⟨p * (a^4*b^3*p^15 + 9*a^4*b^2*p^12 + 27*a^4*b*p^9 + 27*a^4*p^6
         + 12*a^3*b^3*p^12 + 108*a^3*b^2*p^9 + 324*a^3*b*p^6 + 324*a^3*p^3
         + 54*a^2*b^3*p^9 + 486*a^2*b^2*p^6 + 1458*a^2*b*p^3 + 1458*a^2
         + 108*a*b^3*p^6 + 972*a*b^2*p^3 + 2916*a*b + 81*b^3*p^3 + 729*b^2), by ring⟩
