import FormalConjectures.Util.ProblemImports

open Nat Finset BigOperators

lemma algebraic_reduction (S1 S2 : ℕ) (p : ℕ) (hp3 : p ≥ 3)
    (h1 : (S1 : ℤ) ≡ 3 [ZMOD (p : ℤ)^3])
    (h2 : (S2 : ℤ) ≡ 3 [ZMOD (p : ℤ)^3])
    (h3 : 3 * (S2 : ℤ) + 4 * (S1 : ℤ) ≡ 21 [ZMOD (p : ℤ)^5]) :
    (S1 : ℤ)^4 * (S2 : ℤ)^3 ≡ 2187 [ZMOD (p : ℤ)^5] := by
  have hd1 : (p : ℤ)^3 ∣ (S1 : ℤ) - 3 := by
    have h1_symm : 3 ≡ (S1 : ℤ) [ZMOD (p : ℤ)^3] := Int.ModEq.symm h1
    exact Int.ModEq.dvd h1_symm
  have hd2 : (p : ℤ)^3 ∣ (S2 : ℤ) - 3 := by
    have h2_symm : 3 ≡ (S2 : ℤ) [ZMOD (p : ℤ)^3] := Int.ModEq.symm h2
    exact Int.ModEq.dvd h2_symm
  rcases hd1 with ⟨a, ha⟩
  rcases hd2 with ⟨b, hb⟩
  have hS1 : (S1 : ℤ) = 3 + a * (p : ℤ)^3 := by
    linear_combination ha
  have hS2 : (S2 : ℤ) = 3 + b * (p : ℤ)^3 := by
    linear_combination hb
  have hd3 : (p : ℤ)^5 ∣ 3 * (S2 : ℤ) + 4 * (S1 : ℤ) - 21 := by
    have h3_symm : 21 ≡ 3 * (S2 : ℤ) + 4 * (S1 : ℤ) [ZMOD (p : ℤ)^5] := Int.ModEq.symm h3
    exact Int.ModEq.dvd h3_symm
  rcases hd3 with ⟨c, hc⟩
  have h_linear : 3 * (S2 : ℤ) + 4 * (S1 : ℤ) - 21 = c * (p : ℤ)^5 := by
    linear_combination hc
  have h_diff_eq : (S1 : ℤ)^4 * (S2 : ℤ)^3 - 2187 = 729 * (3 * (S2 : ℤ) + 4 * (S1 : ℤ) - 21) + (p : ℤ)^5 * ((p : ℤ) * (
    a^4*b^3*(p : ℤ)^15 + 9*a^4*b^2*(p : ℤ)^12 + 27*a^4*b*(p : ℤ)^9 + 27*a^4*(p : ℤ)^6 + 12*a^3*b^3*(p : ℤ)^12 + 108*a^3*b^2*(p : ℤ)^9 +
    324*a^3*b*(p : ℤ)^6 + 324*a^3*(p : ℤ)^3 + 54*a^2*b^3*(p : ℤ)^9 + 486*a^2*b^2*(p : ℤ)^6 + 1458*a^2*b*(p : ℤ)^3 + 1458*a^2 +
    108*a*b^3*(p : ℤ)^6 + 972*a*b^2*(p : ℤ)^3 + 2916*a*b + 81*b^3*(p : ℤ)^3 + 729*b^2
  )) := by
    rw [hS1, hS2]
    ring
  have h_diff_div : (p : ℤ)^5 ∣ (S1 : ℤ)^4 * (S2 : ℤ)^3 - 2187 := by
    rw [h_diff_eq, h_linear]
    use 729 * c + (p : ℤ) * (
      a^4*b^3*(p : ℤ)^15 + 9*a^4*b^2*(p : ℤ)^12 + 27*a^4*b*(p : ℤ)^9 + 27*a^4*(p : ℤ)^6 + 12*a^3*b^3*(p : ℤ)^12 + 108*a^3*b^2*(p : ℤ)^9 +
      324*a^3*b*(p : ℤ)^6 + 324*a^3*(p : ℤ)^3 + 54*a^2*b^3*(p : ℤ)^9 + 486*a^2*b^2*(p : ℤ)^6 + 1458*a^2*b*(p : ℤ)^3 + 1458*a^2 +
      108*a*b^3*(p : ℤ)^6 + 972*a*b^2*(p : ℤ)^3 + 2916*a*b + 81*b^3*(p : ℤ)^3 + 729*b^2
    )
    ring
  have h_goal_symm : 2187 ≡ (S1 : ℤ)^4 * (S2 : ℤ)^3 [ZMOD (p : ℤ)^5] := Int.modEq_of_dvd h_diff_div
  exact Int.ModEq.symm h_goal_symm
