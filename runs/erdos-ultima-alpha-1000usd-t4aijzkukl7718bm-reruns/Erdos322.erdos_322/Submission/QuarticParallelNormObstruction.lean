import FormalConjecturesUtil

/-! A rational obstruction for binary quartic norm identities with repeated directions. -/
namespace Erdos322Research.QuarticParallelNorm

private lemma coefficient_conditions (h a b c C q r : ℚ)
    (H : ∀ x : ℚ, (h*x)^4+h^4+(a*x+b)^4+(c*x)^4 = C*(x^2+q*x+r)^2) :
    C=h^4+a^4+c^4 ∧ C*q=2*a^3*b ∧
      C*(q^2+2*r)=6*a^2*b^2 ∧ C*q*r=2*a*b^3 ∧ C*r^2=h^4+b^4 := by
  have h₀ := H 0
  have h₁ := H 1
  have h₂ := H 2
  have h₃ := H (-1)
  have h₄ := H (-2)
  constructor
  · linear_combination (-h₂-h₄+4*h₁+4*h₃-6*h₀)/24
  constructor
  · linear_combination (-h₂+h₄+2*h₁-2*h₃)/24
  constructor
  · linear_combination (h₂+h₄-16*h₁-16*h₃+30*h₀)/24
  constructor
  · linear_combination (h₂-h₄-8*h₁+8*h₃)/24
  · simpa using h₀.symm

/-- Four rational linear forms cannot give such a norm identity if one is a
nonzero multiple of another and the other two directions are nondegenerate.
The obstruction is Fermat's Last Theorem for exponent four. -/
theorem no_parallel_fourth_form (h a b c C q r : ℚ)
    (hh : h ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    ¬ (∀ x y : ℚ, (h*x)^4+(h*y)^4+(a*x+b*y)^4+(c*x)^4 =
      C*(x^2+q*x*y+r*y^2)^2) := by
  intro H
  have H' (x : ℚ) : (h*x)^4+h^4+(a*x+b)^4+(c*x)^4 = C*(x^2+q*x+r)^2 := by
    simpa using H x 1
  obtain ⟨hC, hq, hr, hqr, hconst⟩ := coefficient_conditions h a b c C q r H'
  have he : a*b^3*C^2-(a^3*b)*(3*(a^2*b^2)*C-2*(a^3*b)^2)=0 := by
    linear_combination (-C^2/2)*hqr + ((a^3*b)*C/2)*hr +
      ((C^2*r-(a^3*b)*(C*q+2*a^3*b))/2)*hq
  rw [hC] at he
  have hf : a*b^3*(h^4+c^4)*(h^4+c^4-a^4)=0 := by
    convert he using 1; ring
  have hsum : h^4+c^4 ≠ 0 := by positivity
  have hn : a*b^3*(h^4+c^4) ≠ 0 :=
    mul_ne_zero (mul_ne_zero ha (pow_ne_zero _ hb)) hsum
  have heq : h^4+c^4=a^4 := sub_eq_zero.mp ((mul_eq_zero.mp hf).resolve_left hn)
  exact (fermatLastTheoremFor_iff_rat.mp fermatLastTheoremFour) h c a hh hc ha heq

/-- The degenerate choices of the third direction cannot rescue the identity. -/
theorem no_parallel_fourth_form_unrestricted (h a b c C q r : ℚ)
    (hh : h ≠ 0) (hc : c ≠ 0) :
    ¬ (∀ x y : ℚ, (h*x)^4+(h*y)^4+(a*x+b*y)^4+(c*x)^4 =
      C*(x^2+q*x*y+r*y^2)^2) := by
  intro H
  have H' (x : ℚ) : (h*x)^4+h^4+(a*x+b)^4+(c*x)^4 = C*(x^2+q*x+r)^2 := by
    simpa using H x 1
  obtain ⟨hC, hq, hr, hqr, hconst⟩ := coefficient_conditions h a b c C q r H'
  have hCp : 0 < C := by rw [hC]; positivity
  have hCn : C ≠ 0 := hCp.ne'
  have hab : a ≠ 0 ∧ b ≠ 0 := by
    by_contra hn
    have hz : a=0 ∨ b=0 := by tauto
    have hq0 : q=0 := by
      rcases hz with hz | hz <;> simpa [hz, hCn] using hq
    have hr0 : r=0 := by
      rcases hz with hz | hz <;> simpa [hz, hq0, hCn] using hr
    rw [hr0] at hconst
    have hp : 0 < h^4 := by positivity
    have hp' : 0 ≤ b^4 := by positivity
    nlinarith
  exact no_parallel_fourth_form h a b c C q r hh hab.1 hab.2 hc H

end Erdos322Research.QuarticParallelNorm
