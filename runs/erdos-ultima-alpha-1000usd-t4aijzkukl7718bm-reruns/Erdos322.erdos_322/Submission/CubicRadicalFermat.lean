import FormalConjecturesUtil

/-!
Rationality of normalized cubic radicals and a Fermat obstruction.
These lemmas do not assert an upper bound for representation counts.
-/
namespace Erdos322Research.CubicRadicalFermat

/-- Two real cubic radicals whose sum is one are rational. -/
theorem rational_of_sum_one_and_rational_cubes (x y : ℝ) (a b : ℚ)
    (hx : x^3=(a : ℝ)) (hy : y^3=(b : ℝ)) (hxy : x+y=1) :
    ∃ r : ℚ, x=(r : ℝ) := by
  have hy' : y=1-x := by linarith
  have hd : 0 < 2+(a : ℝ)+(b : ℝ) := by
    calc
      2+(a : ℝ)+(b : ℝ) = 3*(x-1/2)^2+9/4 := by
        rw [← hx, ← hy, hy']
        ring
      _ > 0 := by positivity
  refine ⟨(1+2*a-b)/(2+a+b), ?_⟩
  push_cast
  apply (eq_div_iff hd.ne').mpr
  rw [← hx, ← hy, hy']
  ring

/-- On the real fourth-power unit curve, rational cubes already force
rational coordinates. -/
theorem rational_of_fourth_sum_one_and_rational_cubes (x y : ℝ) (a b : ℚ)
    (hx : x^3=(a : ℝ)) (hy : y^3=(b : ℝ))
    (hxy : x^4+y^4=1) (hx0 : x ≠ 0) : ∃ r : ℚ, x=(r : ℝ) := by
  have hx' : (x^4)^3=((a^4 : ℚ) : ℝ) := by
    calc
      (x^4)^3 = (x^3)^4 := by ring
      _ = ((a^4 : ℚ) : ℝ) := by rw [hx]; push_cast; rfl
  have hy' : (y^4)^3=((b^4 : ℚ) : ℝ) := by
    calc
      (y^4)^3 = (y^3)^4 := by ring
      _ = ((b^4 : ℚ) : ℝ) := by rw [hy]; push_cast; rfl
  obtain ⟨r, hr⟩ := rational_of_sum_one_and_rational_cubes (x^4) (y^4)
    (a^4) (b^4) hx' hy' hxy
  refine ⟨r/a, ?_⟩
  push_cast
  have ha0 : (a : ℝ) ≠ 0 := by rw [← hx]; exact pow_ne_zero 3 hx0
  apply (eq_div_iff ha0).mpr
  rw [← hx, ← hr]
  ring

/-- Fermat's fourth-power obstruction extends to real triples whose cubes
are rational. In particular, allowing independent real cubic radicals does
not produce new nonzero fourth-power Fermat solutions. -/
theorem no_fourth_fermat_with_rational_cubes (x y z : ℝ) (a b c : ℚ)
    (hx : x^3=(a : ℝ)) (hy : y^3=(b : ℝ)) (hz : z^3=(c : ℝ))
    (hx0 : x ≠ 0) (hy0 : y ≠ 0) (hz0 : z ≠ 0) :
    x^4+y^4 ≠ z^4 := by
  intro hxyz
  have hnorm : (x/z)^4+(y/z)^4=1 := by
    rw [div_pow, div_pow, ← add_div, hxyz, div_self (pow_ne_zero 4 hz0)]
  have hxc : (x/z)^3=((a/c : ℚ) : ℝ) := by rw [div_pow, hx, hz]; push_cast; rfl
  have hyc : (y/z)^3=((b/c : ℚ) : ℝ) := by rw [div_pow, hy, hz]; push_cast; rfl
  obtain ⟨r, hr⟩ := rational_of_fourth_sum_one_and_rational_cubes
    (x/z) (y/z) (a/c) (b/c) hxc hyc hnorm (div_ne_zero hx0 hz0)
  obtain ⟨s, hs⟩ := rational_of_fourth_sum_one_and_rational_cubes
    (y/z) (x/z) (b/c) (a/c) hyc hxc (by simpa [add_comm] using hnorm)
    (div_ne_zero hy0 hz0)
  have hr0 : r ≠ 0 := by
    intro he
    have hn := div_ne_zero hx0 hz0
    apply hn
    simpa [he] using hr
  have hs0 : s ≠ 0 := by
    intro he
    have hn := div_ne_zero hy0 hz0
    apply hn
    simpa [he] using hs
  have he : r^4+s^4=(1 : ℚ)^4 := by
    rw [hr, hs] at hnorm
    exact_mod_cast hnorm
  exact (fermatLastTheoremFor_iff_rat.mp fermatLastTheoremFour)
    r s 1 hr0 hs0 (by norm_num) he

end Erdos322Research.CubicRadicalFermat
