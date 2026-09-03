import Submission.RationalKernelForms

/-! An exact positive kernel on the physical index domain n>=2.
Its fixed integral form is 4*alpha-5; no vanishing family is supplied. -/
namespace PhysicalPositiveKernelExample

open Polynomial RationalKernelForms Erdos68Development

set_option maxHeartbeats 2000000

noncomputable def lower : Polynomial ℚ :=
  4 * (
    C (-7367 / 840000000) * X^10 +
    C (296087 / 1050000000) * X^9 +
    C (-186459 / 50000000) * X^8 +
    C (6994311 / 280000000) * X^7 +
    C (-46455463 / 600000000) * X^6 +
    C (-67097167 / 4200000000) * X^5 +
    C (184968033 / 200000000) * X^4 +
    C (-4074224743 / 1400000000) * X^3 +
    C (2583200771 / 700000000) * X^2 +
    C (-9479137 / 7000000) * X +
    C (-40059833 / 600000000))

noncomputable def upper : Polynomial ℚ :=
  4 * (
    C (7367 / 840000000) * X^9 +
    C (-629009 / 2100000000) * X^8 +
    C (8905121 / 2100000000) * X^7 +
    C (-131202077 / 4200000000) * X^6 +
    C (163923397 / 1400000000) * X^5 +
    C (-109075229 / 1050000000) * X^4 +
    C (-978644647 / 1050000000) * X^3 +
    C (623920381 / 150000000) * X^2 +
    C (-31034832761 / 4200000000) * X +
    C (3128244593 / 600000000))

noncomputable def family (j : ℕ) : Polynomial ℚ :=
  if j = 0 then lower else upper

noncomputable def p0 (_x : ℝ) : ℝ := 1

noncomputable def p1 (x : ℝ) : ℝ := 1 * x + -1

noncomputable def p2 (x : ℝ) : ℝ := 1 * x^2 + -3 * x + 1

noncomputable def p3 (x : ℝ) : ℝ := 1 * x^3 + -6 * x^2 + 8 * x + -1

noncomputable def p4 (x : ℝ) : ℝ := 1 * x^4 + -10 * x^3 + 29 * x^2 + -24 * x + 1

noncomputable def p5 (x : ℝ) : ℝ := 1 * x^5 + -15 * x^4 + 75 * x^3 + -145 * x^2 + 89 * x + -1

noncomputable def g0 (x t : ℝ) : ℝ :=
  1 * (1) +
    (-1154009 / 5000000) * ((1-t) * p0 x) +
    (-7625007 / 5000000) * ((1-t) * p1 x) +
    (457753 / 500000) * ((1-t) * p2 x) +
    (-370569 / 1250000) * ((1-t) * p3 x) +
    (600369 / 10000000) * ((1-t) * p4 x) +
    (-1139 / 156250) * ((1-t) * p5 x)

noncomputable def g1 (x t : ℝ) : ℝ :=
  1 * ((1-t) * p0 x) +
    (-119135824203063 / 142930453227919) * ((1-t) * p1 x) +
    (47668375817770 / 142930453227919) * ((1-t) * p2 x) +
    (-11926267344484 / 142930453227919) * ((1-t) * p3 x) +
    (569275889903 / 40837272350834) * ((1-t) * p4 x) +
    (-200736320032 / 142930453227919) * ((1-t) * p5 x)

noncomputable def g2 (x t : ℝ) : ℝ :=
  1 * ((1-t) * p1 x) +
    (-254430162993376877 / 485837057162817089) * ((1-t) * p2 x) +
    (76276347202642456 / 485837057162817089) * ((1-t) * p3 x) +
    (-26598031097921087 / 971674114325634178) * ((1-t) * p4 x) +
    (880423693734986 / 485837057162817089) * ((1-t) * p5 x)

noncomputable def g3 (x t : ℝ) : ℝ :=
  1 * ((1-t) * p2 x) +
    (-32364634125115009457 / 87636084810286600850) * ((1-t) * p3 x) +
    (5436215171566485639 / 35054433924114640340) * ((1-t) * p4 x) +
    (-3994924518105953093 / 87636084810286600850) * ((1-t) * p5 x)

noncomputable def g4 (x t : ℝ) : ℝ :=
  1 * ((1-t) * p3 x) +
    (-907654416424421871515 / 6772722462925567587118) * ((1-t) * p4 x) +
    (152316658624646403091 / 3386361231462783793559) * ((1-t) * p5 x)

noncomputable def g5 (x t : ℝ) : ℝ :=
  1 * ((1-t) * p4 x) +
    (30654081703457364247493 / 3444661630049815060676742) * ((1-t) * p5 x)

noncomputable def g6 (x t : ℝ) : ℝ :=
  1 * ((1-t) * p5 x)

noncomputable def gramG (x t : ℝ) : ℝ :=
  1 * (g0 x t)^2 +
    (142930453227919 / 25000000000000) * (g1 x t)^2 +
    (485837057162817089 / 1429304532279190000000) * (g2 x t)^2 +
    (1752721696205732017 / 97167411432563417800000) * (g3 x t)^2 +
    (3386361231462783793559 / 876360848102866008500000000) * (g4 x t)^2 +
    (82015753096424168111351 / 135454449258511351742360000000) * (g5 x t)^2 +
    (222415573129988176524515809 / 5787031538483689301936926560000000) * (g6 x t)^2

noncomputable def h0 (x t : ℝ) : ℝ :=
  1 * ((1-t) * p0 x) +
    (-6667571 / 7961397) * ((1-t) * p1 x) +
    (13404334 / 39806985) * ((1-t) * p2 x) +
    (-224703 / 2653799) * ((1-t) * p3 x) +
    (188717 / 13268995) * ((1-t) * p4 x) +
    (-57439 / 39806985) * ((1-t) * p5 x)

noncomputable def h1 (x t : ℝ) : ℝ :=
  1 * ((1-t) * p1 x) +
    (-99266261 / 923289191) * ((1-t) * p2 x) +
    (340230090 / 923289191) * ((1-t) * p3 x) +
    (-187703475 / 1846578382) * ((1-t) * p4 x) +
    (18118802 / 923289191) * ((1-t) * p5 x)

noncomputable def h2 (x t : ℝ) : ℝ :=
  1 * ((1-t) * p2 x) +
    (44502927620 / 904127035667) * ((1-t) * p3 x) +
    (104420883308 / 904127035667) * ((1-t) * p4 x) +
    (-27198035202 / 904127035667) * ((1-t) * p5 x)

noncomputable def h3 (x t : ℝ) : ℝ :=
  1 * ((1-t) * p3 x) +
    (436423617055 / 1149151441504) * ((1-t) * p4 x) +
    (160197216583 / 3734742184888) * ((1-t) * p5 x)

noncomputable def h4 (x t : ℝ) : ℝ :=
  1 * ((1-t) * p4 x) +
    (686941161121616 / 1063463434510155) * ((1-t) * p5 x)

noncomputable def h5 (x t : ℝ) : ℝ :=
  1 * ((1-t) * p5 x)

noncomputable def gramH (x t : ℝ) : ℝ :=
  (7961397 / 2000000) * (h0 x t)^2 +
    (923289191 / 39806985000000) * (h1 x t)^2 +
    (904127035667 / 46164459550000000) * (h2 x t)^2 +
    (1400528319333 / 282539698645937500) * (h3 x t)^2 +
    (10128223185811 / 11491514415040000000) * (h4 x t)^2 +
    (4565370706662205247 / 58065103524254463000000000) * (h5 x t)^2

lemma boundary_eq_five : boundary family 2 = 5 := by
  norm_num [boundary, Finset.sum_range_succ, family, lower, upper]

/-- The rational LDL certificate is checked as an exact polynomial identity. -/
theorem kernel_identity (n : ℕ) (t : ℝ) :
    kernel 4 family 2 n t = 4 * (gramG (n+2) t + (n : ℝ) * gramH (n+2) t) := by
  norm_num [kernel, rowCoeff, Finset.sum_range_succ, family, lower, upper,
    gramG, gramH, g0, g1, g2, g3, g4, g5, g6, h0, h1, h2, h3, h4, h5,
    p0, p1, p2, p3, p4, p5]
  ring

lemma gramG_nonneg (x t : ℝ) : 0 ≤ gramG x t := by
  unfold gramG
  positivity

lemma gramH_nonneg (x t : ℝ) : 0 ≤ gramH x t := by
  unfold gramH
  positivity

/-- Positivity holds for every real t, on all physical row indices. -/
theorem kernel_nonneg (n : ℕ) (t : ℝ) : 0 ≤ kernel 4 family 2 n t := by
  rw [kernel_identity]
  exact mul_nonneg (by norm_num) (add_nonneg (gramG_nonneg _ _)
    (mul_nonneg (Nat.cast_nonneg n) (gramH_nonneg _ _)))

lemma first_row_positive_small : 0 < kernel 4 family 2 0 (1/2) ∧
    kernel 4 family 2 0 (1/2) < 1 := by
  norm_num [kernel, rowCoeff, Finset.sum_range_succ, family, lower, upper]

/-- Integral boundary and a nonnegative quadratic-t kernel coexist without
an A*t^J baseline. -/
theorem positive_rows_integral_boundary : boundary family 2 = 5 ∧
    (∀ n : ℕ, 0 ≤ kernel 4 family 2 n (1 / ((n+2).factorial : ℝ))) ∧
    0 < kernel 4 family 2 0 (1/2) :=
  ⟨boundary_eq_five, fun n => kernel_nonneg n _, first_row_positive_small.1⟩

theorem sum_kernel :
    (∑' n : ℕ, kernel 4 family 2 n (1 / ((n+2).factorial : ℝ)) /
      (((n+2).factorial : ℝ)-1)) = 4 * (∑' n : ℕ, term n) - 5 := by
  simpa only [boundary_eq_five, Rat.cast_ofNat] using (hasSum_kernel 4 family 2).tsum_eq

/-- This is a single small form, not a sequence proving irrationality. -/
theorem fixed_form_small : 0 < 4 * (∑' n : ℕ, term n) - 5 ∧
    4 * (∑' n : ℕ, term n) - 5 < 1 := by
  constructor
  · have hs := hasSum_kernel 4 family 2
    have hn (n : ℕ) : 0 ≤ kernel 4 family 2 n (1 / ((n+2).factorial : ℝ)) /
        (((n+2).factorial : ℝ)-1) :=
      div_nonneg (kernel_nonneg n _) (denom_pos n).le
    have h := hs.summable.le_tsum 0 (fun n _ => hn n)
    rw [hs.tsum_eq, boundary_eq_five] at h
    norm_num only [Nat.zero_add, Nat.factorial, Nat.cast_ofNat, Nat.cast_one,
      Nat.cast_mul, Rat.cast_ofNat] at h
    have hp := first_row_positive_small.1
    linarith
  · have hu := sum_bounds.2
    linarith

/-- The earlier nonnegative residual ansatz with J=2 cannot describe this
kernel: its forced first-row baseline would already be one. -/
theorem no_column_baseline : ¬ ∃ R : ℕ → ℝ, (∀ n, 0 ≤ R n) ∧
    ∀ n, kernel 4 family 2 n (1 / ((n+2).factorial : ℝ)) =
      4 * (1 / ((n+2).factorial : ℝ))^2 +
        (1 - 1 / ((n+2).factorial : ℝ)) * R n := by
  rintro ⟨R, hR, h⟩
  have he := h 0
  norm_num at he
  have hr := hR 0
  have hk := first_row_positive_small.2
  linarith

end PhysicalPositiveKernelExample

#print axioms PhysicalPositiveKernelExample.kernel_identity
#print axioms PhysicalPositiveKernelExample.positive_rows_integral_boundary
#print axioms PhysicalPositiveKernelExample.sum_kernel
#print axioms PhysicalPositiveKernelExample.fixed_form_small
#print axioms PhysicalPositiveKernelExample.no_column_baseline
