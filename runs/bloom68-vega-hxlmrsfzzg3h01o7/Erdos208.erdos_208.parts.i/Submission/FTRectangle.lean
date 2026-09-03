import FormalConjecturesUtil

/-!
# Finite four-point rectangle spacing

An elementary rectangle-label estimate for square multiples in a short interval.
The numeric lower bound on `x * b^3` is an input, not a consequence of an
additional Roth theorem. No equal-label hypothesis is used.

Writing `Y = x*b*c³/N⁵`, the ideal rational label lies in `[3Y/32, 4Y]`.
The one-sided hit errors contribute at most `2cH/N² ≤ Y/256`. Thus the
integer label satisfies `0 < F ≤ 5Y`; its integrality gives `1 ≤ F` and the
claimed spacing inequality. The constant in the final theorem is exactly `5`.
-/

namespace FTRectangle

/-- The integer rectangle label; all subtractions take place in `ℤ`. -/
def label (b c m0 m1 m2 m3 : ℤ) : ℤ :=
  (c - b) * m0 - (c + b) * m1 + (c + b) * m2 - (c - b) * m3

/-- The ideal rectangle label, evaluated on the function `z ↦ x / z²`. -/
def ideal (x n b c : ℚ) : ℚ :=
  x * b * c * (c ^ 2 - b ^ 2) *
    (1 / n + 1 / (n + b) + 1 / (n + c) + 1 / (n + b + c)) /
      (n * (n + b) * (n + c) * (n + b + c))

/-- Exact rational identity. In the equivalent common-denominator expression,
the denominator is the square of the product of the four bases. -/
lemma ideal_identity (x n b c : ℚ)
    (h0 : n ≠ 0) (h1 : n + b ≠ 0) (h2 : n + c ≠ 0)
    (h3 : n + b + c ≠ 0) :
    (c - b) * (x / n ^ 2) - (c + b) * (x / (n + b) ^ 2) +
      (c + b) * (x / (n + c) ^ 2) - (c - b) * (x / (n + b + c) ^ 2) =
        ideal x n b c := by
  unfold ideal
  field_simp
  ring

/-- A hit gives a one-sided cofactor error. No positivity hypothesis on the
cofactor itself is required. -/
lemma hit_error_bounds {x H N z m : ℚ} (hH0 : 0 ≤ H) (hN : 0 < N)
    (hz : N ≤ z) (hm : x ≤ m * z ^ 2 ∧ m * z ^ 2 ≤ x + H) :
    0 ≤ m - x / z ^ 2 ∧ m - x / z ^ 2 ≤ H / N ^ 2 := by
  have hz0 : 0 < z := hN.trans_le hz
  have he : m - x / z ^ 2 = (m * z ^ 2 - x) / z ^ 2 := by
    field_simp
  rw [he]
  constructor
  · exact div_nonneg (sub_nonneg.mpr hm.1) (sq_nonneg z)
  · calc
      (m * z ^ 2 - x) / z ^ 2 ≤ H / z ^ 2 :=
        div_le_div_of_nonneg_right (by linarith [hm.2]) (sq_nonneg z)
      _ ≤ H / N ^ 2 := div_le_div_of_nonneg_left hH0 (pow_pos hN 2)
        (pow_le_pow_left₀ hN.le hz 2)

/-- The positive and negative weights both sum to `2*c`, so one-sided
errors cost only `2*c*E`, rather than `4*c*E`. -/
lemma weighted_error_bound {b c E e0 e1 e2 e3 : ℚ}
    (hb : 0 ≤ b) (hbc : b ≤ c)
    (h0 : 0 ≤ e0 ∧ e0 ≤ E) (h1 : 0 ≤ e1 ∧ e1 ≤ E)
    (h2 : 0 ≤ e2 ∧ e2 ≤ E) (h3 : 0 ≤ e3 ∧ e3 ≤ E) :
    |(c - b) * e0 - (c + b) * e1 + (c + b) * e2 - (c - b) * e3| ≤
      2 * c * E := by
  have ha : 0 ≤ c - b := sub_nonneg.mpr hbc
  have hd : 0 ≤ c + b := by linarith
  have h00 := mul_nonneg ha h0.1
  have h01 := mul_le_mul_of_nonneg_left h0.2 ha
  have h10 := mul_nonneg hd h1.1
  have h11 := mul_le_mul_of_nonneg_left h1.2 hd
  have h20 := mul_nonneg hd h2.1
  have h21 := mul_le_mul_of_nonneg_left h2.2 hd
  have h30 := mul_nonneg ha h3.1
  have h31 := mul_le_mul_of_nonneg_left h3.2 ha
  rw [abs_le]
  constructor <;> nlinarith only [h00, h01, h10, h11, h20, h21, h30, h31]

/-- Dyadic estimates for the ideal label, with `Y = x*b*c³/N⁵`. -/
lemma ideal_bounds {x N n b c : ℚ}
    (hx : 0 ≤ x) (hN : 0 < N) (hb : 0 < b) (hbc : 2 * b ≤ c)
    (hn : N ≤ n) (hn' : n + b + c ≤ 2 * N) :
    3 / 32 * (x * b * c ^ 3 / N ^ 5) ≤ ideal x n b c ∧
      ideal x n b c ≤ 4 * (x * b * c ^ 3 / N ^ 5) := by
  have hc : 0 < c := by linarith
  have h0 : 0 < n := hN.trans_le hn
  have h1 : 0 < n + b := by linarith
  have h2 : 0 < n + c := by linarith
  have h3 : 0 < n + b + c := by linarith
  let P := n * (n + b) * (n + c) * (n + b + c)
  let S := 1 / n + 1 / (n + b) + 1 / (n + c) + 1 / (n + b + c)
  let K := x * b * c * (c ^ 2 - b ^ 2)
  have hP : 0 < P := by dsimp [P]; positivity
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hPlo : N ^ 4 ≤ P := by
    calc
      N ^ 4 = N * N * N * N := by ring
      _ ≤ P := by dsimp [P]; gcongr <;> linarith
  have hPhi : P ≤ 16 * N ^ 4 := by
    calc
      P ≤ (2 * N) * (2 * N) * (2 * N) * (2 * N) := by
        dsimp [P]; gcongr <;> linarith
      _ = 16 * N ^ 4 := by ring
  have hSlo : 2 / N ≤ S := by
    have r0 := one_div_le_one_div_of_le h0 (show n ≤ 2 * N by linarith)
    have r1 := one_div_le_one_div_of_le h1 (show n + b ≤ 2 * N by linarith)
    have r2 := one_div_le_one_div_of_le h2 (show n + c ≤ 2 * N by linarith)
    have r3 := one_div_le_one_div_of_le h3 hn'
    have he : 1 / (2 * N) + 1 / (2 * N) + 1 / (2 * N) + 1 / (2 * N) =
        2 / N := by ring
    dsimp [S]
    linarith only [r0, r1, r2, r3, he]
  have hShi : S ≤ 4 / N := by
    have r0 := one_div_le_one_div_of_le hN hn
    have r1 := one_div_le_one_div_of_le hN (show N ≤ n + b by linarith)
    have r2 := one_div_le_one_div_of_le hN (show N ≤ n + c by linarith)
    have r3 := one_div_le_one_div_of_le hN (show N ≤ n + b + c by linarith)
    have he : 1 / N + 1 / N + 1 / N + 1 / N = 4 / N := by ring
    dsimp [S]
    linarith only [r0, r1, r2, r3, he]
  have hRlo : (2 / N) / (16 * N ^ 4) ≤ S / P :=
    div_le_div₀ hS hSlo hP hPhi
  have hRhi : S / P ≤ (4 / N) / N ^ 4 :=
    div_le_div₀ (by positivity) hShi (pow_pos hN 4) hPlo
  have hcb2 : 4 * b ^ 2 ≤ c ^ 2 := by
    have hh := pow_le_pow_left₀ (by positivity : (0 : ℚ) ≤ 2 * b) hbc 2
    nlinarith only [hh]
  have hxbc : 0 ≤ x * b * c := by positivity
  have hKlo : 3 / 4 * (x * b * c ^ 3) ≤ K := by
    calc
      3 / 4 * (x * b * c ^ 3) = (x * b * c) * (3 / 4 * c ^ 2) := by ring
      _ ≤ K := mul_le_mul_of_nonneg_left (by nlinarith only [hcb2]) hxbc
  have hKhi : K ≤ x * b * c ^ 3 := by
    calc
      K ≤ (x * b * c) * c ^ 2 :=
        mul_le_mul_of_nonneg_left (by nlinarith only [sq_nonneg b]) hxbc
      _ = x * b * c ^ 3 := by ring
  have hK : 0 ≤ K := le_trans (by positivity) hKlo
  have hi : ideal x n b c = K * (S / P) := by dsimp [ideal, K, S, P]; ring
  rw [hi]
  constructor
  · calc
      3 / 32 * (x * b * c ^ 3 / N ^ 5) =
          (3 / 4 * (x * b * c ^ 3)) * ((2 / N) / (16 * N ^ 4)) := by
        field_simp
        ring
      _ ≤ K * (S / P) := mul_le_mul hKlo hRlo (by positivity) hK
  · calc
      K * (S / P) ≤ (x * b * c ^ 3) * ((4 / N) / N ^ 4) :=
        mul_le_mul hKhi hRhi (div_nonneg hS hP.le) (by positivity)
      _ = 4 * (x * b * c ^ 3 / N ^ 5) := by field_simp

/-- The supplied cubic lower bound makes the interval error at most `Y/256`. -/
lemma error_le_scale {x H N b c : ℚ}
    (hx : 0 ≤ x) (hN : 0 < N) (hH : 256 * H ≤ N)
    (hb : 0 < b) (hbc : 2 * b ≤ c) (hlarge : N ^ 4 ≤ 2 * x * b ^ 3) :
    2 * c * H / N ^ 2 ≤ (x * b * c ^ 3 / N ^ 5) / 256 := by
  have hc : 0 < c := by linarith
  have hcb2 : 4 * b ^ 2 ≤ c ^ 2 := by
    have hh := pow_le_pow_left₀ (by positivity : (0 : ℚ) ≤ 2 * b) hbc 2
    nlinarith only [hh]
  have hbig : 2 * N ^ 4 ≤ x * b * c ^ 2 := by
    have hh := mul_le_mul_of_nonneg_left hcb2 (mul_nonneg hx hb.le)
    nlinarith only [hh, hlarge]
  have hsmall : 512 * c * H * N ^ 3 ≤ 2 * c * N ^ 4 := by
    have hh := mul_le_mul_of_nonneg_right hH (show 0 ≤ 2 * c * N ^ 3 by positivity)
    nlinarith only [hh]
  have hmain : 512 * c * H * N ^ 3 ≤ x * b * c ^ 3 := by
    have hh := mul_le_mul_of_nonneg_right hbig hc.le
    nlinarith only [hh, hsmall]
  rw [div_div]
  apply (div_le_div_iff₀ (pow_pos hN 2) (by positivity : 0 < N ^ 5 * 256)).mpr
  have hh := mul_le_mul_of_nonneg_right hmain (sq_nonneg N)
  nlinarith only [hh]

/-- The actual rational rectangle expression differs from its ideal value by
at most `2*c*H/N²`. -/
lemma rectangle_error_bound {x H N n b c m0 m1 m2 m3 : ℚ}
    (hH0 : 0 ≤ H) (hN : 0 < N) (hb : 0 ≤ b) (hbc : b ≤ c) (hn : N ≤ n)
    (hm0 : x < m0 * n ^ 2 ∧ m0 * n ^ 2 ≤ x + H)
    (hm1 : x < m1 * (n + b) ^ 2 ∧ m1 * (n + b) ^ 2 ≤ x + H)
    (hm2 : x < m2 * (n + c) ^ 2 ∧ m2 * (n + c) ^ 2 ≤ x + H)
    (hm3 : x < m3 * (n + b + c) ^ 2 ∧ m3 * (n + b + c) ^ 2 ≤ x + H) :
    |((c - b) * m0 - (c + b) * m1 + (c + b) * m2 - (c - b) * m3) -
      ideal x n b c| ≤ 2 * c * H / N ^ 2 := by
  have hc : 0 ≤ c := hb.trans hbc
  have h0 : 0 < n := hN.trans_le hn
  have h1 : 0 < n + b := by linarith
  have h2 : 0 < n + c := by linarith
  have h3 : 0 < n + b + c := by linarith
  have he0 := hit_error_bounds hH0 hN hn ⟨hm0.1.le, hm0.2⟩
  have he1 := hit_error_bounds hH0 hN (show N ≤ n + b by linarith) ⟨hm1.1.le, hm1.2⟩
  have he2 := hit_error_bounds hH0 hN (show N ≤ n + c by linarith) ⟨hm2.1.le, hm2.2⟩
  have he3 := hit_error_bounds hH0 hN (show N ≤ n + b + c by linarith) ⟨hm3.1.le, hm3.2⟩
  have hh := weighted_error_bound hb hbc he0 he1 he2 he3
  have heq : ((c - b) * m0 - (c + b) * m1 + (c + b) * m2 - (c - b) * m3) -
      ideal x n b c =
      (c - b) * (m0 - x / n ^ 2) - (c + b) * (m1 - x / (n + b) ^ 2) +
        (c + b) * (m2 - x / (n + c) ^ 2) -
          (c - b) * (m3 - x / (n + b + c) ^ 2) := by
    rw [← ideal_identity x n b c h0.ne' h1.ne' h2.ne' h3.ne']
    ring
  rw [heq]
  calc
    _ ≤ 2 * c * (H / N ^ 2) := hh
    _ = 2 * c * H / N ^ 2 := by ring

/-- Analytic part of rectangle spacing: `0 < F ≤ 5Y`, without any integrality
hypothesis. The lower bound on `x*b³` is explicitly supplied as input. -/
lemma rational_label_bounds {x H N n b c m0 m1 m2 m3 : ℚ}
    (hx : 0 ≤ x) (hH0 : 0 ≤ H) (hN : 0 < N) (hH : 256 * H ≤ N)
    (hb : 0 < b) (hbc : 2 * b ≤ c) (hn : N ≤ n) (hn' : n + b + c ≤ 2 * N)
    (hm0 : x < m0 * n ^ 2 ∧ m0 * n ^ 2 ≤ x + H)
    (hm1 : x < m1 * (n + b) ^ 2 ∧ m1 * (n + b) ^ 2 ≤ x + H)
    (hm2 : x < m2 * (n + c) ^ 2 ∧ m2 * (n + c) ^ 2 ≤ x + H)
    (hm3 : x < m3 * (n + b + c) ^ 2 ∧ m3 * (n + b + c) ^ 2 ≤ x + H)
    (hlarge : N ^ 4 ≤ 2 * x * b ^ 3) :
    0 < (c - b) * m0 - (c + b) * m1 + (c + b) * m2 - (c - b) * m3 ∧
      (c - b) * m0 - (c + b) * m1 + (c + b) * m2 - (c - b) * m3 ≤
        5 * (x * b * c ^ 3 / N ^ 5) := by
  let Y := x * b * c ^ 3 / N ^ 5
  let F := (c - b) * m0 - (c + b) * m1 + (c + b) * m2 - (c - b) * m3
  change 0 < F ∧ F ≤ 5 * Y
  have hc : 0 < c := by linarith
  have hxpos : 0 < x := by
    by_contra hnot
    have hxzero : x = 0 := le_antisymm (le_of_not_gt hnot) hx
    rw [hxzero] at hlarge
    nlinarith only [hlarge, pow_pos hN 4]
  have hY : 0 < Y := by dsimp [Y]; positivity
  have hi : 3 / 32 * Y ≤ ideal x n b c ∧ ideal x n b c ≤ 4 * Y :=
    ideal_bounds hx hN hb hbc hn hn'
  have he : |F - ideal x n b c| ≤ 2 * c * H / N ^ 2 :=
    rectangle_error_bound hH0 hN hb.le (by linarith) hn hm0 hm1 hm2 hm3
  have hs : 2 * c * H / N ^ 2 ≤ Y / 256 := error_le_scale hx hN hH hb hbc hlarge
  rcases abs_le.mp he with ⟨helo, hehi⟩
  constructor <;> linarith only [hi.1, hi.2, helo, hehi, hs, hY]

/-- Integer rectangle-label positivity and its rational upper bound. The
cofactors may be arbitrary integers; their hits provide all needed signs. -/
theorem label_bounds_int {x H N n b c m0 m1 m2 m3 : ℤ}
    (hx : 0 ≤ x) (hH0 : 0 ≤ H) (hN : 0 < N) (hH : 256 * H ≤ N)
    (hb : 0 < b) (hbc : 2 * b ≤ c) (hn : N ≤ n) (hn' : n + b + c ≤ 2 * N)
    (hm0 : x < m0 * n ^ 2 ∧ m0 * n ^ 2 ≤ x + H)
    (hm1 : x < m1 * (n + b) ^ 2 ∧ m1 * (n + b) ^ 2 ≤ x + H)
    (hm2 : x < m2 * (n + c) ^ 2 ∧ m2 * (n + c) ^ 2 ≤ x + H)
    (hm3 : x < m3 * (n + b + c) ^ 2 ∧ m3 * (n + b + c) ^ 2 ≤ x + H)
    (hlarge : N ^ 4 ≤ 2 * x * b ^ 3) :
    0 < label b c m0 m1 m2 m3 ∧
      (label b c m0 m1 m2 m3 : ℚ) ≤
        5 * ((x : ℚ) * b * (c : ℚ) ^ 3 / (N : ℚ) ^ 5) := by
  have hh := rational_label_bounds
    (x := (x : ℚ)) (H := (H : ℚ)) (N := (N : ℚ)) (n := (n : ℚ))
    (b := (b : ℚ)) (c := (c : ℚ))
    (m0 := (m0 : ℚ)) (m1 := (m1 : ℚ)) (m2 := (m2 : ℚ)) (m3 := (m3 : ℚ))
    (by exact_mod_cast hx) (by exact_mod_cast hH0) (by exact_mod_cast hN)
    (by exact_mod_cast hH) (by exact_mod_cast hb) (by exact_mod_cast hbc)
    (by exact_mod_cast hn) (by exact_mod_cast hn')
    (by exact_mod_cast hm0) (by exact_mod_cast hm1)
    (by exact_mod_cast hm2) (by exact_mod_cast hm3) (by exact_mod_cast hlarge)
  have hpos : (0 : ℚ) < (label b c m0 m1 m2 m3 : ℚ) := by
    simpa only [label, Int.cast_sub, Int.cast_mul, Int.cast_add] using hh.1
  refine ⟨by exact_mod_cast hpos, ?_⟩
  simpa only [label, Int.cast_sub, Int.cast_mul, Int.cast_add] using hh.2

/-- Finite four-point spacing for integer data. The integer label is positive,
thus at least one, and its upper bound gives the conclusion with constant `5`. -/
theorem four_point_spacing_int {x H N n b c m0 m1 m2 m3 : ℤ}
    (hx : 0 ≤ x) (hH0 : 0 ≤ H) (hN : 0 < N) (hH : 256 * H ≤ N)
    (hb : 0 < b) (hbc : 2 * b ≤ c) (hn : N ≤ n) (hn' : n + b + c ≤ 2 * N)
    (hm0 : x < m0 * n ^ 2 ∧ m0 * n ^ 2 ≤ x + H)
    (hm1 : x < m1 * (n + b) ^ 2 ∧ m1 * (n + b) ^ 2 ≤ x + H)
    (hm2 : x < m2 * (n + c) ^ 2 ∧ m2 * (n + c) ^ 2 ≤ x + H)
    (hm3 : x < m3 * (n + b + c) ^ 2 ∧ m3 * (n + b + c) ^ 2 ≤ x + H)
    (hlarge : N ^ 4 ≤ 2 * x * b ^ 3) :
    N ^ 5 ≤ 5 * x * b * c ^ 3 := by
  obtain ⟨hpos, hupper⟩ :=
    label_bounds_int hx hH0 hN hH hb hbc hn hn' hm0 hm1 hm2 hm3 hlarge
  have hone : (1 : ℤ) ≤ label b c m0 m1 m2 m3 := by omega
  have honeQ : (1 : ℚ) ≤ (label b c m0 m1 m2 m3 : ℚ) := by exact_mod_cast hone
  have hY := honeQ.trans hupper
  have hNQ : (0 : ℚ) < N := by exact_mod_cast hN
  have hscaled : (N : ℚ) ^ 5 ≤ 5 * (x : ℚ) * b * (c : ℚ) ^ 3 := by
    have he : 5 * ((x : ℚ) * b * (c : ℚ) ^ 3 / (N : ℚ) ^ 5) =
        (5 * (x : ℚ) * b * (c : ℚ) ^ 3) / (N : ℚ) ^ 5 := by ring
    rw [he] at hY
    have hh := (le_div_iff₀ (pow_pos hNQ 5)).mp hY
    simpa only [one_mul] using hh
  exact_mod_cast hscaled

/-- **Finite Roth/FT four-point rectangle spacing.** If all four square
multiples with bases `n`, `n+b`, `n+c`, `n+b+c` lie in `(x,x+H]`, the bases
lie in `[N,2N]`, `c ≥ 2b > 0`, and the numeric lower bound
`N⁴ ≤ 2*x*b³` is supplied, then `N⁵ ≤ 5*x*b*c³`.

This theorem has no equal-label hypothesis and no dependency on `RothQuant`.
It makes no all-positive-exponents squarefree-gap assertion. -/
theorem four_point_spacing {x H N n b c m0 m1 m2 m3 : ℕ}
    (hN : 0 < N) (hH : 256 * H ≤ N)
    (hb : 0 < b) (hbc : 2 * b ≤ c) (hn : N ≤ n) (hn' : n + b + c ≤ 2 * N)
    (hm0 : x < m0 * n ^ 2 ∧ m0 * n ^ 2 ≤ x + H)
    (hm1 : x < m1 * (n + b) ^ 2 ∧ m1 * (n + b) ^ 2 ≤ x + H)
    (hm2 : x < m2 * (n + c) ^ 2 ∧ m2 * (n + c) ^ 2 ≤ x + H)
    (hm3 : x < m3 * (n + b + c) ^ 2 ∧ m3 * (n + b + c) ^ 2 ≤ x + H)
    (hlarge : N ^ 4 ≤ 2 * x * b ^ 3) :
    N ^ 5 ≤ 5 * x * b * c ^ 3 := by
  have hh := four_point_spacing_int
    (x := (x : ℤ)) (H := (H : ℤ)) (N := (N : ℤ)) (n := (n : ℤ))
    (b := (b : ℤ)) (c := (c : ℤ))
    (m0 := (m0 : ℤ)) (m1 := (m1 : ℤ)) (m2 := (m2 : ℤ)) (m3 := (m3 : ℤ))
    (Nat.cast_nonneg x) (Nat.cast_nonneg H) (by exact_mod_cast hN)
    (by exact_mod_cast hH) (by exact_mod_cast hb) (by exact_mod_cast hbc)
    (by exact_mod_cast hn) (by exact_mod_cast hn')
    (by exact_mod_cast hm0) (by exact_mod_cast hm1)
    (by exact_mod_cast hm2) (by exact_mod_cast hm3) (by exact_mod_cast hlarge)
  exact_mod_cast hh

end FTRectangle
