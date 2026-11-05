import FormalConjecturesUtil

/-!
# Global product identities for positive sums of two cubes

These proved auxiliary statements do not import the conjecture declarations.
The three-product detects the diagonal by divisibility by the common cube sum.
The pair resultant and determinant bounds justify weighted prime-allocation
separation. No uniform polylogarithmic bound is asserted in this file.
-/

namespace Erdos829Aux.GlobalProducts

open scoped BigOperators

/-- The cross determinant and its quadratic companion give an exact resultant. -/
theorem cross_resultant {R : Type*} [CommRing R] {n a b c d : R}
    (hab : a ^ 3 + b ^ 3 = n) (hcd : c ^ 3 + d ^ 3 = n) :
    (a * d - c * b) * ((a * d) ^ 2 + (a * d) * (c * b) + (c * b) ^ 2) =
      n * (d ^ 3 - b ^ 3) := by
  calc
    _ = (a ^ 3 + b ^ 3) * d ^ 3 - (c ^ 3 + d ^ 3) * b ^ 3 := by ring
    _ = _ := by rw [hab, hcd]; ring

/-- A three-representation product has a sum-of-squares deficit. -/
theorem triple_deficit {n a b c d e f : ℝ}
    (hab : a ^ 3 + b ^ 3 = n) (hcd : c ^ 3 + d ^ 3 = n)
    (hef : e ^ 3 + f ^ 3 = n) :
    6 * (n - (a * c * e + b * d * f)) =
      (a + c + e) * ((a - c) ^ 2 + (c - e) ^ 2 + (e - a) ^ 2) +
      (b + d + f) * ((b - d) ^ 2 + (d - f) ^ 2 + (f - b) ^ 2) := by
  linear_combination -2 * hab - 2 * hcd - 2 * hef

/-- For nonnegative coordinates, the three-representation product is at most n. -/
theorem triple_product_le {n a b c d e f : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (he : 0 ≤ e) (hf : 0 ≤ f)
    (hab : a ^ 3 + b ^ 3 = n) (hcd : c ^ 3 + d ^ 3 = n)
    (hef : e ^ 3 + f ^ 3 = n) :
    a * c * e + b * d * f ≤ n := by
  have h := triple_deficit hab hcd hef
  have hx : 0 ≤ (a + c + e) *
      ((a - c) ^ 2 + (c - e) ^ 2 + (e - a) ^ 2) := by positivity
  have hy : 0 ≤ (b + d + f) *
      ((b - d) ^ 2 + (d - f) ^ 2 + (f - b) ^ 2) := by positivity
  linarith

private theorem eq_of_three_squares_zero {a b c : ℝ}
    (h : (a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2 = 0) :
    a = b ∧ b = c := by
  have hab : (a - b) ^ 2 = 0 := by
    nlinarith [sq_nonneg (b - c), sq_nonneg (c - a)]
  have hbc : (b - c) ^ 2 = 0 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (c - a)]
  exact ⟨sub_eq_zero.mp (sq_eq_zero_iff.mp hab),
    sub_eq_zero.mp (sq_eq_zero_iff.mp hbc)⟩

/-- With positive coordinates the deficit vanishes only on the diagonal. -/
theorem triple_product_eq_iff {n a b c d e f : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (he : 0 < e) (hf : 0 < f)
    (hab : a ^ 3 + b ^ 3 = n) (hcd : c ^ 3 + d ^ 3 = n)
    (hef : e ^ 3 + f ^ 3 = n) :
    a * c * e + b * d * f = n ↔ a = c ∧ c = e ∧ b = d ∧ d = f := by
  constructor
  · intro heq
    have hid := triple_deficit hab hcd hef
    rw [heq] at hid
    have hx : 0 ≤ (a + c + e) *
        ((a - c) ^ 2 + (c - e) ^ 2 + (e - a) ^ 2) := by positivity
    have hy : 0 ≤ (b + d + f) *
        ((b - d) ^ 2 + (d - f) ^ 2 + (f - b) ^ 2) := by positivity
    have hxz : (a + c + e) *
        ((a - c) ^ 2 + (c - e) ^ 2 + (e - a) ^ 2) = 0 := by linarith
    have hyz : (b + d + f) *
        ((b - d) ^ 2 + (d - f) ^ 2 + (f - b) ^ 2) = 0 := by linarith
    have hxsum : 0 < a + c + e := by linarith
    have hysum : 0 < b + d + f := by linarith
    have hx0 := (mul_eq_zero.mp hxz).resolve_left (ne_of_gt hxsum)
    have hy0 := (mul_eq_zero.mp hyz).resolve_left (ne_of_gt hysum)
    have hxeq := eq_of_three_squares_zero hx0
    have hyeq := eq_of_three_squares_zero hy0
    exact ⟨hxeq.1, hxeq.2, hyeq.1, hyeq.2⟩
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    convert hef using 1
    ring

/-- The natural-number version of the three-product upper bound. -/
theorem triple_product_le_nat {n a b c d e f : ℕ}
    (hab : a ^ 3 + b ^ 3 = n) (hcd : c ^ 3 + d ^ 3 = n)
    (hef : e ^ 3 + f ^ 3 = n) : a * c * e + b * d * f ≤ n := by
  have habR : (a : ℝ) ^ 3 + (b : ℝ) ^ 3 = (n : ℝ) := by exact_mod_cast hab
  have hcdR : (c : ℝ) ^ 3 + (d : ℝ) ^ 3 = (n : ℝ) := by exact_mod_cast hcd
  have hefR : (e : ℝ) ^ 3 + (f : ℝ) ^ 3 = (n : ℝ) := by exact_mod_cast hef
  have h := triple_product_le (Nat.cast_nonneg a) (Nat.cast_nonneg b)
    (Nat.cast_nonneg c) (Nat.cast_nonneg d) (Nat.cast_nonneg e)
    (Nat.cast_nonneg f) habR hcdR hefR
  exact_mod_cast h

/-- Divisibility of the positive three-product by n is a diagonal condition. -/
theorem dvd_triple_product_iff {n a b c d e f : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (he : 0 < e) (hf : 0 < f)
    (hab : a ^ 3 + b ^ 3 = n) (hcd : c ^ 3 + d ^ 3 = n)
    (hef : e ^ 3 + f ^ 3 = n) :
    n ∣ a * c * e + b * d * f ↔ a = c ∧ c = e ∧ b = d ∧ d = f := by
  constructor
  · intro hdvd
    have hpos : 0 < a * c * e + b * d * f := by positivity
    have hle := triple_product_le_nat hab hcd hef
    have hge : n ≤ a * c * e + b * d * f := Nat.le_of_dvd hpos hdvd
    have heq : a * c * e + b * d * f = n := Nat.le_antisymm hle hge
    have habR : (a : ℝ) ^ 3 + (b : ℝ) ^ 3 = (n : ℝ) := by exact_mod_cast hab
    have hcdR : (c : ℝ) ^ 3 + (d : ℝ) ^ 3 = (n : ℝ) := by exact_mod_cast hcd
    have hefR : (e : ℝ) ^ 3 + (f : ℝ) ^ 3 = (n : ℝ) := by exact_mod_cast hef
    have haR : (0 : ℝ) < a := by exact_mod_cast ha
    have hbR : (0 : ℝ) < b := by exact_mod_cast hb
    have hcR : (0 : ℝ) < c := by exact_mod_cast hc
    have hdR : (0 : ℝ) < d := by exact_mod_cast hd
    have heR : (0 : ℝ) < e := by exact_mod_cast he
    have hfR : (0 : ℝ) < f := by exact_mod_cast hf
    have heqR : (a : ℝ) * c * e + (b : ℝ) * d * f = (n : ℝ) := by
      exact_mod_cast heq
    have h := (triple_product_eq_iff haR hbR hcR hdR heR hfR habR hcdR hefR).mp heqR
    exact_mod_cast h
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    have heq : a * a * a + b * b * b = n := by nlinarith [hef]
    rw [heq]

/-- Primitive roots are invertible modulo their common cube sum. -/
theorem primitive_coord_coprime_sum {n x y : ℕ}
    (hxy : Nat.Coprime x y) (hcubes : x ^ 3 + y ^ 3 = n) :
    Nat.Coprime x n ∧ Nat.Coprime y n := by
  have hx : Nat.Coprime x (x ^ 3 + y ^ 3) := by
    apply (Nat.coprime_add_iff_right (show x ∣ x ^ 3 from dvd_pow_self x (by decide))).mpr
    exact hxy.pow_right 3
  have hy : Nat.Coprime y (x ^ 3 + y ^ 3) := by
    apply (Nat.coprime_add_iff_left (show y ∣ y ^ 3 from dvd_pow_self y (by decide))).mpr
    exact hxy.symm.pow_right 3
  simpa only [hcubes] using And.intro hx hy

/-- On a fixed positive fibre, the determinant vanishes only for equal points. -/
theorem cross_det_eq_zero_iff {n a b c d : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hab : a ^ 3 + b ^ 3 = n) (hcd : c ^ 3 + d ^ 3 = n) :
    a * d - c * b = 0 ↔ a = c ∧ b = d := by
  constructor
  · intro hzero
    have hn : 0 < n := by rw [← hab]; positivity
    have hr := cross_resultant hab hcd
    rw [hzero, zero_mul] at hr
    have hcub : d ^ 3 - b ^ 3 = 0 :=
      (mul_eq_zero.mp hr.symm).resolve_left (ne_of_gt hn)
    have hdb : d = b := (pow_left_inj₀ hd.le hb.le (by decide : 3 ≠ 0)).mp
      (sub_eq_zero.mp hcub)
    have hmul : (a - c) * b = 0 := by rw [hdb] at hzero; nlinarith only [hzero]
    have hac : a = c := sub_eq_zero.mp
      ((mul_eq_zero.mp hmul).resolve_right (ne_of_gt hb))
    exact ⟨hac, hdb.symm⟩
  · rintro ⟨rfl, rfl⟩
    ring

/-- Two positive representations have cross determinant smaller than n^(2/3). -/
theorem cross_det_cube_lt {n a b c d : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hab : a ^ 3 + b ^ 3 = n) (hcd : c ^ 3 + d ^ 3 = n) :
    |a * d - c * b| ^ 3 < n ^ 2 := by
  have hn : 0 < n := by rw [← hab]; positivity
  have halt : a ^ 3 < n := by nlinarith [pow_pos hb 3]
  have hblt : b ^ 3 < n := by nlinarith [pow_pos ha 3]
  have hclt : c ^ 3 < n := by nlinarith [pow_pos hd 3]
  have hdlt : d ^ 3 < n := by nlinarith [pow_pos hc 3]
  by_cases h : c * b ≤ a * d
  · have habsle : |a * d - c * b| ≤ a * d := by
      rw [abs_of_nonneg (sub_nonneg.mpr h)]
      nlinarith [mul_pos hc hb]
    have hp : (a * d) ^ 3 < n ^ 2 := by
      calc
        (a * d) ^ 3 = a ^ 3 * d ^ 3 := by ring
        _ < n * d ^ 3 := mul_lt_mul_of_pos_right halt (pow_pos hd 3)
        _ < n * n := mul_lt_mul_of_pos_left hdlt hn
        _ = n ^ 2 := by ring
    exact lt_of_le_of_lt (pow_le_pow_left₀ (abs_nonneg _) habsle 3) hp
  · have h' : a * d ≤ c * b := le_of_not_ge h
    have habsle : |a * d - c * b| ≤ c * b := by
      rw [abs_of_nonpos (sub_nonpos.mpr h')]
      nlinarith [mul_pos ha hd]
    have hp : (c * b) ^ 3 < n ^ 2 := by
      calc
        (c * b) ^ 3 = c ^ 3 * b ^ 3 := by ring
        _ < n * b ^ 3 := mul_lt_mul_of_pos_right hclt (pow_pos hb 3)
        _ < n * n := mul_lt_mul_of_pos_left hblt hn
        _ = n ^ 2 := by ring
    exact lt_of_le_of_lt (pow_le_pow_left₀ (abs_nonneg _) habsle 3) hp

/-- Unordered representatives improve the determinant height by a factor of two. -/
theorem unordered_cross_det_cube_lt {n a b c d : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hab : a ^ 3 + b ^ 3 = n) (hcd : c ^ 3 + d ^ 3 = n)
    (habord : a ≤ b) (hcdord : c ≤ d) :
    2 * |a * d - c * b| ^ 3 < n ^ 2 := by
  have hn : 0 < n := by rw [← hab]; positivity
  have ha3 : a ^ 3 ≤ b ^ 3 := pow_le_pow_left₀ ha.le habord 3
  have hc3 : c ^ 3 ≤ d ^ 3 := pow_le_pow_left₀ hc.le hcdord 3
  have halt : 2 * a ^ 3 ≤ n := by linarith
  have hclt : 2 * c ^ 3 ≤ n := by linarith
  have hblt : b ^ 3 < n := by nlinarith [pow_pos ha 3]
  have hdlt : d ^ 3 < n := by nlinarith [pow_pos hc 3]
  by_cases h : c * b ≤ a * d
  · have habsle : |a * d - c * b| ≤ a * d := by
      rw [abs_of_nonneg (sub_nonneg.mpr h)]
      nlinarith [mul_pos hc hb]
    have hp : 2 * (a * d) ^ 3 < n ^ 2 := by
      calc
        2 * (a * d) ^ 3 = (2 * a ^ 3) * d ^ 3 := by ring
        _ ≤ n * d ^ 3 := mul_le_mul_of_nonneg_right halt (by positivity)
        _ < n * n := mul_lt_mul_of_pos_left hdlt hn
        _ = n ^ 2 := by ring
    have hpw := pow_le_pow_left₀ (abs_nonneg _) habsle 3
    linarith
  · have h' : a * d ≤ c * b := le_of_not_ge h
    have habsle : |a * d - c * b| ≤ c * b := by
      rw [abs_of_nonpos (sub_nonpos.mpr h')]
      nlinarith [mul_pos ha hd]
    have hp : 2 * (c * b) ^ 3 < n ^ 2 := by
      calc
        2 * (c * b) ^ 3 = (2 * c ^ 3) * b ^ 3 := by ring
        _ ≤ n * b ^ 3 := mul_le_mul_of_nonneg_right hclt (by positivity)
        _ < n * n := mul_lt_mul_of_pos_left hblt hn
        _ = n ^ 2 := by ring
    have hpw := pow_le_pow_left₀ (abs_nonneg _) habsle 3
    linarith

/-- The quadratic inequality behind the weighted ternary Elias bound. -/
theorem ternary_disagreement_le (u v : ℝ) :
    1 - ((1 - u - v) ^ 2 + u ^ 2 + v ^ 2) ≤
      2 * (u + v) - (3 / 2 : ℝ) * (u + v) ^ 2 := by
  nlinarith [sq_nonneg (u - v)]

/-- Cauchy-Schwarz in the weighted form needed for allocation coordinates. -/
theorem weighted_cauchy {ι : Type*} (s : Finset ι) (w z : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) :
    (∑ i ∈ s, w i * z i) ^ 2 ≤ (∑ i ∈ s, w i) * ∑ i ∈ s, w i * (z i) ^ 2 := by
  exact Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul s hw
    (fun i hi => mul_nonneg (hw i hi) (sq_nonneg (z i))) (fun i _ => by ring)

/-- Extra fixed allocation mass may be included in the Cauchy-Schwarz denominator. -/
theorem weighted_cauchy_total {ι : Type*} (s : Finset ι) (w z : ι → ℝ) {W : ℝ}
    (hw : ∀ i ∈ s, 0 ≤ w i) (htotal : ∑ i ∈ s, w i ≤ W) :
    (∑ i ∈ s, w i * z i) ^ 2 ≤ W * ∑ i ∈ s, w i * (z i) ^ 2 := by
  exact (weighted_cauchy s w z hw).trans
    (mul_le_mul_of_nonneg_right htotal
      (Finset.sum_nonneg fun i hi => mul_nonneg (hw i hi) (sq_nonneg (z i))))

/-- The concave disagreement quadratic is increasing up to radius 2W/3. -/
theorem radius_quadratic_bound {W ρ R : ℝ} (hW : 0 ≤ W)
    (hR : R ≤ ρ * W) (hρ : ρ ≤ 2 / 3) :
    2 * R * W - (3 / 2 : ℝ) * R ^ 2 ≤
      W ^ 2 * (2 * ρ - (3 / 2 : ℝ) * ρ ^ 2) := by
  have hρW : ρ * W ≤ (2 / 3 : ℝ) * W := mul_le_mul_of_nonneg_right hρ hW
  have h₁ : 0 ≤ ρ * W - R := sub_nonneg.mpr hR
  have h₂ : 0 ≤ 2 * W - (3 / 2 : ℝ) * (ρ * W + R) := by linarith
  nlinarith [mul_nonneg h₁ h₂]

/-- Averaged ternary disagreement inside a weighted ball satisfies the Elias quadratic. -/
theorem weighted_ternary_disagreement_le {ι : Type*} (s : Finset ι)
    (w u v : ι → ℝ) {W ρ : ℝ}
    (hw : ∀ i ∈ s, 0 ≤ w i) (hW : 0 < W)
    (htotal : ∑ i ∈ s, w i ≤ W)
    (hR : ∑ i ∈ s, w i * (u i + v i) ≤ ρ * W)
    (hρ : ρ ≤ 2 / 3) :
    ∑ i ∈ s, w i * (1 - ((1 - u i - v i) ^ 2 + (u i) ^ 2 + (v i) ^ 2)) ≤
      W * (2 * ρ - (3 / 2 : ℝ) * ρ ^ 2) := by
  let R : ℝ := ∑ i ∈ s, w i * (u i + v i)
  let U : ℝ := ∑ i ∈ s, w i * (u i + v i) ^ 2
  have hsum :
      (∑ i ∈ s, w i * (1 - ((1 - u i - v i) ^ 2 + (u i) ^ 2 + (v i) ^ 2))) ≤
        2 * R - (3 / 2 : ℝ) * U := by
    calc
      _ ≤ ∑ i ∈ s, w i * (2 * (u i + v i) - (3 / 2 : ℝ) * (u i + v i) ^ 2) := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_left (ternary_disagreement_le (u i) (v i)) (hw i hi)
      _ = _ := by
        simp only [R, U, mul_sub, Finset.sum_sub_distrib]
        simp_rw [show ∀ i, w i * (2 * (u i + v i)) = 2 * (w i * (u i + v i)) by
          intro i; ring]
        simp_rw [show ∀ i, w i * ((3 / 2 : ℝ) * (u i + v i) ^ 2) =
          (3 / 2 : ℝ) * (w i * (u i + v i) ^ 2) by intro i; ring]
        rw [Finset.mul_sum, Finset.mul_sum]
  have hCS : R ^ 2 ≤ W * U := weighted_cauchy_total s w (fun i => u i + v i) hw htotal
  have hquad := radius_quadratic_bound hW.le hR hρ
  have hmul : W * (2 * R - (3 / 2 : ℝ) * U) ≤
      W * (W * (2 * ρ - (3 / 2 : ℝ) * ρ ^ 2)) := by
    change 2 * R * W - (3 / 2 : ℝ) * R ^ 2 ≤
      W ^ 2 * (2 * ρ - (3 / 2 : ℝ) * ρ ^ 2) at hquad
    nlinarith only [hCS, hquad]
  exact hsum.trans (le_of_mul_le_mul_left hmul hW)

/-- The averaged-distance inequality gives the numerical Elias cardinality bound. -/
theorem elias_numeric_bound {m W ρ : ℝ} (hm : 0 < m) (hW : 0 < W)
    (hD : 0 < 1 - 6 * ρ + (9 / 2 : ℝ) * ρ ^ 2)
    (hdis : m * (m - 1) * (W / 3) ≤
      m ^ 2 * W * (2 * ρ - (3 / 2 : ℝ) * ρ ^ 2)) :
    m ≤ 1 / (1 - 6 * ρ + (9 / 2 : ℝ) * ρ ^ 2) := by
  have hprod : (m * W) * (m * (1 - 6 * ρ + (9 / 2 : ℝ) * ρ ^ 2) - 1) ≤ 0 := by
    nlinarith only [hdis]
  have hcancel : m * (1 - 6 * ρ + (9 / 2 : ℝ) * ρ ^ 2) - 1 ≤ 0 :=
    le_of_mul_le_mul_left (by simpa only [mul_zero] using hprod) (mul_pos hm hW)
  apply (le_div_iff₀ hD).mpr
  linarith

end Erdos829Aux.GlobalProducts
