import Submission.SquarefreeCubic
import Submission.SquarefreeRothAlgebra

/-!
# Roth's quarter-power bound for squarefree gaps

The small-prime sieve and
squarefree enumeration are imported from `Submission.SquarefreeCubic`;
no conjectural squarefree-gap assertion is imported or used.
The determinant positivity certificate is imported from the algebra
helper.  Counting is over arbitrary finite sets of actual natural witnesses.
-/

open scoped BigOperators

namespace SquarefreeRoth

/-- A large-square witness, with no primality assumption on the base. -/
def Witness (N H : ℕ) (w : ℕ × ℕ) : Prop :=
  H < w.1 ∧ 0 < w.2 ∧ N < w.2 * w.1 ^ 2 ∧ w.2 * w.1 ^ 2 ≤ N + H

lemma witness_base_injective {N H : ℕ} (hH : 0 < H)
    {a b : ℕ × ℕ} (ha : Witness N H a) (hb : Witness N H b)
    (hab : a.1 = b.1) : a = b := by
  have hd : H < a.1 := ha.1
  have hsq : H < a.1 ^ 2 := by nlinarith
  have hq : a.2 = b.2 := by
    rcases lt_trichotomy a.2 b.2 with h | h | h
    · have hmul := Nat.mul_le_mul_right (a.1 ^ 2) (show a.2 + 1 ≤ b.2 by omega)
      have hn := hb.2.2.2
      rw [← hab] at hn
      nlinarith [ha.2.2.1]
    · exact h
    · have hmul := Nat.mul_le_mul_right (a.1 ^ 2) (show b.2 + 1 ≤ a.2 by omega)
      have hn := hb.2.2.1
      rw [← hab] at hn
      nlinarith [ha.2.2.2]
  exact Prod.ext hab hq

/-- The reciprocal-square curvature coefficient is at most `3/P⁴`. -/
lemma reciprocal_coefficient_le (P x y z : ℚ)
    (hP : 0 < P) (hx : P ≤ x) (hy : P ≤ y) (hz : P ≤ z) :
    1 / (x * y * z ^ 2) + 1 / (x * y ^ 2 * z) +
      1 / (x ^ 2 * y * z) ≤ 3 / P ^ 4 := by
  have hx0 : 0 < x := hP.trans_le hx
  have hy0 : 0 < y := hP.trans_le hy
  have hz0 : 0 < z := hP.trans_le hz
  have h₁ : P ^ 4 ≤ x * y * z ^ 2 := by
    calc
      P ^ 4 = P * P * P ^ 2 := by ring
      _ ≤ x * y * z ^ 2 := by gcongr
  have h₂ : P ^ 4 ≤ x * y ^ 2 * z := by
    calc
      P ^ 4 = P * P ^ 2 * P := by ring
      _ ≤ x * y ^ 2 * z := by gcongr
  have h₃ : P ^ 4 ≤ x ^ 2 * y * z := by
    calc
      P ^ 4 = P ^ 2 * P * P := by ring
      _ ≤ x ^ 2 * y * z := by gcongr
  have h₁' := one_div_le_one_div_of_le (pow_pos hP 4) h₁
  have h₂' := one_div_le_one_div_of_le (pow_pos hP 4) h₂
  have h₃' := one_div_le_one_div_of_le (pow_pos hP 4) h₃
  simp only [div_eq_mul_inv, one_mul] at h₁' h₂' h₃' ⊢
  linarith

lemma offset_div_square_le (P x e H : ℚ)
    (hP : 0 < P) (hx : P ≤ x) (he : 0 ≤ e) (heH : e ≤ H) :
    0 ≤ e / x ^ 2 ∧ e / x ^ 2 ≤ H / P ^ 2 := by
  have hx0 : 0 < x := hP.trans_le hx
  constructor
  · positivity
  · calc
      e / x ^ 2 ≤ H / x ^ 2 := div_le_div_of_nonneg_right heH (sq_nonneg x)
      _ ≤ H / P ^ 2 := div_le_div_of_nonneg_left (he.trans heH)
        (pow_pos hP 2) (pow_le_pow_left₀ hP.le hx 2)

/-- Derivative-free reciprocal-square determinant estimate, including the
nonnegative-offset error constant `1` (rather than `2`). -/
lemma determinant_bound (N H P R x y z q₁ q₂ q₃ : ℚ)
    (hN : 0 ≤ N) (hH : 0 ≤ H) (hP : 0 < P)
    (hx : P ≤ x) (hxy : x < y) (hyz : y < z) (hR : z - x ≤ R)
    (hn₁ : N ≤ q₁ * x ^ 2) (hn₁' : q₁ * x ^ 2 ≤ N + H)
    (hn₂ : N ≤ q₂ * y ^ 2) (hn₂' : q₂ * y ^ 2 ≤ N + H)
    (hn₃ : N ≤ q₃ * z ^ 2) (hn₃' : q₃ * z ^ 2 ≤ N + H) :
    |(z - y) * q₁ - (z - x) * q₂ + (y - x) * q₃| ≤
      (3 / 4 : ℚ) * N * R ^ 3 / P ^ 4 + H * R / P ^ 2 := by
  let r := y - x
  let s := z - y
  let t := z - x
  let C := 1 / (x * y * z ^ 2) + 1 / (x * y ^ 2 * z) + 1 / (x ^ 2 * y * z)
  let e₁ := q₁ * x ^ 2 - N
  let e₂ := q₂ * y ^ 2 - N
  let e₃ := q₃ * z ^ 2 - N
  let A := s * (e₁ / x ^ 2) + r * (e₃ / z ^ 2)
  let B := t * (e₂ / y ^ 2)
  have hx0 : 0 < x := hP.trans_le hx
  have hy0 : 0 < y := hx0.trans hxy
  have hz0 : 0 < z := hy0.trans hyz
  have hr : 0 ≤ r := (sub_pos.mpr hxy).le
  have hs : 0 ≤ s := (sub_pos.mpr hyz).le
  have ht : 0 ≤ t := (sub_pos.mpr (hxy.trans hyz)).le
  have hR0 : 0 ≤ R := ht.trans hR
  have hrt : r + s = t := by dsimp [r, s, t]; ring
  have hC0 : 0 ≤ C := by dsimp [C]; positivity
  have hC : C ≤ 3 / P ^ 4 := reciprocal_coefficient_le P x y z hP hx
    (hx.trans hxy.le) (hx.trans (hxy.trans hyz).le)
  have hprod : r * s * t ≤ R ^ 3 / 4 := by
    have hfour : 4 * r * s ≤ t ^ 2 := by nlinarith [sq_nonneg (r - s)]
    have hmul := mul_le_mul_of_nonneg_right hfour ht
    have hpow := pow_le_pow_left₀ ht hR 3
    nlinarith
  have hmain : N * (r * s * t) * C ≤ (3 / 4 : ℚ) * N * R ^ 3 / P ^ 4 := by
    calc
      N * (r * s * t) * C ≤ N * (R ^ 3 / 4) * (3 / P ^ 4) := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left hprod hN) hC hC0 (by positivity)
      _ = (3 / 4 : ℚ) * N * R ^ 3 / P ^ 4 := by ring
  have he₁ := offset_div_square_le P x e₁ H hP hx (by dsimp [e₁]; linarith)
    (by dsimp [e₁]; linarith)
  have he₂ := offset_div_square_le P y e₂ H hP (hx.trans hxy.le)
    (by dsimp [e₂]; linarith) (by dsimp [e₂]; linarith)
  have he₃ := offset_div_square_le P z e₃ H hP (hx.trans (hxy.trans hyz).le)
    (by dsimp [e₃]; linarith) (by dsimp [e₃]; linarith)
  have hA0 : 0 ≤ A := add_nonneg (mul_nonneg hs he₁.1) (mul_nonneg hr he₃.1)
  have hB0 : 0 ≤ B := mul_nonneg ht he₂.1
  have hA : A ≤ H * t / P ^ 2 := by
    have h₁ := mul_le_mul_of_nonneg_left he₁.2 hs
    have h₃ := mul_le_mul_of_nonneg_left he₃.2 hr
    calc
      A ≤ s * (H / P ^ 2) + r * (H / P ^ 2) := add_le_add h₁ h₃
      _ = H * t / P ^ 2 := by rw [← hrt]; ring
  have hB : B ≤ H * t / P ^ 2 := by
    calc
      B ≤ t * (H / P ^ 2) := mul_le_mul_of_nonneg_left he₂.2 ht
      _ = H * t / P ^ 2 := by ring
  have herror : |A - B| ≤ H * R / P ^ 2 := by
    have hsmall : |A - B| ≤ H * t / P ^ 2 := abs_le.mpr ⟨by linarith, by linarith⟩
    exact hsmall.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hR hH) (sq_nonneg P))
  have hid : (z - y) * q₁ - (z - x) * q₂ + (y - x) * q₃ =
      N * (r * s * t) * C + (A - B) := by
    have hi := SquarefreeRothAlgebra.inverse_square_crossproduct x y z
      hx0.ne' hy0.ne' hz0.ne'
    have hc : (x * y + x * z + y * z) / (x ^ 2 * y ^ 2 * z ^ 2) = C := by
      dsimp [C]
      field_simp
    rw [show (y - x) * (z - y) * (z - x) * (x * y + x * z + y * z) /
        (x ^ 2 * y ^ 2 * z ^ 2) = r * s * t * C by
          rw [← hc]; dsimp [r, s, t]; ring] at hi
    have hd : (z - y) * q₁ - (z - x) * q₂ + (y - x) * q₃ =
        N * ((z - y) / x ^ 2 - (z - x) / y ^ 2 + (y - x) / z ^ 2) + (A - B) := by
      dsimp [A, B, e₁, e₂, e₃, r, s, t]
      field_simp
      ring
    rw [hd, hi]
    ring
  rw [hid]
  calc
    |N * (r * s * t) * C + (A - B)| ≤ |N * (r * s * t) * C| + |A - B| := abs_add_le _ _
    _ = N * (r * s * t) * C + |A - B| := by
      rw [abs_of_nonneg (by positivity)]
    _ ≤ (3 / 4 : ℚ) * N * R ^ 3 / P ^ 4 + H * R / P ^ 2 := add_le_add hmain herror

/-- An ordered natural witness triple has determinant at least one. -/
lemma determinant_ge_one {N H : ℕ} (hH : 0 < H)
    {a b c : ℕ × ℕ} (ha : Witness N H a) (hb : Witness N H b) (hc : Witness N H c)
    (hab : a.1 < b.1) (hbc : b.1 < c.1) :
    (1 : ℚ) ≤ ((c.1 : ℚ) - b.1) * a.2 - ((c.1 : ℚ) - a.1) * b.2 +
      ((b.1 : ℚ) - a.1) * c.2 := by
  have h := SquarefreeRothAlgebra.witness_determinant_positive
    N H a.1 b.1 c.1 a.2 b.2 c.2 hH ha.1 hab hbc
    ha.2.1 hb.2.1 hc.2.1 ha.2.2.1 ha.2.2.2 hb.2.2.1 hb.2.2.2 hc.2.2.1 hc.2.2.2
  have h' : (1 : ℤ) ≤ ((c.1 : ℤ) - b.1) * a.2 - ((c.1 : ℤ) - a.1) * b.2 +
      ((b.1 : ℤ) - a.1) * c.2 := by omega
  exact_mod_cast h'

/-- The rational-window certificate: the determinant is simultaneously
at least one and strictly smaller than one, so such a triple cannot exist. -/
lemma no_three_in_window {N H P K : ℕ}
    (hH : 0 < H) (hP : H ≤ P) (hN : 64 * H < N) (hmain : N ≤ P * K ^ 3)
    {a b c : ℕ × ℕ} (ha : Witness N H a) (hb : Witness N H b) (hc : Witness N H c)
    (hPa : P < a.1) (hab : a.1 < b.1) (hbc : b.1 < c.1)
    (hspan : (c.1 : ℚ) - a.1 ≤ (P : ℚ) / K) : False := by
  have hPK : 4 * H < P * K :=
    SquarefreeRothAlgebra.rational_window_error_condition N H P K hH hP hN hmain
  have hP0 : 0 < P := hH.trans_le hP
  have hK0 : 0 < K := by nlinarith
  have hPq : (0 : ℚ) < P := by exact_mod_cast hP0
  have hKq : (0 : ℚ) < K := by exact_mod_cast hK0
  have hmainq : (N : ℚ) ≤ (P : ℚ) * (K : ℚ) ^ 3 := by exact_mod_cast hmain
  have hPKq : 4 * (H : ℚ) < (P : ℚ) * K := by exact_mod_cast hPK
  have hratio : (N : ℚ) / ((P : ℚ) * (K : ℚ) ^ 3) ≤ 1 :=
    (div_le_one (by positivity)).mpr hmainq
  have herror : (H : ℚ) / ((P : ℚ) * K) < 1 / 4 := by
    apply (div_lt_iff₀ (mul_pos hPq hKq)).mpr
    linarith
  have hupper : (3 / 4 : ℚ) * N * ((P : ℚ) / K) ^ 3 / (P : ℚ) ^ 4 +
      (H : ℚ) * ((P : ℚ) / K) / (P : ℚ) ^ 2 < 1 := by
    have hid : (3 / 4 : ℚ) * N * ((P : ℚ) / K) ^ 3 / (P : ℚ) ^ 4 +
        (H : ℚ) * ((P : ℚ) / K) / (P : ℚ) ^ 2 =
        (3 / 4 : ℚ) * ((N : ℚ) / ((P : ℚ) * (K : ℚ) ^ 3)) +
          (H : ℚ) / ((P : ℚ) * K) := by
      field_simp
    rw [hid]
    linarith
  have hbnd := determinant_bound N H P ((P : ℚ) / K) a.1 b.1 c.1 a.2 b.2 c.2
    (by positivity) (by positivity) hPq (by exact_mod_cast hPa.le)
    (by exact_mod_cast hab) (by exact_mod_cast hbc) hspan
    (by exact_mod_cast ha.2.2.1.le) (by exact_mod_cast ha.2.2.2)
    (by exact_mod_cast hb.2.2.1.le) (by exact_mod_cast hb.2.2.2)
    (by exact_mod_cast hc.2.2.1.le) (by exact_mod_cast hc.2.2.2)
  have hlow := determinant_ge_one hH ha hb hc hab hbc
  have hle := le_abs_self (((c.1 : ℚ) - b.1) * a.2 - ((c.1 : ℚ) - a.1) * b.2 +
      ((b.1 : ℚ) - a.1) * c.2)
  linarith

/-- Right-closed rational bins, encoded by natural Euclidean division. -/
def bin (P K d : ℕ) : ℕ := (K * (d - P) - 1) / P

lemma bin_bounds {P K d : ℕ} (hP : 0 < P) (hK : 0 < K)
    (hd : P < d) (hd' : d ≤ 2 * P) :
    bin P K d < K ∧ bin P K d * P < K * (d - P) ∧
      K * (d - P) ≤ (bin P K d + 1) * P := by
  let v := K * (d - P)
  have hv : 0 < v := Nat.mul_pos hK (Nat.sub_pos_of_lt hd)
  have hvbound : v ≤ K * P := Nat.mul_le_mul_left K (show d - P ≤ P by omega)
  have hj : bin P K d < K := by
    apply (Nat.div_lt_iff_lt_mul hP).mpr
    change v - 1 < K * P
    omega
  have hlo := Nat.div_mul_le_self (v - 1) P
  have hmod := Nat.mod_lt (v - 1) hP
  have heq := Nat.div_add_mod (v - 1) P
  have hlow : bin P K d * P < v := by
    change (v - 1) / P * P < v
    omega
  have hhigh : v ≤ (bin P K d + 1) * P := by
    change v ≤ ((v - 1) / P + 1) * P
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm P] at *
    omega
  exact ⟨hj, hlow, hhigh⟩

lemma bin_span {P K x z : ℕ} (hP : 0 < P) (hK : 0 < K)
    (hx : P < x) (hx' : x ≤ 2 * P) (hz : P < z) (hz' : z ≤ 2 * P)
    (hbin : bin P K x = bin P K z) :
    (z : ℚ) - x ≤ (P : ℚ) / K := by
  have hlo := (bin_bounds hP hK hx hx').2.1
  have hhi := (bin_bounds hP hK hz hz').2.2
  rw [← hbin] at hhi
  have hloq : (bin P K x : ℚ) * P < (K : ℚ) * ((x - P : ℕ) : ℚ) := by
    exact_mod_cast hlo
  have hhiq : (K : ℚ) * ((z - P : ℕ) : ℚ) ≤ ((bin P K x : ℚ) + 1) * P := by
    exact_mod_cast hhi
  rw [Nat.cast_sub hx.le] at hloq
  rw [Nat.cast_sub hz.le] at hhiq
  apply (le_div_iff₀ (by exact_mod_cast hK : (0 : ℚ) < K)).mpr
  nlinarith

/-- A fully explicit three-element cardinality argument. -/
lemma card_le_two_of_no_ordered_triple (S : Finset (ℕ × ℕ))
    (hinj : Set.InjOn Prod.fst (S : Set (ℕ × ℕ)))
    (htriple : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a.1 < b.1 → b.1 < c.1 → False) :
    S.card ≤ 2 := by
  by_contra h
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ :=
    Finset.two_lt_card_iff.mp (show 2 < S.card by omega)
  have hab' : a.1 ≠ b.1 := fun h => hab (hinj ha hb h)
  have hac' : a.1 ≠ c.1 := fun h => hac (hinj ha hc h)
  have hbc' : b.1 ≠ c.1 := fun h => hbc (hinj hb hc h)
  have hord : (a.1 < b.1 ∧ b.1 < c.1) ∨ (a.1 < c.1 ∧ c.1 < b.1) ∨
      (b.1 < a.1 ∧ a.1 < c.1) ∨ (b.1 < c.1 ∧ c.1 < a.1) ∨
      (c.1 < a.1 ∧ a.1 < b.1) ∨ (c.1 < b.1 ∧ b.1 < a.1) := by omega
  rcases hord with h | h | h | h | h | h
  · exact htriple a ha b hb c hc h.1 h.2
  · exact htriple a ha c hc b hb h.1 h.2
  · exact htriple b hb a ha c hc h.1 h.2
  · exact htriple b hb c hc a ha h.1 h.2
  · exact htriple c hc a ha b hb h.1 h.2
  · exact htriple c hc b hb a ha h.1 h.2

/-- At most two witnesses per bin, and therefore at most `2K` in a band.
This includes `K > P`; no correspondence or cardinality statement is assumed. -/
lemma band_card_le (N H P K : ℕ) (S : Finset (ℕ × ℕ))
    (hH : 0 < H) (hP : H ≤ P) (hN : 64 * H < N) (hmain : N ≤ P * K ^ 3)
    (hS : ∀ w ∈ S, Witness N H w ∧ P < w.1 ∧ w.1 ≤ 2 * P) :
    S.card ≤ 2 * K := by
  have hP0 : 0 < P := hH.trans_le hP
  have hPK := SquarefreeRothAlgebra.rational_window_error_condition N H P K hH hP hN hmain
  have hK0 : 0 < K := by nlinarith
  have hinj : Set.InjOn Prod.fst (S : Set (ℕ × ℕ)) := by
    intro a ha b hb hab
    exact witness_base_injective hH (hS a ha).1 (hS b hb).1 hab
  have hfiber : ∀ j ∈ Finset.range K, (S.filter (fun w => bin P K w.1 = j)).card ≤ 2 := by
    intro j hj
    apply card_le_two_of_no_ordered_triple
    · exact hinj.mono (Finset.filter_subset _ _)
    · intro a ha b hb c hc hab hbc
      obtain ⟨haS, haj⟩ := Finset.mem_filter.mp ha
      obtain ⟨hbS, hbj⟩ := Finset.mem_filter.mp hb
      obtain ⟨hcS, hcj⟩ := Finset.mem_filter.mp hc
      have has := hS a haS
      have hbs := hS b hbS
      have hcs := hS c hcS
      apply no_three_in_window hH hP hN hmain has.1 hbs.1 hcs.1 has.2.1 hab hbc
      exact bin_span hP0 hK0 has.2.1 has.2.2 hcs.2.1 hcs.2.2 (haj.trans hcj.symm)
  have hc := Finset.card_le_mul_card_image_of_maps_to
    (f := fun w : ℕ × ℕ => bin P K w.1) (s := S) (t := Finset.range K)
    (fun w hw => Finset.mem_range.mpr (bin_bounds hP0 hK0 (hS w hw).2.1 (hS w hw).2.2).1)
    2 hfiber
  simpa only [Finset.card_range] using hc

/-- The integer-base bound is available regardless of how short the windows are. -/
lemma band_card_le_bases (N H P : ℕ) (S : Finset (ℕ × ℕ))
    (hH : 0 < H) (hS : ∀ w ∈ S, Witness N H w ∧ P < w.1 ∧ w.1 ≤ 2 * P) :
    S.card ≤ P := by
  calc
    S.card ≤ (Finset.Ioc P (2 * P)).card := by
      apply Finset.card_le_card_of_injOn Prod.fst
      · intro w hw
        exact Finset.mem_Ioc.mpr (hS w hw).2
      · intro a ha b hb hab
        exact witness_base_injective hH (hS a ha).1 (hS b hb).1 hab
    _ = P := by simp [Nat.card_Ioc]; omega

lemma band_card_le_min (N H P K : ℕ) (S : Finset (ℕ × ℕ))
    (hH : 0 < H) (hP : H ≤ P) (hN : 64 * H < N) (hmain : N ≤ P * K ^ 3)
    (hS : ∀ w ∈ S, Witness N H w ∧ P < w.1 ∧ w.1 ≤ 2 * P) :
    S.card ≤ min P (2 * K) :=
  le_min (band_card_le_bases N H P S hH hS) (band_card_le N H P K S hH hP hN hmain hS)

/-- Coverage by dyadic right-closed bands, proved by induction. -/
lemma dyadic_cover (H L d : ℕ) (hd : H < d) (hd' : d ≤ 2 ^ L * H) :
    ∃ k < L, 2 ^ k * H < d ∧ d ≤ 2 * (2 ^ k * H) := by
  induction L with
  | zero => simp only [pow_zero, one_mul] at hd'; omega
  | succ L ih =>
    by_cases h : d ≤ 2 ^ L * H
    · obtain ⟨k, hk, hkd, hdk⟩ := ih h
      exact ⟨k, by omega, hkd, hdk⟩
    · refine ⟨L, by omega, by omega, ?_⟩
      simpa only [pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hd'

/-- The rational dyadic ceiling targets have no additive logarithmic loss:
on every active band they are at most twice the unrounded target. -/
lemma dyadic_target (N H k : ℕ) (U : ℚ)
    (hH : 0 < H) (hU : 0 < U) (hNU : (N : ℚ) ≤ (H : ℚ) * U ^ 3)
    (hactive : 2 ^ k * H < N) :
    N ≤ (2 ^ k * H) * ⌈U * (4 / 5 : ℚ) ^ k⌉₊ ^ 3 ∧
      (⌈U * (4 / 5 : ℚ) ^ k⌉₊ : ℚ) ≤ 2 * (U * (4 / 5 : ℚ) ^ k) := by
  let P := 2 ^ k * H
  let a := U * (4 / 5 : ℚ) ^ k
  let K := ⌈a⌉₊
  have hP : (0 : ℚ) < P := by dsimp [P]; positivity
  have ha : 0 < a := by dsimp [a]; positivity
  have hid : (P : ℚ) * a ^ 3 = (H : ℚ) * U ^ 3 * (128 / 125 : ℚ) ^ k := by
    dsimp [P, a]
    have hp : ((4 / 5 : ℚ) ^ k) ^ 3 = ((4 / 5 : ℚ) ^ 3) ^ k := by
      rw [← pow_mul, ← pow_mul, Nat.mul_comm k 3]
    simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, mul_pow]
    rw [hp]
    calc
      (2 : ℚ) ^ k * H * (U ^ 3 * ((4 / 5 : ℚ) ^ 3) ^ k) =
          (H : ℚ) * U ^ 3 * ((2 : ℚ) ^ k * ((4 / 5 : ℚ) ^ 3) ^ k) := by ring
      _ = (H : ℚ) * U ^ 3 * ((2 : ℚ) * (4 / 5 : ℚ) ^ 3) ^ k := by rw [mul_pow]
      _ = (H : ℚ) * U ^ 3 * (128 / 125 : ℚ) ^ k := by norm_num
  have hscale : (N : ℚ) ≤ (P : ℚ) * a ^ 3 := by
    rw [hid]
    calc
      (N : ℚ) ≤ (H : ℚ) * U ^ 3 := hNU
      _ ≤ (H : ℚ) * U ^ 3 * (128 / 125 : ℚ) ^ k := by
        have hpow : (1 : ℚ) ≤ (128 / 125 : ℚ) ^ k := one_le_pow₀ (by norm_num)
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hpow
          (show (0 : ℚ) ≤ (H : ℚ) * U ^ 3 by positivity)
  have hPN : (P : ℚ) < N := by exact_mod_cast hactive
  have ha1 : 1 < a := by
    by_contra h
    have hle : a ≤ 1 := le_of_not_gt h
    have hc : a ^ 3 ≤ 1 := by simpa using pow_le_pow_left₀ ha.le hle 3
    have hm := mul_le_mul_of_nonneg_left hc hP.le
    linarith
  have hceil : a ≤ (K : ℚ) := Nat.le_ceil a
  have hceil' : (K : ℚ) < a + 1 := Nat.ceil_lt_add_one ha.le
  have hmain : (N : ℚ) ≤ (P : ℚ) * (K : ℚ) ^ 3 := hscale.trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha.le hceil 3) hP.le)
  constructor
  · exact_mod_cast hmain
  · change (K : ℚ) ≤ 2 * a
    linarith

lemma geometric_sum_le_five (L : ℕ) :
    (∑ k ∈ Finset.range L, (4 / 5 : ℚ) ^ k) ≤ 5 := by
  have hid : (∑ k ∈ Finset.range L, (4 / 5 : ℚ) ^ k) = 5 * (1 - (4 / 5 : ℚ) ^ L) := by
    induction L with
    | zero => norm_num
    | succ L ih => rw [Finset.sum_range_succ, ih, pow_succ]; ring
  rw [hid]
  have hp : (0 : ℚ) ≤ (4 / 5 : ℚ) ^ L := by positivity
  linarith

/-- Roth's global witness count, stated without roots or a presumed
coefficient/witness correspondence.  It applies to any finite witness set. -/
theorem witnesses_card_le (N H : ℕ) (S : Finset (ℕ × ℕ)) (U : ℚ)
    (hH : 64 ≤ H) (hU : 0 < U) (hNU : (N : ℚ) ≤ (H : ℚ) * U ^ 3)
    (hS : ∀ w ∈ S, Witness N H w) :
    (S.card : ℚ) ≤ 20 * U := by
  classical
  rcases S.eq_empty_or_nonempty with rfl | hnonempty
  · simp only [Finset.card_empty, Nat.cast_zero]
    positivity
  have hH0 : 0 < H := by omega
  obtain ⟨w, hw⟩ := hnonempty
  have hwb := hS w hw
  have hbasic := SquarefreeRothAlgebra.witness_basic_bounds N H w.1 w.2
    hH0 hwb.1 hwb.2.1 hwb.2.2.2
  have hN : 64 * H < N := by nlinarith [hbasic.1]
  have hdN : ∀ w ∈ S, w.1 < N := by
    intro w hw
    have h := hS w hw
    exact (SquarefreeRothAlgebra.witness_basic_bounds N H w.1 w.2 hH0 h.1 h.2.1 h.2.2.2).2.1
  have hex : ∃ L : ℕ, N ≤ 2 ^ L * H := by
    refine ⟨N, ?_⟩
    have hpow : N < 2 ^ N := Nat.lt_two_pow_self
    have hm := Nat.mul_le_mul_left (2 ^ N) (show 1 ≤ H by omega)
    nlinarith
  let L := Nat.find hex
  have htop : N ≤ 2 ^ L * H := Nat.find_spec hex
  have hactive : ∀ k < L, 2 ^ k * H < N := by
    intro k hk
    have h := Nat.find_min hex hk
    omega
  let B := fun k : ℕ => S.filter (fun w => 2 ^ k * H < w.1 ∧ w.1 ≤ 2 * (2 ^ k * H))
  have hcover : S ⊆ (Finset.range L).biUnion B := by
    intro w hw
    obtain ⟨k, hk, hkw, hwk⟩ := dyadic_cover H L w.1 (hS w hw).1 ((hdN w hw).le.trans htop)
    exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_range.mpr hk, Finset.mem_filter.mpr ⟨hw, hkw, hwk⟩⟩
  have hc : S.card ≤ ∑ k ∈ Finset.range L, (B k).card :=
    (Finset.card_le_card hcover).trans Finset.card_biUnion_le
  have hlocal : ∀ k ∈ Finset.range L, ((B k).card : ℚ) ≤ 4 * (U * (4 / 5 : ℚ) ^ k) := by
    intro k hk
    have hkL : k < L := Finset.mem_range.mp hk
    obtain ⟨hmain, hceil⟩ := dyadic_target N H k U hH0 hU hNU (hactive k hkL)
    have hPH : H ≤ 2 ^ k * H := by nlinarith [Nat.one_le_two_pow (n := k)]
    have hb : (B k).card ≤ 2 * ⌈U * (4 / 5 : ℚ) ^ k⌉₊ := by
      apply band_card_le N H (2 ^ k * H) _ (B k) hH0 hPH hN hmain
      intro w hw
      obtain ⟨hwS, hwb⟩ := Finset.mem_filter.mp hw
      exact ⟨hS w hwS, hwb⟩
    have hbq : ((B k).card : ℚ) ≤ 2 * (⌈U * (4 / 5 : ℚ) ^ k⌉₊ : ℚ) := by exact_mod_cast hb
    linarith
  calc
    (S.card : ℚ) ≤ ∑ k ∈ Finset.range L, ((B k).card : ℚ) := by exact_mod_cast hc
    _ ≤ ∑ k ∈ Finset.range L, 4 * (U * (4 / 5 : ℚ) ^ k) := Finset.sum_le_sum hlocal
    _ = (4 * U) * (∑ k ∈ Finset.range L, (4 / 5 : ℚ) ^ k) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ ≤ (4 * U) * 5 := mul_le_mul_of_nonneg_left (geometric_sum_le_five L) (by positivity)
    _ = 20 * U := by ring

/-- Survivors in a wholly nonsquarefree interval inject into actual witnesses
by their chosen prime-square factors; the product recovers the survivor. -/
lemma survivors_card_le_roth (N H : ℕ) (U : ℚ)
    (hH : 64 ≤ H) (hU : 0 < U) (hNU : (N : ℚ) ≤ (H : ℚ) * U ^ 3)
    (hbad : ∀ m : ℕ, N < m → m ≤ N + H → ¬ Squarefree m) :
    ((SquarefreeCubic.survivors N H).card : ℚ) ≤ 20 * U := by
  classical
  let S := SquarefreeCubic.survivors N H
  have hw : ∀ m : S, ∃ w : ℕ × ℕ, Witness N H w ∧ (m : ℕ) = w.2 * w.1 ^ 2 := by
    intro m
    have hm := SquarefreeCubic.mem_survivors.mp m.property
    obtain ⟨p, q, hp, hpH, hq, heq⟩ :=
      SquarefreeCubic.survivor_large_square m.property (hbad m hm.1 hm.2.1)
    refine ⟨(p, q), ⟨hpH, hq, ?_, ?_⟩, heq⟩
    · simpa only [heq] using hm.1
    · simpa only [heq] using hm.2.1
  choose w hw heq using hw
  have hinj : Function.Injective w := by
    intro a b hab
    apply Subtype.ext
    rw [heq a, heq b, hab]
  let T := (Finset.univ : Finset S).image w
  have hT : ∀ a ∈ T, Witness N H a := by
    intro a ha
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp ha
    exact hw m
  have hcard : T.card = S.card := by
    dsimp [T]
    rw [Finset.card_image_of_injOn hinj.injOn]
    simp
  have hcount := witnesses_card_le N H T U hH hU hNU hT
  simpa only [hcard] using hcount

/-- Explicit natural interval criterion for Roth's squarefree gap bound. -/
theorem exists_squarefree_Ioc (N H : ℕ) (hH : 64 ≤ H)
    (hsize : 2 ^ 24 * N ≤ H ^ 4) :
    ∃ m : ℕ, N < m ∧ m ≤ N + H ∧ Squarefree m := by
  by_contra h
  have hbad : ∀ m : ℕ, N < m → m ≤ N + H → ¬ Squarefree m := by
    intro m hm hm' hsf
    exact h ⟨m, hm, hm', hsf⟩
  have hH0 : 0 < H := by omega
  have hU : (0 : ℚ) < (H : ℚ) / 256 := by positivity
  have hs : (2 : ℚ) ^ 24 * (N : ℚ) ≤ (H : ℚ) ^ 4 := by exact_mod_cast hsize
  have hNU : (N : ℚ) ≤ (H : ℚ) * ((H : ℚ) / 256) ^ 3 := by
    norm_num at hs
    nlinarith
  have hcount := survivors_card_le_roth N H ((H : ℚ) / 256) hH hU hNU hbad
  have hcross : (256 : ℚ) * (SquarefreeCubic.survivors N H).card ≤ 20 * (H : ℚ) := by
    linarith
  have hcross' : (256 : ℝ) * (SquarefreeCubic.survivors N H).card ≤ 20 * (H : ℝ) := by
    exact_mod_cast hcross
  have hlo := SquarefreeCubic.survivors_card_ge_twelfth N H (show 48 ≤ H by omega)
  exact SquarefreeRothAlgebra.survivor_contradiction H
    (SquarefreeCubic.survivors N H).card (by exact_mod_cast hH0) hlo (by linarith)

/-- The rounded integer length for the explicit quarter-power bound. -/
noncomputable def rothLength (N : ℕ) : ℕ := ⌈64 * (N : ℝ) ^ (1 / 4 : ℝ)⌉₊

lemma rothLength_spec (N : ℕ) (hN : 1 ≤ N) :
    64 ≤ rothLength N ∧ 2 ^ 24 * N ≤ rothLength N ^ 4 ∧
      (rothLength N : ℝ) ≤ 65 * (N : ℝ) ^ (1 / 4 : ℝ) := by
  let x : ℝ := (N : ℝ) ^ (1 / 4 : ℝ)
  have hx0 : 0 ≤ x := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hfour : x ^ 4 = (N : ℝ) := by
    simpa only [x, one_div, Nat.cast_ofNat] using
      (Real.rpow_inv_natCast_pow (Nat.cast_nonneg N) (by decide : (4 : ℕ) ≠ 0))
  have hx1 : 1 ≤ x := by
    apply (pow_le_pow_iff_left₀ (by norm_num : (0 : ℝ) ≤ 1) hx0
      (by decide : (4 : ℕ) ≠ 0)).mp
    rw [hfour]
    norm_num
    exact_mod_cast hN
  have hceil : 64 * x ≤ (rothLength N : ℝ) := Nat.le_ceil _
  have hceil' : (rothLength N : ℝ) < 64 * x + 1 := Nat.ceil_lt_add_one (by positivity)
  have hHreal : (64 : ℝ) ≤ (rothLength N : ℝ) := by linarith
  have hH : 64 ≤ rothLength N := by exact_mod_cast hHreal
  have hpow : (64 * x) ^ 4 ≤ (rothLength N : ℝ) ^ 4 :=
    pow_le_pow_left₀ (by positivity) hceil 4
  have hsize : (2 : ℝ) ^ 24 * (N : ℝ) ≤ (rothLength N : ℝ) ^ 4 := by
    calc
      (2 : ℝ) ^ 24 * (N : ℝ) = (64 * x) ^ 4 := by rw [mul_pow, hfour]; norm_num
      _ ≤ (rothLength N : ℝ) ^ 4 := hpow
  exact ⟨hH, by exact_mod_cast hsize, by linarith⟩

/-- Uniform explicit Roth bound, valid for every positive starting integer. -/
theorem exists_squarefree_roth (N : ℕ) (hN : 1 ≤ N) :
    ∃ m : ℕ, Squarefree m ∧ N < m ∧
      (m : ℝ) ≤ (N : ℝ) + 65 * (N : ℝ) ^ (1 / 4 : ℝ) := by
  obtain ⟨hH, hsize, hlen⟩ := rothLength_spec N hN
  obtain ⟨m, hNm, hm, hsf⟩ := exists_squarefree_Ioc N (rothLength N) hH hsize
  refine ⟨m, hsf, hNm, ?_⟩
  have hmreal : (m : ℝ) ≤ (N : ℝ) + (rothLength N : ℝ) := by exact_mod_cast hm
  linarith

open SquarefreeSqrt

/-- Every enumerated squarefree gap is at most `65 s(n)^(1/4)`. -/
theorem squarefree_gap_le_roth (n : ℕ) :
    ((Nat.nth Squarefree (n + 1) : ℝ) - (Nat.nth Squarefree n : ℝ)) ≤
      65 * (Nat.nth Squarefree n : ℝ) ^ (1 / 4 : ℝ) := by
  change ((s (n + 1) : ℝ) - (s n : ℝ)) ≤ 65 * (s n : ℝ) ^ (1 / 4 : ℝ)
  obtain ⟨m, hsf, hNm, hm⟩ := exists_squarefree_roth (s n) (by have := s_pos n; omega)
  have hnext : (s (n + 1) : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast next_le_of_squarefree hsf hNm
  linarith

/-- Unconditional Roth quarter-power Big-O bound and every larger exponent. -/
theorem squarefree_gap_isBigO {ε : ℝ} (hε : (1 / 4 : ℝ) ≤ ε) :
    (fun n => ((Nat.nth Squarefree (n + 1) : ℝ) - (Nat.nth Squarefree n : ℝ)))
      =O[Filter.atTop] (fun n => (Nat.nth Squarefree n : ℝ) ^ ε) := by
  change (fun n => ((s (n + 1) : ℝ) - (s n : ℝ)))
    =O[Filter.atTop] (fun n => (s n : ℝ) ^ ε)
  apply Asymptotics.isBigO_iff.mpr
  refine ⟨65, Filter.Eventually.of_forall ?_⟩
  intro n
  simp only [Real.norm_eq_abs, abs_of_pos (gap_pos n),
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg (s n)) ε)]
  apply (squarefree_gap_le_roth n).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 65)
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast s_pos n) hε

/-- The exponent is exactly `1/4`, not just any strictly larger exponent. -/
theorem squarefree_gap_isBigO_roth :
    (fun n => ((Nat.nth Squarefree (n + 1) : ℝ) - (Nat.nth Squarefree n : ℝ)))
      =O[Filter.atTop] (fun n => (Nat.nth Squarefree n : ℝ) ^ (1 / 4 : ℝ)) :=
  squarefree_gap_isBigO le_rfl

#print axioms witnesses_card_le
#print axioms exists_squarefree_Ioc
#print axioms exists_squarefree_roth
#print axioms squarefree_gap_le_roth
#print axioms squarefree_gap_isBigO
#print axioms squarefree_gap_isBigO_roth

end SquarefreeRoth
