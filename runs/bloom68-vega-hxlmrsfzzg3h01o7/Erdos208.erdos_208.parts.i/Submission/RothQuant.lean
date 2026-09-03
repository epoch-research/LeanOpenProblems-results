import Submission.RothLocal

/-!
# Quantitative integer pair labels for square multiples

For natural square multiples hitting `(x, x + H]`, with bases in `[N, 2 * N]`
and `256 * H ≤ N`, this file gives the rational approximation to the integer
pair label, positive- and zero-label gap bounds, the exclusion of two adjacent
zero labels, and the diameter bound for pairs with a fixed gap and positive
label. These are local quantitative lemmas, not a global gap theorem.

`label` is exactly `RothLocal.label` on natural inputs. `ideal` uses the natural
gap `v - u`; all its applications have `u ≤ v`. No rounding occurs in `ideal`
or `scale`: their divisions are in `ℚ`.
-/

namespace RothQuant

/-- The existing integer label, with natural inputs. -/
abbrev label (u v m m' : ℕ) : ℤ :=
  RothLocal.label (u : ℤ) (v : ℤ) (m : ℤ) (m' : ℤ)

/-- The rational ideal label `x (v-u)³ / (u² v²)`. -/
def ideal (x u v : ℕ) : ℚ :=
  (x : ℚ) * (↑(v - u) : ℚ) ^ 3 / ((u : ℚ) ^ 2 * (v : ℚ) ^ 2)

/-- The dyadic normalization `x b³ / N⁴`. -/
def scale (x N b : ℕ) : ℚ :=
  (x : ℚ) * (b : ℚ) ^ 3 / (N : ℚ) ^ 4

lemma ideal_nonneg (x u v : ℕ) : 0 ≤ ideal x u v := by
  unfold ideal
  positivity

lemma ideal_of_le {x u v : ℕ} (huv : u ≤ v) :
    ideal x u v =
      (x : ℚ) * ((v : ℚ) - u) ^ 3 / ((u : ℚ) ^ 2 * (v : ℚ) ^ 2) := by
  simp only [ideal, Nat.cast_sub huv]

@[simp] lemma ideal_add (x u b : ℕ) :
    ideal x u (u + b) =
      (x : ℚ) * (b : ℚ) ^ 3 / ((u : ℚ) ^ 2 * ((u : ℚ) + b) ^ 2) := by
  simp [ideal]

private lemma coefficient_bounds {N a c : ℚ}
    (hN : 0 < N) (ha : N ≤ a) (hc0 : 0 ≤ c) (hc : c ≤ 5 * N) :
    0 ≤ c / a ^ 2 ∧ c / a ^ 2 ≤ 5 / N := by
  have ha0 : 0 < a := hN.trans_le ha
  have hsq : N ^ 2 ≤ a ^ 2 := pow_le_pow_left₀ hN.le ha 2
  refine ⟨div_nonneg hc0 (sq_nonneg a), ?_⟩
  apply (div_le_div_iff₀ (pow_pos ha0 2) hN).2
  have hp := mul_le_mul_of_nonneg_right hc hN.le
  nlinarith only [hp, hsq]

private lemma approximation_aux {x H N u v m m' k : ℚ}
    (hH0 : 0 ≤ H) (hN : 0 < N)
    (hu : N ≤ u) (huv : u ≤ v) (hv : v ≤ 2 * N)
    (hm : x ≤ m * u ^ 2 ∧ m * u ^ 2 ≤ x + H)
    (hm' : x ≤ m' * v ^ 2 ∧ m' * v ^ 2 ≤ x + H)
    (hid : k * u ^ 2 * v ^ 2 =
      x * (v - u) ^ 3 + (m' * v ^ 2 - x) * u ^ 2 * (3 * v - u) -
        (m * u ^ 2 - x) * v ^ 2 * (3 * u - v)) :
    |k - x * (v - u) ^ 3 / (u ^ 2 * v ^ 2)| ≤ 5 * H / N := by
  have hu0 : 0 < u := hN.trans_le hu
  have hv0 : 0 < v := hu0.trans_le huv
  obtain ⟨hA0, hA⟩ := coefficient_bounds hN (hu.trans huv)
    (show 0 ≤ 3 * v - u by linarith) (show 3 * v - u ≤ 5 * N by linarith)
  obtain ⟨hB0, hB⟩ := coefficient_bounds hN hu
    (show 0 ≤ 3 * u - v by linarith) (show 3 * u - v ≤ 5 * N by linarith)
  have he0 : 0 ≤ m * u ^ 2 - x := by linarith [hm.1]
  have he : m * u ^ 2 - x ≤ H := by linarith [hm.2]
  have he'0 : 0 ≤ m' * v ^ 2 - x := by linarith [hm'.1]
  have he' : m' * v ^ 2 - x ≤ H := by linarith [hm'.2]
  have hPA0 := mul_nonneg he'0 hA0
  have hPB0 := mul_nonneg he0 hB0
  have hPA := mul_le_mul he' hA hA0 hH0
  have hPB := mul_le_mul he hB hB0 hH0
  have hid' : k - x * (v - u) ^ 3 / (u ^ 2 * v ^ 2) =
      (m' * v ^ 2 - x) * ((3 * v - u) / v ^ 2) -
        (m * u ^ 2 - x) * ((3 * u - v) / u ^ 2) := by
    field_simp [hu0.ne', hv0.ne']
    linear_combination hid
  have heq : H * (5 / N) = 5 * H / N := by ring
  rw [heq] at hPA hPB
  rw [hid']
  apply abs_le.mpr
  constructor <;> linarith only [hPA0, hPB0, hPA, hPB]

/-- The error in the ideal pair label is at most `5 H / N`.
The smallness condition on `H` is not needed for this approximation. -/
lemma label_approx {x H N u v m m' : ℕ}
    (hN : 0 < N) (hu : N ≤ u) (huv : u ≤ v) (hv : v ≤ 2 * N)
    (hm : x < m * u ^ 2 ∧ m * u ^ 2 ≤ x + H)
    (hm' : x < m' * v ^ 2 ∧ m' * v ^ 2 ≤ x + H) :
    |(label u v m m' : ℚ) - ideal x u v| ≤ 5 * (H : ℚ) / N := by
  rw [ideal_of_le huv]
  apply approximation_aux (Nat.cast_nonneg H) (by exact_mod_cast hN)
    (by exact_mod_cast hu) (by exact_mod_cast huv) (by exact_mod_cast hv)
    (m := (m : ℚ)) (m' := (m' : ℚ))
    (by exact_mod_cast (show x ≤ m * u ^ 2 ∧ m * u ^ 2 ≤ x + H from ⟨hm.1.le, hm.2⟩))
    (by exact_mod_cast (show x ≤ m' * v ^ 2 ∧ m' * v ^ 2 ≤ x + H from ⟨hm'.1.le, hm'.2⟩))
  exact_mod_cast RothLocal.label_error_identity (x : ℤ) (u : ℤ) (v : ℤ)
    (m : ℤ) (m' : ℤ)

/-- If `K = x (v-u)³ / N⁴` and `g` is the ideal label, then `K/16 ≤ g ≤ K`. -/
lemma ideal_scale_bounds {x N u v : ℕ}
    (hN : 0 < N) (hu : N ≤ u) (huv : u ≤ v) (hv : v ≤ 2 * N) :
    scale x N (v - u) / 16 ≤ ideal x u v ∧
      ideal x u v ≤ scale x N (v - u) := by
  have hNq : (0 : ℚ) < N := by exact_mod_cast hN
  have huq : (N : ℚ) ≤ u := by exact_mod_cast hu
  have huvq : (u : ℚ) ≤ v := by exact_mod_cast huv
  have hvq : (v : ℚ) ≤ 2 * N := by exact_mod_cast hv
  have hu0 : (0 : ℚ) < u := hNq.trans_le huq
  have hv0 : (0 : ℚ) < v := hu0.trans_le huvq
  have hN2u2 : (N : ℚ) ^ 2 ≤ (u : ℚ) ^ 2 := pow_le_pow_left₀ hNq.le huq 2
  have hN2v2 : (N : ℚ) ^ 2 ≤ (v : ℚ) ^ 2 :=
    pow_le_pow_left₀ hNq.le (huq.trans huvq) 2
  have hu2 : (u : ℚ) ^ 2 ≤ (2 * (N : ℚ)) ^ 2 :=
    pow_le_pow_left₀ hu0.le (huvq.trans hvq) 2
  have hv2 : (v : ℚ) ^ 2 ≤ (2 * (N : ℚ)) ^ 2 :=
    pow_le_pow_left₀ hv0.le hvq 2
  have hdenlo : (N : ℚ) ^ 4 ≤ (u : ℚ) ^ 2 * (v : ℚ) ^ 2 := by
    nlinarith only [mul_le_mul hN2u2 hN2v2 (sq_nonneg (N : ℚ)) (sq_nonneg (u : ℚ))]
  have hdenhi : (u : ℚ) ^ 2 * (v : ℚ) ^ 2 ≤ 16 * (N : ℚ) ^ 4 := by
    nlinarith only [mul_le_mul hu2 hv2 (sq_nonneg (v : ℚ)) (sq_nonneg (2 * (N : ℚ)))]
  have hnum : (0 : ℚ) ≤ (x : ℚ) * (↑(v - u) : ℚ) ^ 3 := by positivity
  unfold scale ideal
  constructor
  · rw [div_div]
    exact div_le_div_of_nonneg_left hnum
      (mul_pos (pow_pos hu0 2) (pow_pos hv0 2)) (by nlinarith only [hdenhi])
  · exact div_le_div_of_nonneg_left hnum (pow_pos hNq 4) hdenlo

private lemma error_le_eighth {H N : ℕ} (hN : 0 < N) (hH : 256 * H ≤ N) :
    5 * (H : ℚ) / N ≤ 1 / 8 := by
  have hNq : (0 : ℚ) < N := by exact_mod_cast hN
  have hHq : 256 * (H : ℚ) ≤ N := by exact_mod_cast hH
  apply (div_le_iff₀ hNq).2
  linarith [show (0 : ℚ) ≤ H from Nat.cast_nonneg H]

/-- Every ordered pair in the dyadic band has a nonnegative integer label. -/
lemma label_nonneg {x H N u v m m' : ℕ}
    (hN : 0 < N) (hH : 256 * H ≤ N)
    (hu : N ≤ u) (huv : u ≤ v) (hv : v ≤ 2 * N)
    (hm : x < m * u ^ 2 ∧ m * u ^ 2 ≤ x + H)
    (hm' : x < m' * v ^ 2 ∧ m' * v ^ 2 ≤ x + H) :
    0 ≤ label u v m m' := by
  have he := (abs_le.mp (label_approx hN hu huv hv hm hm')).1
  have herr := error_le_eighth hN hH
  have hg := ideal_nonneg x u v
  by_contra hk
  have hk' : label u v m m' ≤ -1 := by omega
  have hkq : (label u v m m' : ℚ) ≤ -1 := by exact_mod_cast hk'
  linarith

/-- For a positive label `k`, the ideal label lies between `k/2` and `9k/8`. -/
lemma positive_label_ideal_bounds {x H N u v m m' : ℕ}
    (hN : 0 < N) (hH : 256 * H ≤ N)
    (hu : N ≤ u) (huv : u ≤ v) (hv : v ≤ 2 * N)
    (hm : x < m * u ^ 2 ∧ m * u ^ 2 ≤ x + H)
    (hm' : x < m' * v ^ 2 ∧ m' * v ^ 2 ≤ x + H)
    (hk : 0 < label u v m m') :
    (label u v m m' : ℚ) / 2 ≤ ideal x u v ∧
      ideal x u v ≤ (9 / 8 : ℚ) * (label u v m m' : ℚ) := by
  obtain ⟨helo, hehi⟩ := abs_le.mp (label_approx hN hu huv hv hm hm')
  have herr := error_le_eighth hN hH
  have hk' : 1 ≤ label u v m m' := by omega
  have hkq : (1 : ℚ) ≤ (label u v m m' : ℚ) := by exact_mod_cast hk'
  constructor <;> linarith

/-- Division-free integer bounds for a positive label, with constants `18` and `2`. -/
lemma positive_label_bounds {x H N u v m m' : ℕ}
    (hN : 0 < N) (hH : 256 * H ≤ N)
    (hu : N ≤ u) (huv : u ≤ v) (hv : v ≤ 2 * N)
    (hm : x < m * u ^ 2 ∧ m * u ^ 2 ≤ x + H)
    (hm' : x < m' * v ^ 2 ∧ m' * v ^ 2 ≤ x + H)
    (hk : 0 < label u v m m') :
    (x : ℤ) * (↑(v - u) : ℤ) ^ 3 ≤ 18 * label u v m m' * (N : ℤ) ^ 4 ∧
      label u v m m' * (N : ℤ) ^ 4 ≤ 2 * (x : ℤ) * (↑(v - u) : ℤ) ^ 3 := by
  obtain ⟨hgl, hgu⟩ := positive_label_ideal_bounds hN hH hu huv hv hm hm' hk
  obtain ⟨hKl, hKu⟩ := ideal_scale_bounds (x := x) hN hu huv hv
  have hNq : (0 : ℚ) < N := by exact_mod_cast hN
  have hKup : scale x N (v - u) ≤ 18 * (label u v m m' : ℚ) := by linarith
  have hKlo : (label u v m m' : ℚ) ≤ 2 * scale x N (v - u) := by linarith
  have hupper : (x : ℚ) * (↑(v - u) : ℚ) ^ 3 ≤
      18 * (label u v m m' : ℚ) * (N : ℚ) ^ 4 :=
    (div_le_iff₀ (pow_pos hNq 4)).mp hKup
  have hlower : (label u v m m' : ℚ) * (N : ℚ) ^ 4 ≤
      2 * (x : ℚ) * (↑(v - u) : ℚ) ^ 3 := by
    have hp := mul_le_mul_of_nonneg_right hKlo (pow_nonneg hNq.le 4)
    dsimp [scale] at hp
    field_simp [hNq.ne'] at hp
    nlinarith only [hp]
  exact ⟨by exact_mod_cast hupper, by exact_mod_cast hlower⟩

/-- A positive label forces the natural cubic gap inequality needed in counting. -/
lemma positive_label_gap {x H N u v m m' : ℕ}
    (hN : 0 < N) (hH : 256 * H ≤ N)
    (hu : N ≤ u) (huv : u ≤ v) (hv : v ≤ 2 * N)
    (hm : x < m * u ^ 2 ∧ m * u ^ 2 ≤ x + H)
    (hm' : x < m' * v ^ 2 ∧ m' * v ^ 2 ≤ x + H)
    (hk : 0 < label u v m m') :
    N ^ 4 ≤ 2 * x * (v - u) ^ 3 := by
  have hb := (positive_label_bounds hN hH hu huv hv hm hm' hk).2
  have hk1 : 1 ≤ label u v m m' := by omega
  have hN4 : (N : ℤ) ^ 4 ≤ label u v m m' * (N : ℤ) ^ 4 := by
    simpa using mul_le_mul_of_nonneg_right hk1 (show 0 ≤ (N : ℤ) ^ 4 by positivity)
  exact_mod_cast hN4.trans hb

/-- A zero label forces `x (v-u)³ ≤ 20 H N³`.
This follows directly from the exact label identity, without a smallness
condition on `H`. -/
lemma zero_label_bound {x H N u v m m' : ℕ}
    (hN : 0 < N) (hu : N ≤ u) (huv : u ≤ v) (hv : v ≤ 2 * N)
    (hm : x < m * u ^ 2 ∧ m * u ^ 2 ≤ x + H)
    (hm' : x < m' * v ^ 2 ∧ m' * v ^ 2 ≤ x + H)
    (hk : label u v m m' = 0) :
    x * (v - u) ^ 3 ≤ 20 * H * N ^ 3 := by
  have hNq : (0 : ℤ) < N := by exact_mod_cast hN
  have huq : (N : ℤ) ≤ u := by exact_mod_cast hu
  have huvq : (u : ℤ) ≤ v := by exact_mod_cast huv
  have hvq : (v : ℤ) ≤ 2 * N := by exact_mod_cast hv
  have hmq : (x : ℤ) < (m : ℤ) * (u : ℤ) ^ 2 ∧
      (m : ℤ) * (u : ℤ) ^ 2 ≤ (x : ℤ) + H := by exact_mod_cast hm
  have hm'q : (x : ℤ) < (m' : ℤ) * (v : ℤ) ^ 2 ∧
      (m' : ℤ) * (v : ℤ) ^ 2 ≤ (x : ℤ) + H := by exact_mod_cast hm'
  have hH0 : (0 : ℤ) ≤ H := Nat.cast_nonneg H
  have hu0 : (0 : ℤ) < u := hNq.trans_le huq
  have hb0 : (0 : ℤ) ≤ (v : ℤ) - u := sub_nonneg.mpr huvq
  have hc0 : (0 : ℤ) ≤ 3 * (v : ℤ) - u := by linarith
  have hc : 3 * (v : ℤ) - u ≤ 5 * N := by linarith
  have hdelta : -(H : ℤ) ≤ (m' : ℤ) * (v : ℤ) ^ 2 - (m : ℤ) * (u : ℤ) ^ 2 := by
    linarith [hmq.2, hm'q.1]
  have hid := RothLocal.label_identity (u : ℤ) (v : ℤ) (m : ℤ) (m' : ℤ)
  change label u v m m' * _ = _ at hid
  rw [hk, zero_mul] at hid
  have hmb : (m : ℤ) * ((v : ℤ) - u) ^ 3 ≤ 5 * (H : ℤ) * N := by
    have hp := mul_le_mul_of_nonneg_left hdelta hc0
    have hq := mul_le_mul_of_nonneg_right hc hH0
    nlinarith only [hid, hp, hq]
  have hu2 : (u : ℤ) ^ 2 ≤ 4 * (N : ℤ) ^ 2 := by
    have hp := pow_le_pow_left₀ hu0.le (huvq.trans hvq) 2
    nlinarith only [hp]
  have hxb := mul_le_mul_of_nonneg_right hmq.1.le (pow_nonneg hb0 3)
  have hmbu := mul_le_mul_of_nonneg_right hmb (sq_nonneg (u : ℤ))
  have hupper := mul_le_mul_of_nonneg_left hu2
    (show (0 : ℤ) ≤ 5 * (H : ℤ) * N by positivity)
  have hfinal : (x : ℤ) * ((v : ℤ) - u) ^ 3 ≤ 20 * (H : ℤ) * (N : ℤ) ^ 3 := by
    nlinarith only [hxb, hmbu, hupper]
  rw [← Nat.cast_sub huv] at hfinal
  exact_mod_cast hfinal

/-- Natural-valued version of the positive-label bounds; no integer subtraction
or division appears in the conclusion. -/
lemma positive_label_bounds_nat {x H N u v m m' : ℕ}
    (hN : 0 < N) (hH : 256 * H ≤ N)
    (hu : N ≤ u) (huv : u ≤ v) (hv : v ≤ 2 * N)
    (hm : x < m * u ^ 2 ∧ m * u ^ 2 ≤ x + H)
    (hm' : x < m' * v ^ 2 ∧ m' * v ^ 2 ≤ x + H)
    (hk : 0 < label u v m m') :
    x * (v - u) ^ 3 ≤ 18 * (label u v m m').toNat * N ^ 4 ∧
      (label u v m m').toNat * N ^ 4 ≤ 2 * x * (v - u) ^ 3 := by
  have h := positive_label_bounds hN hH hu huv hv hm hm' hk
  have heq : ((label u v m m').toNat : ℤ) = label u v m m' :=
    Int.toNat_of_nonneg hk.le
  rw [← heq] at h
  exact_mod_cast h

/-- Turning a division-free cubic bound into a bound for the rational scale. -/
lemma scale_le_of_cube_bound {x H N b C : ℕ} (hN : 0 < N)
    (hsmall : x * b ^ 3 ≤ C * H * N ^ 3) :
    scale x N b ≤ (C : ℚ) * H / N := by
  have hNq : (0 : ℚ) < N := by exact_mod_cast hN
  have hq : (x : ℚ) * (b : ℚ) ^ 3 ≤ (C : ℚ) * H * (N : ℚ) ^ 3 := by
    exact_mod_cast hsmall
  unfold scale
  apply (div_le_div_iff₀ (pow_pos hNq 4) hNq).2
  calc
    (x : ℚ) * (b : ℚ) ^ 3 * N ≤ ((C : ℚ) * H * (N : ℚ) ^ 3) * N :=
      mul_le_mul_of_nonneg_right hq hNq.le
    _ = ((C : ℚ) * H) * (N : ℚ) ^ 4 := by ring

/-- A cubic gap of size at most `160 H N³` forces the integer label to vanish:
its rational upper bound is `165 H / N < 1`. -/
lemma label_eq_zero_of_small_cube {x H N u v m m' : ℕ}
    (hN : 0 < N) (hH : 256 * H ≤ N)
    (hu : N ≤ u) (huv : u ≤ v) (hv : v ≤ 2 * N)
    (hm : x < m * u ^ 2 ∧ m * u ^ 2 ≤ x + H)
    (hm' : x < m' * v ^ 2 ∧ m' * v ^ 2 ≤ x + H)
    (hsmall : x * (v - u) ^ 3 ≤ 160 * H * N ^ 3) :
    label u v m m' = 0 := by
  have hk0 := label_nonneg hN hH hu huv hv hm hm'
  have he := (abs_le.mp (label_approx hN hu huv hv hm hm')).2
  have hg := (ideal_scale_bounds (x := x) hN hu huv hv).2
  have hs : scale x N (v - u) ≤ 160 * (H : ℚ) / N := by
    simpa only [Nat.cast_ofNat] using scale_le_of_cube_bound hN hsmall
  have hkupper : (label u v m m' : ℚ) ≤ 165 * (H : ℚ) / N := by
    calc
      (label u v m m' : ℚ) ≤ ideal x u v + 5 * (H : ℚ) / N := by linarith only [he]
      _ ≤ 160 * (H : ℚ) / N + 5 * (H : ℚ) / N :=
        add_le_add (hg.trans hs) le_rfl
      _ = 165 * (H : ℚ) / N := by ring
  have hNq : (0 : ℚ) < N := by exact_mod_cast hN
  have hHq : 256 * (H : ℚ) ≤ N := by exact_mod_cast hH
  have hlt : 165 * (H : ℚ) / N < 1 := by
    apply (div_lt_iff₀ hNq).2
    have hH0 : (0 : ℚ) ≤ H := Nat.cast_nonneg H
    nlinarith only [hHq, hNq, hH0]
  have hklt : label u v m m' < 1 := by exact_mod_cast hkupper.trans_lt hlt
  omega

/-- The elementary cubic inequality used to join two adjacent gaps. -/
lemma cube_add_le_four (a b : ℕ) : (a + b) ^ 3 ≤ 4 * (a ^ 3 + b ^ 3) := by
  have hpos : (0 : ℤ) ≤ 3 * ((a : ℤ) + b) * ((a : ℤ) - b) ^ 2 := by positivity
  have h : ((a : ℤ) + b) ^ 3 ≤ 4 * ((a : ℤ) ^ 3 + (b : ℤ) ^ 3) := by
    nlinarith only [hpos]
  exact_mod_cast h

/-- Three ordered hits in the dyadic band cannot have both adjacent labels zero.
The two `20 H N³` bounds combine to `160 H N³` for the outer gap, forcing
its label to vanish too, contrary to `RothLocal.no_three_zero_labels`. -/
theorem no_two_adjacent_zero_labels {x H N u v w m₁ m₂ m₃ : ℕ}
    (hN : 0 < N) (hH : 256 * H ≤ N)
    (hu : N ≤ u) (huv : u < v) (hvw : v < w) (hw : w ≤ 2 * N)
    (hm₁ : x < m₁ * u ^ 2 ∧ m₁ * u ^ 2 ≤ x + H)
    (hm₂ : x < m₂ * v ^ 2 ∧ m₂ * v ^ 2 ≤ x + H)
    (hm₃ : x < m₃ * w ^ 2 ∧ m₃ * w ^ 2 ≤ x + H)
    (huv0 : label u v m₁ m₂ = 0) (hvw0 : label v w m₂ m₃ = 0) : False := by
  have hv : v ≤ 2 * N := hvw.le.trans hw
  have hvN : N ≤ v := hu.trans huv.le
  have h₁ := zero_label_bound hN hu huv.le hv hm₁ hm₂ huv0
  have h₂ := zero_label_bound hN hvN hvw.le hw hm₂ hm₃ hvw0
  have hsum : w - u = (v - u) + (w - v) := by omega
  have hc := mul_le_mul_of_nonneg_left (cube_add_le_four (v - u) (w - v)) (Nat.zero_le x)
  have hsmall : x * (w - u) ^ 3 ≤ 160 * H * N ^ 3 := by
    rw [hsum]
    nlinarith only [hc, h₁, h₂]
  have huw0 := label_eq_zero_of_small_cube hN hH hu (huv.trans hvw).le hw hm₁ hm₃ hsmall
  have hm₁0 : (m₁ : ℤ) ≠ 0 := by
    have hn : m₁ ≠ 0 := by
      intro hz
      simp [hz] at hm₁
    exact_mod_cast hn
  exact RothLocal.no_three_zero_labels (u := u) (v := v) (w := w)
    (m₁ := m₁) (m₂ := m₂) (m₃ := m₃)
    (by exact_mod_cast (ne_of_lt huv)) (by exact_mod_cast (ne_of_lt (huv.trans hvw)))
    (by exact_mod_cast (ne_of_lt hvw)) hm₁0 huv0 hvw0 huw0

private lemma ratio_lower_aux {N u v b : ℚ}
    (hN : 0 < N) (hu : N ≤ u) (huv : u ≤ v)
    (hb : 0 ≤ b) (hvb : v + b ≤ 2 * N) :
    1 + 2 * (v - u) / N ≤
      (1 + (v - u) / u) ^ 2 * (1 + (v - u) / (u + b)) ^ 2 := by
  have hu0 : 0 < u := hN.trans_le hu
  have hub0 : 0 < u + b := by linarith
  have hd0 : 0 ≤ v - u := sub_nonneg.mpr huv
  have ha0 : 0 ≤ (v - u) / u := div_nonneg hd0 hu0.le
  have hc0 : 0 ≤ (v - u) / (u + b) := div_nonneg hd0 hub0.le
  have ha : (v - u) / (2 * N) ≤ (v - u) / u :=
    div_le_div_of_nonneg_left hd0 hu0 (by linarith)
  have hc : (v - u) / (2 * N) ≤ (v - u) / (u + b) :=
    div_le_div_of_nonneg_left hd0 hub0 (by linarith)
  have htwice : 2 * ((v - u) / (2 * N)) = (v - u) / N := by ring
  have h₁ : 1 + 2 * ((v - u) / u) ≤ (1 + (v - u) / u) ^ 2 := by
    nlinarith only [sq_nonneg ((v - u) / u)]
  have h₂ : 1 + 2 * ((v - u) / (u + b)) ≤ (1 + (v - u) / (u + b)) ^ 2 := by
    nlinarith only [sq_nonneg ((v - u) / (u + b))]
  have hp := mul_le_mul h₁ h₂ (by linarith : 0 ≤ 1 + 2 * ((v - u) / (u + b)))
    (sq_nonneg (1 + (v - u) / u))
  have hprod := mul_nonneg ha0 hc0
  have ht : 2 * (v - u) / N = 2 * ((v - u) / N) := by ring
  rw [ht]
  nlinarith only [ha, hc, htwice, hp, hprod]

private lemma same_gap_separation_aux {x N u v b : ℚ}
    (hx : 0 ≤ x) (hN : 0 < N) (hu : N ≤ u) (huv : u ≤ v)
    (hb : 0 ≤ b) (hvb : v + b ≤ 2 * N) :
    (2 * (v - u) / N) * (x * b ^ 3 / (v ^ 2 * (v + b) ^ 2)) ≤
      x * b ^ 3 / (u ^ 2 * (u + b) ^ 2) - x * b ^ 3 / (v ^ 2 * (v + b) ^ 2) := by
  have hu0 : 0 < u := hN.trans_le hu
  have hv0 : 0 < v := hu0.trans_le huv
  have hub0 : 0 < u + b := by linarith
  have hvb0 : 0 < v + b := by linarith
  have hid : x * b ^ 3 / (u ^ 2 * (u + b) ^ 2) =
      (x * b ^ 3 / (v ^ 2 * (v + b) ^ 2)) *
        ((1 + (v - u) / u) ^ 2 * (1 + (v - u) / (u + b)) ^ 2) := by
    field_simp [hu0.ne', hv0.ne', hub0.ne', hvb0.ne']
    ring
  have hg0 : 0 ≤ x * b ^ 3 / (v ^ 2 * (v + b) ^ 2) := by positivity
  have hp := mul_le_mul_of_nonneg_left (ratio_lower_aux hN hu huv hb hvb) hg0
  rw [← hid] at hp
  nlinarith only [hp]

/-- Separation of ideal labels for pairs of the same gap, proved algebraically.
No hits or small-interval hypothesis are needed. -/
lemma same_gap_ideal_separation {x N u v b : ℕ}
    (hN : 0 < N) (hu : N ≤ u) (huv : u ≤ v) (hvb : v + b ≤ 2 * N) :
    (2 * (↑(v - u) : ℚ) / N) * ideal x v (v + b) ≤
      ideal x u (u + b) - ideal x v (v + b) := by
  rw [ideal_add, ideal_add, Nat.cast_sub huv]
  exact same_gap_separation_aux (Nat.cast_nonneg x) (by exact_mod_cast hN)
    (by exact_mod_cast hu) (by exact_mod_cast huv) (Nat.cast_nonneg b) (by exact_mod_cast hvb)

/-- Equal positive labels on two pairs of the same gap have diameter at most
`10 H / k`. The endpoint assumptions imply that all four bases lie in `[N, 2N]`.
Neither strict ordering of the starts nor positivity of the gap is needed. -/
theorem same_positive_label_diameter {x H N u v b m₁ m₁' m₂ m₂' : ℕ} {k : ℤ}
    (hN : 0 < N) (hH : 256 * H ≤ N)
    (hu : N ≤ u) (huv : u ≤ v) (hvb : v + b ≤ 2 * N)
    (hm₁ : x < m₁ * u ^ 2 ∧ m₁ * u ^ 2 ≤ x + H)
    (hm₁' : x < m₁' * (u + b) ^ 2 ∧ m₁' * (u + b) ^ 2 ≤ x + H)
    (hm₂ : x < m₂ * v ^ 2 ∧ m₂ * v ^ 2 ≤ x + H)
    (hm₂' : x < m₂' * (v + b) ^ 2 ∧ m₂' * (v + b) ^ 2 ≤ x + H)
    (hk₁ : label u (u + b) m₁ m₁' = k) (hk₂ : label v (v + b) m₂ m₂' = k)
    (hk : 0 < k) :
    k * (↑(v - u) : ℤ) ≤ 10 * (H : ℤ) := by
  have hub : u + b ≤ 2 * N := by omega
  have hvN : N ≤ v := hu.trans huv
  have he₁ := abs_le.mp (label_approx hN hu (Nat.le_add_right u b) hub hm₁ hm₁')
  have he₂ := abs_le.mp (label_approx hN hvN (Nat.le_add_right v b) hvb hm₂ hm₂')
  rw [hk₁] at he₁
  rw [hk₂] at he₂
  have hg₂ := (positive_label_ideal_bounds hN hH hvN (Nat.le_add_right v b) hvb
    hm₂ hm₂' (by simpa only [hk₂] using hk)).1
  rw [hk₂] at hg₂
  have hsep := same_gap_ideal_separation (x := x) hN hu huv hvb
  have hNq : (0 : ℚ) < N := by exact_mod_cast hN
  have hmul := mul_le_mul_of_nonneg_left hg₂
    (show (0 : ℚ) ≤ 2 * (↑(v - u) : ℚ) / N by positivity)
  have hid : (2 * (↑(v - u) : ℚ) / N) * ((k : ℚ) / 2) =
      (k : ℚ) * (↑(v - u) : ℚ) / N := by ring
  rw [hid] at hmul
  have hq : (k : ℚ) * (↑(v - u) : ℚ) / N ≤ 10 * (H : ℚ) / N := by
    calc
      (k : ℚ) * (↑(v - u) : ℚ) / N ≤
          (2 * (↑(v - u) : ℚ) / N) * ideal x v (v + b) := hmul
      _ ≤ ideal x u (u + b) - ideal x v (v + b) := hsep
      _ ≤ 5 * (H : ℚ) / N + 5 * (H : ℚ) / N := by linarith [he₁.1, he₂.2]
      _ = 10 * (H : ℚ) / N := by ring
  have hq' : (k : ℚ) * (↑(v - u) : ℚ) ≤ 10 * (H : ℚ) :=
    (mul_le_mul_iff_left₀ hNq).mp ((div_le_div_iff₀ hNq hNq).mp hq)
  exact_mod_cast hq'

/-- Natural-label version of `same_positive_label_diameter`, suitable for finite
counting with a prescribed positive natural label. -/
theorem same_positive_label_diameter_nat {x H N u v b m₁ m₁' m₂ m₂' k : ℕ}
    (hN : 0 < N) (hH : 256 * H ≤ N)
    (hu : N ≤ u) (huv : u ≤ v) (hvb : v + b ≤ 2 * N)
    (hm₁ : x < m₁ * u ^ 2 ∧ m₁ * u ^ 2 ≤ x + H)
    (hm₁' : x < m₁' * (u + b) ^ 2 ∧ m₁' * (u + b) ^ 2 ≤ x + H)
    (hm₂ : x < m₂ * v ^ 2 ∧ m₂ * v ^ 2 ≤ x + H)
    (hm₂' : x < m₂' * (v + b) ^ 2 ∧ m₂' * (v + b) ^ 2 ≤ x + H)
    (hk₁ : label u (u + b) m₁ m₁' = (k : ℤ))
    (hk₂ : label v (v + b) m₂ m₂' = (k : ℤ)) (hk : 0 < k) :
    k * (v - u) ≤ 10 * H := by
  exact_mod_cast same_positive_label_diameter hN hH hu huv hvb hm₁ hm₁' hm₂ hm₂'
    hk₁ hk₂ (by exact_mod_cast hk)

end RothQuant
