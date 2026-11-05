import Mathlib
import Submission.PrimeNormalization

/-! Elementary Chebyshev estimates with explicit symbolic constants, and the
negligibility of the fixed-cutoff smooth-number contribution. -/

open Filter
open scoped BigOperators Topology

namespace Erdos5EfficientCover

/-- Inclusive finite prime set. -/
def primesUpTo (y : ℕ) : Finset ℕ := Nat.primesBelow (y + 1)

@[simp] theorem mem_primesUpTo {p y : ℕ} :
    p ∈ primesUpTo y ↔ p.Prime ∧ p ≤ y := by
  simp [primesUpTo, Nat.mem_primesBelow, and_comm]

@[simp] theorem card_primesUpTo (y : ℕ) :
    (primesUpTo y).card = Nat.primeCounting y :=
  Nat.primesBelow_card_eq_primeCounting' (y + 1)

/-- Primes in the upper, reserved portion of the inclusive prime set. -/
def reservePrimes (y T : ℕ) : Finset ℕ := primesUpTo y \ primesUpTo (y / T)

@[simp] theorem mem_reservePrimes {p y T : ℕ} :
    p ∈ reservePrimes y T ↔ p.Prime ∧ p ≤ y ∧ y / T < p := by
  simp only [reservePrimes, Finset.mem_sdiff, mem_primesUpTo]
  constructor
  · rintro ⟨⟨hpp, hpy⟩, hn⟩
    exact ⟨hpp, hpy, lt_of_not_ge (fun h => hn ⟨hpp, h⟩)⟩
  · rintro ⟨hpp, hpy, hdp⟩
    exact ⟨⟨hpp, hpy⟩, fun h => (not_le_of_gt hdp) h.2⟩

theorem card_reservePrimes_real (y T : ℕ) :
    ((reservePrimes y T).card : ℝ) =
      (Nat.primeCounting y : ℝ) - (Nat.primeCounting (y / T) : ℝ) := by
  have hsub : primesUpTo (y / T) ⊆ primesUpTo y := by
    intro p hp
    exact mem_primesUpTo.mpr ⟨(mem_primesUpTo.mp hp).1,
      (mem_primesUpTo.mp hp).2.trans (Nat.div_le_self y T)⟩
  rw [reservePrimes, Finset.card_sdiff_of_subset hsub, card_primesUpTo, card_primesUpTo,
    Nat.cast_sub (Nat.monotone_primeCounting (Nat.div_le_self y T))]

/-- The available elementary lower-bound constant. -/
noncomputable def lowerConst : ℝ := Real.log 2 / 3

/-- A convenient upper-bound constant: the Chebyshev upper bound with `ε=1`. -/
noncomputable def upperConst : ℝ := Real.log 4 + 1

theorem lowerConst_pos : 0 < lowerConst :=
  div_pos (Real.log_pos (by norm_num)) (by norm_num)

theorem upperConst_pos : 0 < upperConst := by
  unfold upperConst
  have := Real.log_pos (by norm_num : (1 : ℝ) < 4)
  linarith

/-- Natural-number form of the imported kernel-proved Chebyshev upper estimate. -/
theorem eventually_primeCounting_upper :
    ∀ᶠ x : ℕ in atTop,
      (Nat.primeCounting x : ℝ) ≤ upperConst * x / Real.log (x : ℝ) := by
  have h := (tendsto_natCast_atTop_atTop : Tendsto (fun x : ℕ => (x : ℝ)) atTop atTop).eventually
    (Chebyshev.eventually_primeCounting_le (ε := 1) (by norm_num))
  simpa only [Nat.floor_natCast, upperConst] using h

/-- A fixed reserve scale exists without any numerical approximation of logarithms. -/
theorem exists_reserve_scale :
    ∃ T : ℕ, 0 < T ∧ 4 * upperConst ≤ lowerConst * (T : ℝ) := by
  obtain ⟨T, hT⟩ := exists_nat_gt (max 1 (8 * upperConst / lowerConst))
  have hT1 : (1 : ℝ) < T := (le_max_left _ _).trans_lt hT
  have hTpos : 0 < T := by exact_mod_cast (lt_trans (by norm_num : (0 : ℝ) < 1) hT1)
  have h8 : 8 * upperConst < (T : ℝ) * lowerConst :=
    (div_lt_iff₀ lowerConst_pos).mp ((le_max_right _ _).trans_lt hT)
  exact ⟨T, hTpos, by nlinarith [upperConst_pos]⟩

/-- At least `α*y/log y` primes remain in reserve, with `α = (log 2)/6`. -/
theorem eventually_reserve_lower (T : ℕ) (hT : 0 < T)
    (hscale : 4 * upperConst ≤ lowerConst * (T : ℝ)) :
    ∀ᶠ y : ℕ in atTop,
      (lowerConst / 2) * y / Real.log (y : ℝ) ≤ ((reservePrimes y T).card : ℝ) := by
  have hupper := (Nat.tendsto_div_const_atTop hT.ne').eventually eventually_primeCounting_upper
  filter_upwards [hupper, eventually_ge_atTop (2 : ℕ),
    eventually_ge_atTop ((2 * T) * T)] with y hupper hy2 hylarge
  let d := y / T
  have hdlarge : 2 * T ≤ d := (Nat.le_div_iff_mul_le hT).mpr hylarge
  have hd2 : 2 ≤ d := by omega
  have hylt : y < (d + 1) * T :=
    (Nat.div_lt_iff_lt_mul hT).mp (Nat.lt_succ_self d)
  have hysq : y ≤ d ^ 2 := by nlinarith
  have hypos : (0 : ℝ) < y := by exact_mod_cast (show 0 < y by omega)
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hlogy : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hlogd : 0 < Real.log (d : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < d by omega))
  have hlogs : Real.log (y : ℝ) ≤ 2 * Real.log (d : ℝ) := by
    have h := Real.log_le_log hypos (by exact_mod_cast hysq : (y : ℝ) ≤ (d : ℝ) ^ 2)
    simpa only [Real.log_pow, Nat.cast_ofNat] using h
  have hu : (Nat.primeCounting d : ℝ) * Real.log (d : ℝ) ≤ upperConst * d :=
    (le_div_iff₀ hlogd).mp hupper
  have hlogs' := mul_le_mul_of_nonneg_left hlogs
    (show (0 : ℝ) ≤ Nat.primeCounting d by positivity)
  have hu2 : (Nat.primeCounting d : ℝ) * Real.log (y : ℝ) ≤ 2 * upperConst * d := by
    nlinarith [hu, hlogs']
  have hdy : (T : ℝ) * d ≤ y := by exact_mod_cast Nat.mul_div_le y T
  have h4 := mul_le_mul_of_nonneg_right hscale (show (0 : ℝ) ≤ d by positivity)
  have hA := mul_le_mul_of_nonneg_left hdy lowerConst_pos.le
  have hhalf : 2 * upperConst * d ≤ (lowerConst / 2) * y := by nlinarith [h4, hA]
  have hdcount : (Nat.primeCounting d : ℝ) ≤ (lowerConst / 2) * y / Real.log (y : ℝ) :=
    (le_div_iff₀ hlogy).mpr (hu2.trans hhalf)
  have hlow := Erdos5PrimeNormalization.weak_chebyshev_lower_div y hy2
  change lowerConst * (y : ℝ) / Real.log (y : ℝ) ≤ (Nat.primeCounting y : ℝ) at hlow
  rw [card_reservePrimes_real]
  change (lowerConst / 2) * (y : ℝ) / Real.log (y : ℝ) ≤
    (Nat.primeCounting y : ℝ) - (Nat.primeCounting d : ℝ)
  have hid : lowerConst * (y : ℝ) / Real.log (y : ℝ) =
      2 * ((lowerConst / 2) * (y : ℝ) / Real.log (y : ℝ)) := by ring
  rw [hid] at hlow
  linarith

/-- For fixed positive `c`, the prime count at `c*y` is at most `B*c*y/log y`. -/
theorem eventually_primeCounting_mul_upper (c : ℕ) (hc : 1 ≤ c) :
    ∀ᶠ y : ℕ in atTop,
      (Nat.primeCounting (c * y) : ℝ) ≤ upperConst * c * y / Real.log (y : ℝ) := by
  have hcy : ∀ y : ℕ, y ≤ c * y := fun y => by nlinarith
  have htend : Tendsto (fun y : ℕ => c * y) atTop atTop :=
    tendsto_atTop_mono hcy tendsto_id
  filter_upwards [htend.eventually eventually_primeCounting_upper,
    eventually_ge_atTop (2 : ℕ)] with y hcount hy2
  have hypos : (0 : ℝ) < y := by exact_mod_cast (show 0 < y by omega)
  have hlogy : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hlogs : Real.log (y : ℝ) ≤ Real.log (c * y : ℕ) :=
    Real.log_le_log hypos (by exact_mod_cast hcy y)
  calc
    (Nat.primeCounting (c * y) : ℝ) ≤ upperConst * (c * y : ℕ) / Real.log (c * y : ℕ) := hcount
    _ ≤ upperConst * (c * y : ℕ) / Real.log (y : ℝ) :=
      div_le_div_of_nonneg_left (mul_nonneg upperConst_pos.le (Nat.cast_nonneg _)) hlogy hlogs
    _ = upperConst * c * y / Real.log (y : ℝ) := by push_cast; ring

/-- A natural square root is at most the corresponding real square root. -/
theorem nat_sqrt_le_real (m : ℕ) : (Nat.sqrt m : ℝ) ≤ Real.sqrt (m : ℝ) := by
  apply (Real.le_sqrt (by positivity) (by positivity)).mpr
  exact_mod_cast Nat.sqrt_le' m

/-- A useful uniform majorant for the smooth-number square root when `c≥1`. -/
theorem nat_sqrt_mul_le (c y : ℕ) (hc : 1 ≤ c) :
    (Nat.sqrt (c * y) : ℝ) ≤ (c : ℝ) * Real.sqrt (y : ℝ) := by
  have hc1 : (1 : ℝ) ≤ c := by exact_mod_cast hc
  have hc2 : (c : ℝ) ≤ (c : ℝ) ^ 2 := by nlinarith
  have hsq : (Nat.sqrt (c * y) : ℝ) ^ 2 ≤ ((c : ℝ) * Real.sqrt (y : ℝ)) ^ 2 := by
    calc
      (Nat.sqrt (c * y) : ℝ) ^ 2 ≤ (c : ℝ) * y := by exact_mod_cast Nat.sqrt_le' (c * y)
      _ ≤ (c : ℝ) ^ 2 * y := mul_le_mul_of_nonneg_right hc2 (Nat.cast_nonneg y)
      _ = ((c : ℝ) * Real.sqrt (y : ℝ)) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg y)]
  exact (sq_le_sq₀ (by positivity) (by positivity)).mp hsq

/-- Any fixed multiple of `sqrt(c*y)` is eventually at most `y/log y`. -/
theorem eventually_sqrt_term_le (c D : ℕ) (hc : 1 ≤ c) :
    ∀ᶠ y : ℕ in atTop,
      (D : ℝ) * (Nat.sqrt (c * y) : ℝ) ≤ (y : ℝ) / Real.log (y : ℝ) := by
  have hratio : Tendsto (fun y : ℕ => Real.log (y : ℝ) / Real.sqrt (y : ℝ)) atTop (𝓝 0) := by
    simpa only [Real.sqrt_eq_rpow] using
      (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero.comp
        (tendsto_natCast_atTop_atTop : Tendsto (fun y : ℕ => (y : ℝ)) atTop atTop)
  have hsmall : Tendsto (fun y : ℕ =>
      (D : ℝ) * (c : ℝ) * (Real.log (y : ℝ) / Real.sqrt (y : ℝ))) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hratio
  filter_upwards [hsmall.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    eventually_ge_atTop (2 : ℕ)] with y hsmall hy2
  have hypos : (0 : ℝ) < y := by exact_mod_cast (show 0 < y by omega)
  have hlogy : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hsqrt : 0 < Real.sqrt (y : ℝ) := Real.sqrt_pos.mpr hypos
  have hb : (D : ℝ) * (c : ℝ) * Real.log (y : ℝ) ≤ Real.sqrt (y : ℝ) := by
    apply (div_le_one hsqrt).mp
    simpa only [mul_div_assoc] using hsmall.le
  apply (le_div_iff₀ hlogy).mpr
  calc
    (D : ℝ) * (Nat.sqrt (c * y) : ℝ) * Real.log (y : ℝ) ≤
        (D : ℝ) * ((c : ℝ) * Real.sqrt (y : ℝ)) * Real.log (y : ℝ) := by
      gcongr
      exact nat_sqrt_mul_le c y hc
    _ = ((D : ℝ) * (c : ℝ) * Real.log (y : ℝ)) * Real.sqrt (y : ℝ) := by ring
    _ ≤ Real.sqrt (y : ℝ) * Real.sqrt (y : ℝ) :=
      mul_le_mul_of_nonneg_right hb hsqrt.le
    _ = (y : ℝ) := Real.mul_self_sqrt hypos.le

end Erdos5EfficientCover

#print axioms Erdos5EfficientCover.exists_reserve_scale
#print axioms Erdos5EfficientCover.eventually_reserve_lower
#print axioms Erdos5EfficientCover.eventually_primeCounting_mul_upper
#print axioms Erdos5EfficientCover.eventually_sqrt_term_le
