import Submission.AmplificationBarrier
import Submission.PrimorialSquareSieve

/-!
A stronger obstruction to fixed-power density amplification. This is auxiliary
work and does not prove or disprove Erdős 773.
-/
namespace Erdos773.Amplification
open Filter Finset
open scoped Topology
set_option maxHeartbeats 1000000

lemma geometric_upper_of_affine_recurrence (g : ℕ → ℝ) (θ C t D : ℝ)
    (hθ : 0 ≤ θ) (ht : 1 ≤ t) (_hD : 0 ≤ D)
    (hbase : g 0 ≤ D) (hgap : C ≤ D * (t - θ))
    (hgap0 : 0 ≤ D * (t - θ))
    (hrec : ∀ m, g (m + 1) ≤ θ * g m + C) :
    ∀ m, g m ≤ D * t ^ m := by
  intro m
  induction m with
  | zero => simpa using hbase
  | succ m ih =>
    have hp : 1 ≤ t ^ m := one_le_pow₀ ht
    have hc : C ≤ D * (t - θ) * t ^ m :=
      hgap.trans (le_mul_of_one_le_right hgap0 hp)
    calc
      g (m + 1) ≤ θ * g m + C := hrec m
      _ ≤ θ * (D * t ^ m) + D * (t - θ) * t ^ m :=
        add_le_add (mul_le_mul_of_nonneg_left ih hθ) hc
      _ = D * t ^ (m + 1) := by rw [pow_succ]; ring

lemma no_subquadratic_log_recurrence (g : ℕ → ℝ) (A L : ℝ) (hA : 0 < A)
    (hlower : ∀ m : ℕ, 7 ≤ m → A * (2 : ℝ) ^ m ≤ m * (g m + L))
    (θ : ℝ) (hθ : 0 ≤ θ) (hθ2 : θ < 2) :
    ¬ ∃ C : ℝ, ∀ m : ℕ, g (m + 1) ≤ θ * g m + C := by
  rintro ⟨C, hrec⟩
  let t := (max θ 1 + 2) / 2
  have ht1 : 1 < t := by dsimp [t]; have := le_max_right θ 1; linarith
  have hθt : θ < t := by
    have hm : max θ 1 < 2 := max_lt hθ2 (by norm_num)
    have := le_max_left θ 1
    dsimp [t]
    linarith
  have ht2 : t < 2 := by dsimp [t]; have := max_lt hθ2 (by norm_num : (1 : ℝ) < 2); linarith
  let D := max (max (g 0) 0) (C / (t - θ)) + 1
  have hD : 0 < D := by
    have := (le_max_right (g 0) 0).trans (le_max_left (max (g 0) 0) (C / (t - θ)))
    dsimp [D]
    linarith
  have hbase : g 0 ≤ D := by
    have := (le_max_left (g 0) 0).trans (le_max_left (max (g 0) 0) (C / (t - θ)))
    dsimp [D]
    linarith
  have hgap : C ≤ D * (t - θ) := by
    apply (div_le_iff₀ (sub_pos.mpr hθt)).mp
    have := le_max_right (max (g 0) 0) (C / (t - θ))
    dsimp [D]
    linarith
  have hg := geometric_upper_of_affine_recurrence g θ C t D hθ ht1.le hD.le
    hbase hgap (mul_nonneg hD.le (sub_nonneg.mpr hθt.le)) hrec
  have ht0 := tendsto_self_mul_const_pow_of_lt_one
    (show (0 : ℝ) ≤ t / 2 by positivity) (show t / 2 < 1 by linarith)
  have hh0 := tendsto_self_mul_const_pow_of_lt_one
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
  have hlim : Tendsto (fun m : ℕ => (m : ℝ) * (D * t ^ m + L) / 2 ^ m)
      atTop (𝓝 0) := by
    have hh := (ht0.const_mul D).add (hh0.const_mul L)
    simp only [mul_zero, add_zero] at hh
    convert hh using 1
    ext m
    have htdiv : (t / 2) ^ m = t ^ m / 2 ^ m := div_pow t 2 m
    have hhdiv : (1 / 2 : ℝ) ^ m = 1 / 2 ^ m := by rw [div_pow, one_pow]
    rw [htdiv, hhdiv]
    ring
  obtain ⟨m, hm, hsmall⟩ := ((eventually_ge_atTop 7).and
    (hlim.eventually (eventually_lt_nhds hA))).exists
  have hlo := hlower m hm
  have hhi : (m : ℝ) * (g m + L) ≤ m * (D * t ^ m + L) := by
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg (α := ℝ) m)
    linarith [hg m]
  have hle : A ≤ (m : ℝ) * (D * t ^ m + L) / 2 ^ m :=
    (le_div_iff₀ (by positivity)).mpr (hlo.trans hhi)
  linarith

noncomputable def squareDensity (N : ℕ) : ℝ := squareMax N / N

lemma squareDensity_pos (N : ℕ) (hN : 1 ≤ N) : 0 < squareDensity N :=
  div_pos (squareMax_pos N hN) (by exact_mod_cast (show 0 < N by omega))

lemma squareDensity_le_one (N : ℕ) : squareDensity N ≤ 1 := by
  by_cases hN : N = 0
  · simp [squareDensity, hN]
  apply (div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hN : (0 : ℝ) < N)).mpr
  dsimp [squareMax]
  exact_mod_cast max_square_sidon_card_le N

lemma squareDensity_primorial_log_lower (B m : ℕ) (hB : 128 ≤ B) (hm : 7 ≤ m) :
    (-Real.log (Real.sqrt (3 / 4)) / 8) * (2 : ℝ) ^ m ≤
      m * (-Real.log (squareDensity (B ^ (2 ^ m))) + Real.log 2) := by
  let r : ℝ := Real.sqrt (3 / 4)
  let k := (sievePrimes (2 ^ m)).card
  have hr0 : 0 < r := Real.sqrt_pos.mpr (by norm_num)
  have hr1 : r < 1 := by
    have hs : r ^ 2 = 3 / 4 := Real.sq_sqrt (by norm_num)
    nlinarith
  have hlr : 0 < -Real.log r := neg_pos.mpr (Real.log_neg hr0 hr1)
  have hN : 128 ^ (2 ^ m) ≤ B ^ (2 ^ m) := Nat.pow_le_pow_left hB _
  have hNpos : 0 < B ^ (2 ^ m) := pow_pos (by omega) _
  have hNposR : (0 : ℝ) < B ^ (2 ^ m) := by exact_mod_cast hNpos
  have hu : squareDensity (B ^ (2 ^ m)) ≤ 2 * r ^ k := by
    apply (div_le_iff₀ (by exact_mod_cast hNpos : (0 : ℝ) < (B ^ (2 ^ m) : ℕ))).mpr
    exact square_sidon_primorial_parametric_upper (2 ^ m) (B ^ (2 ^ m))
      (by positivity) hN
  have hp := squareDensity_pos (B ^ (2 ^ m)) hNpos
  have hlog := Real.log_le_log hp hu
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (pow_pos hr0 k).ne', Real.log_pow] at hlog
  have hm128 : 128 ≤ (2 : ℕ) ^ m := by
    calc
      128 = 2 ^ 7 := by norm_num
      _ ≤ _ := Nat.pow_le_pow_right (by decide) hm
  have hk := sievePrimes_card_log_lower (2 ^ m) hm128
  rw [Nat.cast_pow, Real.log_pow] at hk
  have hl2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have hmul := mul_le_mul_of_nonneg_left hl2
    (show (0 : ℝ) ≤ (k : ℝ) * m by positivity)
  have hk' : (2 : ℝ) ^ m / 8 ≤ (k : ℝ) * m := by
    dsimp [k] at hmul ⊢
    nlinarith only [hk, hmul]
  have h1 := mul_le_mul_of_nonneg_left hk' hlr.le
  have h2 := mul_le_mul_of_nonneg_left
    (show (k : ℝ) * (-Real.log r) ≤ -Real.log (squareDensity (B ^ (2 ^ m))) + Real.log 2 by linarith)
    (Nat.cast_nonneg (α := ℝ) m)
  dsimp [r] at h1 h2
  nlinarith only [h1, h2]

/-- A fixed power below two cannot give an eventual density amplification law. -/
theorem no_fixed_power_density_amplification_of_nonneg (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ2 : θ < 2) :
    ¬ ∃ c > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      c * (squareDensity N) ^ θ ≤ squareDensity (N ^ 2) := by
  rintro ⟨c, hc, he⟩
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp he
  let B := max N₀ 128
  have hB : 128 ≤ B := le_max_right _ _
  have hBN (m : ℕ) : B ≤ B ^ (2 ^ m) := by
    calc
      B = B ^ 1 := by simp
      _ ≤ _ := Nat.pow_le_pow_right (by omega) (Nat.one_le_pow m 2 (by decide))
  let g : ℕ → ℝ := fun m => -Real.log (squareDensity (B ^ (2 ^ m)))
  have hA : 0 < -Real.log (Real.sqrt (3 / 4)) / 8 := by
    have hr0 : 0 < Real.sqrt (3 / 4) := Real.sqrt_pos.mpr (by norm_num)
    have hr1 : Real.sqrt (3 / 4) < 1 := by
      have := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3 / 4)
      nlinarith
    exact div_pos (neg_pos.mpr (Real.log_neg hr0 hr1)) (by norm_num)
  apply no_subquadratic_log_recurrence g
    (-Real.log (Real.sqrt (3 / 4)) / 8) (Real.log 2) hA
    (fun m hm => squareDensity_primorial_log_lower B m hB hm) θ hθ0 hθ2
  refine ⟨-Real.log c, ?_⟩
  intro m
  have hn : N₀ ≤ B ^ (2 ^ m) := (le_max_left _ _).trans (hBN m)
  have hp := squareDensity_pos (B ^ (2 ^ m)) (by have := hBN m; omega)
  have hl := Real.log_le_log (mul_pos hc (Real.rpow_pos_of_pos hp θ)) (hN₀ _ hn)
  rw [Real.log_mul hc.ne' (Real.rpow_pos_of_pos hp θ).ne', Real.log_rpow hp] at hl
  have heq : B ^ (2 ^ (m + 1)) = (B ^ (2 ^ m)) ^ 2 := by rw [pow_succ, pow_mul]
  dsimp [g]
  rw [heq]
  linarith

/-- The nonnegativity restriction on the fixed power is unnecessary. -/
theorem no_fixed_power_density_amplification (θ : ℝ) (hθ2 : θ < 2) :
    ¬ ∃ c > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      c * (squareDensity N) ^ θ ≤ squareDensity (N ^ 2) := by
  by_cases hθ0 : 0 ≤ θ
  · exact no_fixed_power_density_amplification_of_nonneg θ hθ0 hθ2
  rintro ⟨c, hc, he⟩
  apply no_fixed_power_density_amplification_of_nonneg 0 (by norm_num) (by norm_num)
  refine ⟨c, hc, ?_⟩
  filter_upwards [he, eventually_ge_atTop 1] with N hN hn
  have hp : 1 ≤ (squareDensity N) ^ θ := by
    have h := Real.rpow_le_rpow_of_exponent_ge (squareDensity_pos N hn)
      (squareDensity_le_one N) (show θ ≤ 0 by linarith)
    simpa using h
  simpa using (le_mul_of_one_le_right hc.le hp).trans hN

/-- Each such proposed gain fails at arbitrarily large scales. -/
theorem frequently_small_power_density_gain (θ c : ℝ) (hθ : θ < 2) (hc : 0 < c) :
    ∃ᶠ N : ℕ in atTop, squareDensity (N ^ 2) < c * (squareDensity N) ^ θ := by
  have hn : ¬ ∀ᶠ N : ℕ in atTop,
      c * (squareDensity N) ^ θ ≤ squareDensity (N ^ 2) := by
    intro h
    exact no_fixed_power_density_amplification θ hθ ⟨c, hc, h⟩
  simpa only [not_le] using Filter.not_eventually.mp hn

/-- Cardinality formulation: this fixed-power exponent-improvement recurrence
cannot hold at every sufficiently large scale, even though its intended limiting
exponent is compatible with the original conjecture. -/
theorem no_fixed_power_cardinality_amplification (θ : ℝ) (hθ : θ < 2) :
    ¬ ∃ c > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      c * (N : ℝ) ^ (2 - θ) * (squareMax N) ^ θ ≤ squareMax (N ^ 2) := by
  rintro ⟨c, hc, he⟩
  apply no_fixed_power_density_amplification θ hθ
  refine ⟨c, hc, ?_⟩
  filter_upwards [he, eventually_ge_atTop 1] with N hN hn
  have hn0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  dsimp [squareDensity]
  rw [Real.div_rpow (squareMax_pos N hn).le hn0.le, Nat.cast_pow]
  apply (le_div_iff₀ (sq_pos_of_pos hn0)).mpr
  calc
    c * (squareMax N ^ θ / (N : ℝ) ^ θ) * (N : ℝ) ^ 2 =
        c * (N : ℝ) ^ (2 - θ) * squareMax N ^ θ := by
      rw [Real.rpow_sub hn0, Real.rpow_two]
      ring
    _ ≤ _ := hN

theorem frequently_small_power_cardinality_gain (θ c : ℝ) (hθ : θ < 2) (hc : 0 < c) :
    ∃ᶠ N : ℕ in atTop,
      squareMax (N ^ 2) < c * (N : ℝ) ^ (2 - θ) * squareMax N ^ θ := by
  have hn : ¬ ∀ᶠ N : ℕ in atTop,
      c * (N : ℝ) ^ (2 - θ) * squareMax N ^ θ ≤ squareMax (N ^ 2) := by
    intro h
    exact no_fixed_power_cardinality_amplification θ hθ ⟨c, hc, h⟩
  simpa only [not_le] using Filter.not_eventually.mp hn

#print axioms no_fixed_power_density_amplification
#print axioms frequently_small_power_density_gain
#print axioms no_fixed_power_cardinality_amplification
#print axioms frequently_small_power_cardinality_gain
end Erdos773.Amplification
