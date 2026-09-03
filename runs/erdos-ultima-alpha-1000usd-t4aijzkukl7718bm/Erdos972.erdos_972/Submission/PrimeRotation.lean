import Submission.VaughanSums
import Submission.ChebyshevLower
import Submission.RationalRoute
import Submission.PrimePowerError

/-! Simultaneous good scales for finitely many prime-rotation frequencies.
This file does not assert simultaneous primality. -/
namespace Erdos972PrimeRotation
open Finset
open Erdos972VaughanSums Erdos972ExponentialSum

lemma rational_separation (r s : ℚ) (hrs : r ≠ s) :
    1 ≤ |(r : ℝ) - s| * r.den * s.den := by
  have hc : r.num * (s.den : ℤ) - s.num * (r.den : ℤ) ≠ 0 :=
    sub_ne_zero.mpr (mt Rat.eq_iff_mul_eq_mul.mpr hrs)
  have h := Int.one_le_abs hc
  have hnumr : (r : ℝ) * r.den = r.num := by exact_mod_cast Rat.mul_den_eq_num r
  have hnums : (s : ℝ) * s.den = s.num := by exact_mod_cast Rat.mul_den_eq_num s
  have he : ((r.num * (s.den : ℤ) - s.num * (r.den : ℤ) : ℤ) : ℝ) =
      ((r : ℝ) - s) * r.den * s.den := by
    push_cast
    rw [← hnumr, ← hnums]
    ring
  have h' : (1 : ℝ) ≤ |((r.num * (s.den : ℤ) - s.num * (r.den : ℤ) : ℤ) : ℝ)| := by
    exact_mod_cast h
  rwa [he, abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) r.den),
    abs_of_nonneg (Nat.cast_nonneg (α := ℝ) s.den)] at h'

lemma den_nat_mul_le (h : ℕ) (r : ℚ) : ((h : ℚ) * r).den ≤ r.den := by
  have hd := Rat.mul_den_dvd (h : ℚ) r
  simp only [Rat.den_natCast, one_mul] at hd
  exact Nat.le_of_dvd r.pos hd

lemma den_le_nat_mul_den {h : ℕ} (hh : 0 < h) (r : ℚ) :
    r.den ≤ h * ((h : ℚ) * r).den := by
  let s : ℚ := (h : ℚ) * r
  have he : s * (h : ℚ)⁻¹ = r := by dsimp [s]; field_simp
  have hd := Rat.mul_den_dvd s (h : ℚ)⁻¹
  rw [he, Rat.den_inv_of_ne_zero (Nat.cast_ne_zero.mpr hh.ne'), Rat.num_natCast,
    Int.natAbs_natCast] at hd
  exact (Nat.le_of_dvd (Nat.mul_pos s.pos hh) hd).trans_eq (Nat.mul_comm _ _)

/-- A good approximation to `θ` supplies comparable-denominator approximations
to every one of finitely many positive integer multiples of `θ`. -/
theorem simultaneous_approximant {θ : ℝ} (r : ℚ)
    (hr : |θ - r| ≤ 1 / (r.den : ℝ) ^ 2)
    (h H : ℕ) (hh : 0 < h) (hhH : h ≤ H) :
    ∃ s : ℚ, r.den ≤ 2 * H * s.den ∧ s.den ≤ 4 * H * r.den ∧
      |(h : ℝ) * θ - s| ≤ 1 / (s.den : ℝ) ^ 2 := by
  have hH : 0 < H := hh.trans_le hhH
  let T : ℕ := 4 * H * r.den
  have hT : 0 < T := by dsimp [T]; positivity
  obtain ⟨s, hs, hsT⟩ := Real.exists_rat_abs_sub_le_and_den_le ((h : ℝ) * θ) hT
  refine ⟨s, ?_, hsT, ?_⟩
  · by_contra hlow
    have hsmall : 2 * H * s.den < r.den := Nat.lt_of_not_ge hlow
    by_cases he : (h : ℚ) * r = s
    · have hd := den_le_nat_mul_den hh r
      rw [he] at hd
      have hm := Nat.mul_le_mul_right s.den hhH
      nlinarith
    · have hsep := rational_separation ((h : ℚ) * r) s he
      have hsep' : (1 : ℝ) ≤ |(h : ℝ) * r - s| * r.den * s.den := by
        simp only [Rat.cast_mul, Rat.cast_natCast] at hsep
        apply hsep.trans
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (den_nat_mul_le h r)) (abs_nonneg _))
          (Nat.cast_nonneg _)
      have htriangle : |(h : ℝ) * r - s| ≤
          (h : ℝ) / (r.den : ℝ) ^ 2 + 1 / (((T : ℝ) + 1) * s.den) := by
        calc
          _ ≤ |(h : ℝ) * r - h * θ| + |(h : ℝ) * θ - s| := abs_sub_le _ _ _
          _ = (h : ℝ) * |θ - r| + |(h : ℝ) * θ - s| := by
            rw [← mul_sub, abs_mul, abs_of_nonneg (Nat.cast_nonneg h), abs_sub_comm (r : ℝ) θ]
          _ ≤ _ := by
            have hp := mul_le_mul_of_nonneg_left hr (Nat.cast_nonneg (α := ℝ) h)
            simpa only [mul_one_div] using add_le_add hp hs
      have hq : (0 : ℝ) < r.den := Nat.cast_pos.mpr r.pos
      have hd : (0 : ℝ) < s.den := Nat.cast_pos.mpr s.pos
      have hTr : (0 : ℝ) < (T : ℝ) + 1 := by positivity
      have hhalf : (h : ℝ) * s.den / r.den < 1 / 2 := by
        apply (div_lt_iff₀ hq).mpr
        have hm : (h : ℝ) ≤ H := Nat.cast_le.mpr hhH
        have hsm : 2 * (H : ℝ) * s.den < r.den := by exact_mod_cast hsmall
        nlinarith
      have hhalf' : (r.den : ℝ) / ((T : ℝ) + 1) < 1 / 2 := by
        apply (div_lt_iff₀ hTr).mpr
        have hH' : (1 : ℝ) ≤ H := by exact_mod_cast hH
        dsimp [T]
        push_cast
        nlinarith
      have hbound := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right htriangle hq.le) hd.le
      have heq : ((h : ℝ) / (r.den : ℝ) ^ 2 + 1 / (((T : ℝ) + 1) * s.den)) *
          r.den * s.den = (h : ℝ) * s.den / r.den + r.den / ((T : ℝ) + 1) := by
        field_simp
      rw [heq] at hbound
      linarith
  · apply hs.trans
    have hd : (0 : ℝ) < s.den := Nat.cast_pos.mpr s.pos
    apply one_div_le_one_div_of_le (sq_pos_of_pos hd)
    have hsT' : (s.den : ℝ) ≤ T := Nat.cast_le.mpr hsT
    nlinarith

lemma fourth_root_bounds {q : ℕ} (hq : 0 < q) :
    let u := Nat.sqrt (Nat.sqrt q)
    0 < u ∧ u ^ 4 ≤ q ∧ q ≤ 16 * u ^ 4 := by
  dsimp only
  let u := Nat.sqrt (Nat.sqrt q)
  have hu : 0 < u := Nat.sqrt_pos.mpr (Nat.sqrt_pos.mpr hq)
  have hlow : u ^ 4 ≤ q := by
    calc
      _ = (u ^ 2) ^ 2 := by ring
      _ ≤ (Nat.sqrt q) ^ 2 := Nat.pow_le_pow_left (Nat.sqrt_le' _) 2
      _ ≤ q := Nat.sqrt_le' q
  have hupp : q < (u + 1) ^ 4 := by
    calc
      _ < (Nat.sqrt q + 1) ^ 2 := Nat.lt_succ_sqrt' q
      _ ≤ ((u + 1) ^ 2) ^ 2 := Nat.pow_le_pow_left (Nat.succ_le_of_lt (Nat.lt_succ_sqrt' (Nat.sqrt q))) 2
      _ = _ := by ring
  refine ⟨hu, hlow, hupp.le.trans ?_⟩
  calc
    _ ≤ (2 * u) ^ 4 := Nat.pow_le_pow_left (by omega) 4
    _ = _ := by ring

lemma le_fourth_root_iff (T q : ℕ) :
    T ≤ Nat.sqrt (Nat.sqrt q) ↔ T ^ 4 ≤ q := by
  rw [Nat.le_sqrt', Nat.le_sqrt']
  ring_nf

lemma logarithmic_scale_bounds {u : ℕ} (hu : 0 < u) :
    Real.log ((u : ℝ) ^ 6 + 1) ≤ 7 * (1 + Real.log u) ∧
    2 + Real.log (2 * (u : ℝ) ^ 6 + 1) ≤ 10 * (1 + Real.log u) ∧
    ((Nat.log 2 (u ^ 6) + 1 : ℕ) : ℝ) ≤ 13 * (1 + Real.log u) := by
  have hu1 : (1 : ℝ) ≤ u := by exact_mod_cast hu
  have hu0 : (0 : ℝ) < u := by positivity
  have hp : (1 : ℝ) ≤ (u : ℝ) ^ 6 := one_le_pow₀ hu1
  have hl0 := Real.log_natCast_nonneg u
  have hlog2 : Real.log 2 ≤ 1 := by simpa only [show (2 : ℝ) - 1 = 1 by norm_num, show (3 : ℝ) - 1 = 2 by norm_num, show (4 : ℝ) - 1 = 3 by norm_num] using Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  have hlog3 : Real.log 3 ≤ 2 := by simpa only [show (2 : ℝ) - 1 = 1 by norm_num, show (3 : ℝ) - 1 = 2 by norm_num, show (4 : ℝ) - 1 = 3 by norm_num] using Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
  have hhalf : (1 : ℝ) / 2 ≤ Real.log 2 := by
    simpa only [show (1 : ℝ) - 2⁻¹ = 1 / 2 by norm_num] using Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
  refine ⟨?_, ?_, ?_⟩
  · have h := Real.log_le_log (by positivity : (0 : ℝ) < (u : ℝ) ^ 6 + 1)
      (show (u : ℝ) ^ 6 + 1 ≤ 2 * (u : ℝ) ^ 6 by linarith)
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at h
    norm_num at h
    linarith
  · have h := Real.log_le_log (by positivity : (0 : ℝ) < 2 * (u : ℝ) ^ 6 + 1)
      (show 2 * (u : ℝ) ^ 6 + 1 ≤ 3 * (u : ℝ) ^ 6 by linarith)
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at h
    norm_num at h
    linarith
  · have h := Real.natLog_le_logb (u ^ 6) 2
    rw [Real.logb, Nat.cast_pow, Real.log_pow] at h
    norm_num at h
    have hd : 6 * Real.log u / Real.log 2 ≤ 12 * Real.log u := by
      apply (div_le_iff₀ (by linarith : 0 < Real.log 2)).mpr
      nlinarith
    push_cast
    linarith

/-- A convenient explicit constant for polynomially comparable denominators. -/
noncomputable def rotationConstant (K : ℕ) : ℝ :=
  32 * K * (K + 6) + 7 + 130000 * Real.exp (2 * Real.pi) * (K + 4)

lemma rotationConstant_pos (K : ℕ) : 0 < rotationConstant K := by
  unfold rotationConstant
  positivity

set_option maxHeartbeats 1000000 in
/-- At sixth-power scales and polynomially comparable rational denominators,
the complete Vaughan majorant has a power saving up to logarithms. -/
lemma sixth_scale_majorant {q : ℕ} [NeZero q] (u K : ℕ)
    (hu : 0 < u) (hK : 0 < K) (hlo : u ^ 4 ≤ K * q) (hhi : q ≤ K * u ^ 4) :
    4 * Real.log ((u : ℝ) ^ 6 + 1) * q * (2 + Real.log q) +
      2 * Real.log ((u : ℝ) * u) * q * (2 + Real.log q) + Chebyshev.psi u +
      (Nat.log 2 (u ^ 6) + 1 : ℕ) *
        (Real.exp (2 * Real.pi) * (2 + Real.log (2 * (u : ℝ) ^ 6 + 1)) ^ 4 *
          Real.sqrt (2 * (u : ℝ) ^ 6 *
            (2 * (u : ℝ) ^ 6 / q + 4 * (u ^ 6 / u : ℕ) + q))) ≤
      rotationConstant K * (1 + Real.log u) ^ 5 * (u : ℝ) ^ 5 * Real.sqrt u := by
  let x : ℝ := u
  let k : ℝ := K
  let S : ℝ := 1 + Real.log u
  let W : ℝ := S ^ 5 * x ^ 5 * Real.sqrt x
  have hx1 : 1 ≤ x := by dsimp [x]; exact_mod_cast hu
  have hx0 : 0 < x := by positivity
  have hk1 : 1 ≤ k := by dsimp [k]; exact_mod_cast hK
  have hk0 : 0 < k := by positivity
  have hq : (0 : ℝ) < q := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
  have hqlo : x ^ 4 ≤ k * q := by dsimp [x, k]; exact_mod_cast hlo
  have hqhi : (q : ℝ) ≤ k * x ^ 4 := by dsimp [x, k]; exact_mod_cast hhi
  have hS : 1 ≤ S := by dsimp [S]; linarith [Real.log_natCast_nonneg u]
  have hS0 : 0 ≤ S := by linarith
  have hsqrt : 1 ≤ Real.sqrt x := (Real.le_sqrt (by norm_num) hx0.le).mpr (by simpa using hx1)
  obtain ⟨hlogX, hL, hJ⟩ := logarithmic_scale_bounds hu
  change Real.log (x ^ 6 + 1) ≤ 7 * S at hlogX
  change 2 + Real.log (2 * x ^ 6 + 1) ≤ 10 * S at hL
  change ((Nat.log 2 (u ^ 6) + 1 : ℕ) : ℝ) ≤ 13 * S at hJ
  have hlogq : 2 + Real.log q ≤ (k + 6) * S := by
    have h := Real.log_le_log hq hqhi
    rw [Real.log_mul hk0.ne' (by positivity), Real.log_pow] at h
    have hklog := Real.log_le_sub_one_of_pos hk0
    have hl0 := Real.log_natCast_nonneg u
    dsimp [S, x] at *
    nlinarith
  have hlogq0 : 0 ≤ 2 + Real.log q := by linarith [Real.log_natCast_nonneg q]
  have hlogu2 : 2 * Real.log ((u : ℝ) * u) ≤ 4 * S := by
    rw [← pow_two, Real.log_pow]
    dsimp [S]
    linarith
  have hXdiv : x ^ 6 / q ≤ k * x ^ 2 := by
    apply (div_le_iff₀ hq).mpr
    have := mul_le_mul_of_nonneg_right hqlo (sq_nonneg x)
    nlinarith
  have hdiv : ((u ^ 6 / u : ℕ) : ℝ) = x ^ 5 := by
    rw [show u ^ 6 = u ^ 5 * u by ring, Nat.mul_div_cancel _ hu, Nat.cast_pow]
  have hinside : 2 * x ^ 6 * (2 * x ^ 6 / q + 4 * (u ^ 6 / u : ℕ) + q) ≤
      (k + 4) ^ 2 * x ^ 10 * x := by
    rw [hdiv]
    have hp25 : x ^ 2 ≤ x ^ 5 := pow_le_pow_right₀ hx1 (by omega)
    have hp45 : x ^ 4 ≤ x ^ 5 := pow_le_pow_right₀ hx1 (by omega)
    have hinner : 2 * x ^ 6 / q + 4 * x ^ 5 + q ≤ (3 * k + 4) * x ^ 5 := by
      have h1 := mul_le_mul_of_nonneg_left hp25 hk0.le
      have h2 := mul_le_mul_of_nonneg_left hp45 hk0.le
      rw [mul_div_assoc]
      linarith
    have hb := mul_le_mul_of_nonneg_left hinner (show 0 ≤ 2 * x ^ 6 by positivity)
    have hc : 2 * (3 * k + 4) ≤ (k + 4) ^ 2 := by nlinarith
    calc
      _ ≤ 2 * x ^ 6 * ((3 * k + 4) * x ^ 5) := hb
      _ = (2 * (3 * k + 4)) * x ^ 11 := by ring
      _ ≤ (k + 4) ^ 2 * x ^ 11 := mul_le_mul_of_nonneg_right hc (by positivity)
      _ = _ := by ring
  have hsqrtbound :
      Real.sqrt (2 * x ^ 6 * (2 * x ^ 6 / q + 4 * (u ^ 6 / u : ℕ) + q)) ≤
        (k + 4) * x ^ 5 * Real.sqrt x := by
    apply (Real.sqrt_le_left (by positivity)).mpr
    apply hinside.trans_eq
    rw [mul_pow, mul_pow, Real.sq_sqrt hx0.le]
    ring
  have hW0 : 0 ≤ W := by dsimp [W]; positivity
  have hS2x4 : S ^ 2 * x ^ 4 ≤ W := by
    have h1 : S ^ 2 ≤ S ^ 5 := pow_le_pow_right₀ hS (by omega)
    have h2 : x ^ 4 ≤ x ^ 5 := pow_le_pow_right₀ hx1 (by omega)
    have h3 := mul_le_mul h1 h2 (by positivity) (by positivity)
    exact h3.trans (by
      dsimp [W]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hsqrt
        (mul_nonneg (pow_nonneg hS0 5) (pow_nonneg hx0.le 5)))
  have hxW : x ≤ W := by
    have hx5 : x ≤ x ^ 5 := by simpa using pow_le_pow_right₀ hx1 (show 1 ≤ 5 by omega)
    have hS5 : 1 ≤ S ^ 5 := one_le_pow₀ hS
    calc
      x ≤ x ^ 5 := hx5
      _ ≤ S ^ 5 * x ^ 5 := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hS5 (pow_nonneg hx0.le 5)
      _ ≤ W := by
        dsimp [W]
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hsqrt (by positivity : 0 ≤ S ^ 5 * x ^ 5)
  have hI : 4 * Real.log (x ^ 6 + 1) * q * (2 + Real.log q) ≤
      28 * k * (k + 6) * W := by
    calc
      _ ≤ 4 * (7 * S) * (k * x ^ 4) * ((k + 6) * S) := by
        gcongr
      _ = 28 * k * (k + 6) * (S ^ 2 * x ^ 4) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hS2x4 (by positivity)
  have hII : 2 * Real.log ((u : ℝ) * u) * q * (2 + Real.log q) ≤
      4 * k * (k + 6) * W := by
    calc
      _ ≤ (4 * S) * (k * x ^ 4) * ((k + 6) * S) := by gcongr
      _ = 4 * k * (k + 6) * (S ^ 2 * x ^ 4) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hS2x4 (by positivity)
  have hpsi : Chebyshev.psi u ≤ 7 * W := by
    have h := Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg (α := ℝ) u)
    have hl : Real.log 4 ≤ 3 := by simpa only [show (2 : ℝ) - 1 = 1 by norm_num, show (3 : ℝ) - 1 = 2 by norm_num, show (4 : ℝ) - 1 = 3 by norm_num] using Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
    change Chebyshev.psi u ≤ (Real.log 4 + 4) * x at h
    nlinarith
  have hIII : ((Nat.log 2 (u ^ 6) + 1 : ℕ) : ℝ) *
      (Real.exp (2 * Real.pi) * (2 + Real.log (2 * x ^ 6 + 1)) ^ 4 *
        Real.sqrt (2 * x ^ 6 * (2 * x ^ 6 / q + 4 * (u ^ 6 / u : ℕ) + q))) ≤
      (130000 * Real.exp (2 * Real.pi) * (k + 4)) * W := by
    calc
      _ ≤ (13 * S) * (Real.exp (2 * Real.pi) * (10 * S) ^ 4 *
          ((k + 4) * x ^ 5 * Real.sqrt x)) := by
        have hL0 : 0 ≤ 2 + Real.log (2 * x ^ 6 + 1) := by
          have := Real.log_nonneg (show (1 : ℝ) ≤ 2 * x ^ 6 + 1 by nlinarith [pow_nonneg hx0.le 6])
          linarith
        gcongr
      _ = _ := by dsimp [W]; ring
  change _ ≤ rotationConstant K * S ^ 5 * x ^ 5 * Real.sqrt x
  have he : rotationConstant K * S ^ 5 * x ^ 5 * Real.sqrt x =
      (32 * k * (k + 6) + 7 + 130000 * Real.exp (2 * Real.pi) * (k + 4)) * W := by
    dsimp [rotationConstant, k, W]
    ring
  rw [he]
  linarith

open Filter in
/-- The explicit normalized majorant tends to zero. -/
theorem eventually_rotation_majorant_small (K : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ u : ℕ in atTop,
      rotationConstant K * (1 + Real.log u) ^ 5 * (u : ℝ) ^ 5 * Real.sqrt u ≤
        ε * (u : ℝ) ^ 6 := by
  let C : ℝ := rotationConstant K
  have hC : 0 < C := rotationConstant_pos K
  let δ : ℝ := ε / (32 * C)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hsmall : ∀ᶠ x : ℝ in atTop,
      ‖Real.log x ^ 5‖ ≤ δ * ‖Real.sqrt x‖ := by
    have hpow (x : ℝ) : x ^ (5 : ℝ) = x ^ (5 : ℕ) := Real.rpow_natCast x 5
    simpa only [hpow, ← Real.sqrt_eq_rpow] using
      (isLittleO_log_rpow_rpow_atTop (5 : ℝ) (by norm_num : (0 : ℝ) < 1 / 2)).bound hδ
  have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  filter_upwards [hnat.eventually (eventually_ge_atTop (1 : ℝ)),
    hnat.eventually (Real.tendsto_log_atTop.eventually_ge_atTop 1),
    hnat.eventually hsmall] with u hu hlog hs
  have hu0 : (0 : ℝ) ≤ u := Nat.cast_nonneg _
  have hl0 : 0 ≤ Real.log u := by linarith
  simp only [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hl0 5),
    abs_of_nonneg (Real.sqrt_nonneg _)] at hs
  have hS : (1 + Real.log u) ^ 5 ≤ 32 * Real.log u ^ 5 := by
    calc
      _ ≤ (2 * Real.log u) ^ 5 := pow_le_pow_left₀ (by positivity) (by linarith) 5
      _ = _ := by ring
  calc
    _ ≤ C * (32 * Real.log u ^ 5) * (u : ℝ) ^ 5 * Real.sqrt u := by
      apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg hu0 5)
      exact mul_le_mul_of_nonneg_left hS hC.le
    _ ≤ C * (32 * (δ * Real.sqrt u)) * (u : ℝ) ^ 5 * Real.sqrt u := by
      gcongr
    _ = ε * (u : ℝ) ^ 6 := by
      have he : C * 32 * δ = ε := by dsimp [δ]; field_simp
      calc
        _ = (C * 32 * δ) * (u : ℝ) ^ 5 * (Real.sqrt u) ^ 2 := by ring
        _ = _ := by rw [he, Real.sq_sqrt hu0]; ring

lemma sixth_scale_eligible {u K q : ℕ} (hK : 0 < K)
    (hu : 8 * K ≤ u) (hlo : u ^ 4 ≤ K * q) :
    8 * (u * u) ≤ q ∧ 2 * (u : ℝ) ^ 6 ≤ (q : ℝ) ^ 2 := by
  have hup : 8 * K ≤ u ^ 2 := hu.trans (by simpa only [pow_two] using Nat.le_mul_self u)
  have hmul : K * (8 * (u * u)) ≤ K * q := by
    calc
      _ = (8 * K) * u ^ 2 := by ring
      _ ≤ u ^ 2 * u ^ 2 := Nat.mul_le_mul_right _ hup
      _ = u ^ 4 := by ring
      _ ≤ _ := hlo
  refine ⟨Nat.le_of_mul_le_mul_left hmul hK, ?_⟩
  have huk : 2 * K ^ 2 ≤ u ^ 2 := by
    have := Nat.pow_le_pow_left hu 2
    nlinarith
  have hm : K ^ 2 * (2 * u ^ 6) ≤ K ^ 2 * q ^ 2 := by
    calc
      _ = (2 * K ^ 2) * u ^ 6 := by ring
      _ ≤ u ^ 2 * u ^ 6 := Nat.mul_le_mul_right _ huk
      _ = (u ^ 4) ^ 2 := by ring
      _ ≤ (K * q) ^ 2 := Nat.pow_le_pow_left hlo 2
      _ = _ := by ring
  exact_mod_cast Nat.le_of_mul_le_mul_left hm (by positivity : 0 < K ^ 2)

theorem expSum_sixth_scale_bound {q : ℕ} [NeZero q]
    (a : ℕ) (ha : a.Coprime q) (θ : ℝ)
    (hθ : |θ - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (u K : ℕ) (hK : 0 < K) (hu : 8 * K ≤ u)
    (hlo : u ^ 4 ≤ K * q) (hhi : q ≤ K * u ^ 4) :
    ‖expSum ArithmeticFunction.vonMangoldt θ (u ^ 6)‖ ≤
      rotationConstant K * (1 + Real.log u) ^ 5 * (u : ℝ) ^ 5 * Real.sqrt u := by
  have hu0 : 0 < u := lt_of_lt_of_le (by positivity : 0 < 8 * K) hu
  obtain ⟨hUq, hXq⟩ := sixth_scale_eligible hK hu hlo
  have h := vonMangoldt_expSum_bound a ha θ hθ u (u ^ 6) hu0 hUq
    (by simpa only [Nat.cast_pow] using hXq)
  apply h.trans
  simpa only [Nat.cast_pow] using sixth_scale_majorant u K hu0 hK hlo hhi

lemma nonneg_rat_eq_natAbs_div (s : ℚ) (hs : 0 ≤ s) :
    (s : ℝ) = (s.num.natAbs : ℝ) / s.den := by
  have he : (s.num.natAbs : ℝ) = (s.num : ℝ) := by
    have hi : (s.num.natAbs : ℤ) = s.num :=
      (Int.natCast_natAbs s.num).trans (abs_of_nonneg (Rat.num_nonneg.mpr hs))
    simpa only [Int.cast_natCast] using congrArg (fun z : ℤ => (z : ℝ)) hi
  rw [he]
  exact_mod_cast (Rat.num_div_den s).symm

/-- Simultaneous cancellation at arbitrarily large common scales, for any
fixed finite set of positive rotation frequencies. -/
theorem exists_common_prime_rotation_scale {θ : ℝ} (hθ : 1 < θ) (hI : Irrational θ)
    (H : ℕ) (hH : 0 < H) {ε : ℝ} (hε : 0 < ε) (N : ℕ) :
    ∃ u : ℕ, N < u ∧ ∀ h : ℕ, 0 < h → h ≤ H →
      ‖expSum ArithmeticFunction.vonMangoldt ((h : ℝ) * θ) (u ^ 6)‖ ≤ ε * (u : ℝ) ^ 6 := by
  let K : ℕ := 64 * H
  have hK : 0 < K := by dsimp [K]; positivity
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp (eventually_rotation_majorant_small K hε)
  let B : ℕ := max T (max (8 * K) (N + 1))
  obtain ⟨r, hr, hden⟩ := Erdos972RationalRoute.exists_good_approximant_large_den hθ hI (B ^ 4)
  let u : ℕ := Nat.sqrt (Nat.sqrt r.den)
  have hBu : B ≤ u := (le_fourth_root_iff B r.den).mpr hden.le
  have hu : 8 * K ≤ u := (le_trans (le_max_left _ _) (le_max_right T _)).trans hBu
  have hNu : N < u := by
    have := (le_trans (le_max_right _ _) (le_max_right T _)).trans hBu
    omega
  have hTu : T ≤ u := (le_max_left _ _).trans hBu
  obtain ⟨hu0, hulow, huhi⟩ := fourth_root_bounds r.pos
  change 0 < u at hu0
  change u ^ 4 ≤ r.den at hulow
  change r.den ≤ 16 * u ^ 4 at huhi
  refine ⟨u, hNu, ?_⟩
  intro h hh hhH
  obtain ⟨s, hslo, hshi, hsapprox⟩ := simultaneous_approximant r hr.le h H hh hhH
  have hspos : (0 : ℝ) < s := by
    have hh1 : (1 : ℝ) ≤ h := by exact_mod_cast hh
    have hd1 : (1 : ℝ) ≤ s.den := by exact_mod_cast s.pos
    have herr : |(h : ℝ) * θ - s| ≤ 1 := hsapprox.trans
      ((div_le_one (by positivity)).mpr (by nlinarith))
    have := (abs_le.mp herr).2
    nlinarith
  have hsrep := nonneg_rat_eq_natAbs_div s (by exact_mod_cast hspos.le)
  have hlo : u ^ 4 ≤ K * s.den := by
    have hKH : 2 * H ≤ K := by dsimp [K]; omega
    exact (hulow.trans hslo).trans (by nlinarith)
  have hhi : s.den ≤ K * u ^ 4 := by
    have hm := Nat.mul_le_mul_left (4 * H) huhi
    dsimp [K]
    nlinarith
  letI : NeZero s.den := ⟨s.den_ne_zero⟩
  have hbound := expSum_sixth_scale_bound s.num.natAbs s.reduced ((h : ℝ) * θ)
    (by simpa only [← hsrep] using hsapprox) u K hK hu hlo hhi
  exact hbound.trans (hT u hTu)

noncomputable def primeExpSum (θ : ℝ) (N : ℕ) : ℂ :=
  ∑ p ∈ (Ioc 0 N).filter Nat.Prime, (Real.log p : ℂ) * phase (θ * p)

/-- Removing non-prime prime powers costs only `ψ(N)-θ(N)`. -/
lemma norm_expSum_sub_primeExpSum_le (θ : ℝ) (N : ℕ) :
    ‖expSum ArithmeticFunction.vonMangoldt θ N - primeExpSum θ N‖ ≤
      Chebyshev.psi N - Chebyshev.theta N := by
  classical
  have he : expSum ArithmeticFunction.vonMangoldt θ N - primeExpSum θ N =
      ∑ p ∈ (Ioc 0 N).filter (fun p => ¬p.Prime),
        (ArithmeticFunction.vonMangoldt p : ℂ) * phase (θ * p) := by
    unfold expSum primeExpSum
    simp only [sum_filter]
    rw [← sum_sub_distrib]
    apply sum_congr rfl
    intro p hp
    by_cases hprime : p.Prime
    · simp only [hprime, if_true, not_true_eq_false, if_false,
        ArithmeticFunction.vonMangoldt_apply_prime hprime, sub_self]
    · simp only [hprime, if_false, not_false_eq_true, if_true, sub_zero]
  rw [he, Chebyshev.psi_sub_theta_eq_sum_not_prime, Nat.floor_natCast]
  apply (norm_sum_le _ _).trans_eq
  apply sum_congr rfl
  intro p hp
  rw [norm_mul, norm_phase, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]

/-- The common-scale cancellation estimate holds for the actual prime-weighted
sum, not merely for prime powers. -/
theorem exists_common_prime_scale {θ : ℝ} (hθ : 1 < θ) (hI : Irrational θ)
    (H : ℕ) (hH : 0 < H) {ε : ℝ} (hε : 0 < ε) (N : ℕ) :
    ∃ u : ℕ, N < u ∧ ∀ h : ℕ, 0 < h → h ≤ H →
      ‖primeExpSum ((h : ℝ) * θ) (u ^ 6)‖ ≤ ε * (u : ℝ) ^ 6 := by
  let C : ℝ := Real.log 4 + 12
  have hC : 0 ≤ C := by dsimp [C]; positivity
  obtain ⟨T, hT⟩ := exists_nat_gt (2 * C / ε)
  obtain ⟨u, hu, hbound⟩ := exists_common_prime_rotation_scale hθ hI H hH
    (half_pos hε) (max N T)
  have hNu : N < u := (le_max_left _ _).trans_lt hu
  have hTu : T < u := (le_max_right _ _).trans_lt hu
  have hu0 : 0 < u := (Nat.zero_le N).trans_lt hNu
  have hu1 : (1 : ℝ) ≤ u := by exact_mod_cast hu0
  have huc : 2 * C / ε < (u : ℝ) := hT.trans (Nat.cast_lt.mpr hTu)
  have hCsmall : C ≤ (ε / 2) * (u : ℝ) ^ 3 := by
    have hp : (u : ℝ) ≤ (u : ℝ) ^ 3 := by
      simpa only [pow_one] using pow_le_pow_right₀ hu1 (show 1 ≤ 3 by omega)
    have hm := (div_lt_iff₀ hε).mp huc
    nlinarith
  have hsqrt : Real.sqrt ((u : ℝ) ^ 6) = (u : ℝ) ^ 3 := by
    rw [show (u : ℝ) ^ 6 = ((u : ℝ) ^ 3) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  refine ⟨u, hNu, ?_⟩
  intro h hh hhH
  have herr : ‖expSum ArithmeticFunction.vonMangoldt ((h : ℝ) * θ) (u ^ 6) -
      primeExpSum ((h : ℝ) * θ) (u ^ 6)‖ ≤ (ε / 2) * (u : ℝ) ^ 6 := by
    apply (norm_expSum_sub_primeExpSum_le _ _).trans
    have he := Erdos972PrimePowerError.psi_sub_theta_le_sqrt
      (show (1 : ℝ) ≤ (u ^ 6 : ℕ) by exact_mod_cast (one_le_pow₀ hu0 : 1 ≤ u ^ 6))
    simp only [Nat.cast_pow, hsqrt] at he ⊢
    apply he.trans
    change C * (u : ℝ) ^ 3 ≤ _
    calc
      _ ≤ ((ε / 2) * (u : ℝ) ^ 3) * (u : ℝ) ^ 3 :=
        mul_le_mul_of_nonneg_right hCsmall (by positivity)
      _ = _ := by ring
  have ht := norm_add_le
    (primeExpSum ((h : ℝ) * θ) (u ^ 6) - expSum ArithmeticFunction.vonMangoldt ((h : ℝ) * θ) (u ^ 6))
    (expSum ArithmeticFunction.vonMangoldt ((h : ℝ) * θ) (u ^ 6))
  rw [sub_add_cancel, norm_sub_rev] at ht
  exact ht.trans (by linarith [hbound h hh hhH])

#print axioms exists_common_prime_scale
#print axioms norm_expSum_sub_primeExpSum_le
#print axioms exists_common_prime_rotation_scale
#print axioms expSum_sixth_scale_bound
#print axioms eventually_rotation_majorant_small
#print axioms sixth_scale_majorant
#print axioms fourth_root_bounds
#print axioms simultaneous_approximant
end Erdos972PrimeRotation
