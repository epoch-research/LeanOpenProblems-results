import Mathlib
import Submission.PLog

/-!
# Balanced p-adic supercongruence

We prove a balanced supercongruence for products of "p-free factorials"
`W(m) = ∏_{1 ≤ j ≤ m, p ∤ j} j`, using the p-adic logarithm developed in
`Submission.PLog`.
-/

open PLog Finset

namespace PKaz

variable {p : ℕ} [hp : Fact p.Prime]

/-! ## Divisibility ↔ norm bridge, and reduction mod p -/

/-- `(p:ℤ_[p])^n ∣ x` is equivalent to `‖x‖ ≤ p^(-n)`. -/
lemma dvd_iff_norm_le (x : ℤ_[p]) (n : ℕ) :
    (p : ℤ_[p]) ^ n ∣ x ↔ ‖x‖ ≤ (p : ℝ) ^ (-n : ℤ) := by
  rw [PadicInt.norm_le_pow_iff_mem_span_pow, Ideal.mem_span_singleton]

lemma dvd_of_toZModPow_zero {x : ℤ_[p]} {n : ℕ}
    (h : PadicInt.toZModPow n x = 0) : (p : ℤ_[p]) ^ n ∣ x := by
  have hmem : x ∈ RingHom.ker (PadicInt.toZModPow n : ℤ_[p] →+* ZMod (p ^ n)) := h
  rw [PadicInt.ker_toZModPow] at hmem
  exact Ideal.mem_span_singleton.mp hmem

lemma dvd_of_toZMod_zero {x : ℤ_[p]} (h : PadicInt.toZMod x = 0) :
    (p : ℤ_[p]) ∣ x := by
  have hmem : x ∈ RingHom.ker (PadicInt.toZMod : ℤ_[p] →+* ZMod p) := h
  rw [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p] at hmem
  exact Ideal.mem_span_singleton.mp hmem

/-! ## p-adic inverses and harmonic sums -/

/-- p-adic inverse of a natural number, as an element of `ℤ_[p]`. -/
noncomputable def iv (i : ℕ) : ℤ_[p] := PadicInt.inv (i : ℤ_[p])

lemma norm_cast_eq_one {i : ℕ} (h : ¬ p ∣ i) : ‖(i : ℤ_[p])‖ = 1 := by
  rw [PadicInt.norm_natCast_eq_one_iff]
  exact (Nat.Prime.coprime_iff_not_dvd hp.out).mpr h

lemma iv_mul_cancel {i : ℕ} (h : ¬ p ∣ i) : iv i * (i : ℤ_[p]) = 1 :=
  PadicInt.inv_mul (norm_cast_eq_one h)

lemma mul_iv_cancel {i : ℕ} (h : ¬ p ∣ i) : (i : ℤ_[p]) * iv i = 1 :=
  PadicInt.mul_inv (norm_cast_eq_one h)

lemma norm_iv {i : ℕ} (h : ¬ p ∣ i) : ‖(iv i : ℤ_[p])‖ = 1 := by
  exact PadicInt.isUnit_iff.mp (IsUnit.of_mul_eq_one (i : ℤ_[p]) (iv_mul_cancel h))

/-- The coercion of a p-adic inverse to `ℚ_[p]` is the field inverse. -/
lemma coe_iv {i : ℕ} (h : ¬ p ∣ i) : ((iv i : ℤ_[p]) : ℚ_[p]) = ((i : ℚ_[p]))⁻¹ := by
  have hne : ((i : ℚ_[p])) ≠ 0 := by
    have : ‖(i : ℤ_[p])‖ = 1 := norm_cast_eq_one h
    intro hc
    have : ‖(i : ℤ_[p])‖ = 0 := by
      rw [PadicInt.norm_def]; simpa using congrArg (fun z : ℚ_[p] => ‖z‖) hc
    rw [norm_cast_eq_one h] at this; exact one_ne_zero this
  have h1 : ((iv i : ℤ_[p]) : ℚ_[p]) * (i : ℚ_[p]) = 1 := by
    have h2 := congrArg (fun z : ℤ_[p] => (z : ℚ_[p])) (iv_mul_cancel h)
    push_cast at h2
    simpa using h2
  calc ((iv i : ℤ_[p]) : ℚ_[p])
      = ((iv i : ℤ_[p]) : ℚ_[p]) * ((i : ℚ_[p]) * (i : ℚ_[p])⁻¹) := by
        rw [mul_inv_cancel₀ hne, mul_one]
    _ = (((iv i : ℤ_[p]) : ℚ_[p]) * (i : ℚ_[p])) * (i : ℚ_[p])⁻¹ := by ring
    _ = (i : ℚ_[p])⁻¹ := by rw [h1, one_mul]

/-- Reindex a sum over `Icc 1 (p-1)` (via `ℕ → ZMod p`) as a sum over the nonzero
elements of `ZMod p`. -/
lemma sum_Icc_castZMod {M : Type*} [AddCommMonoid M] (g : ZMod p → M) :
    ∑ i ∈ Finset.Icc 1 (p - 1), g (i : ZMod p) =
      ∑ x ∈ (Finset.univ.erase (0 : ZMod p)), g x := by
  haveI : NeZero p := ⟨hp.out.pos.ne'⟩
  have hp1 : 1 ≤ p := hp.out.one_lt.le
  refine Finset.sum_nbij' (fun i => (i : ZMod p)) (fun x => x.val) ?_ ?_ ?_ ?_ ?_
  · intro a ha
    rw [Finset.mem_Icc] at ha
    rw [Finset.mem_erase]
    refine ⟨?_, Finset.mem_univ _⟩
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hdvd
    have := Nat.le_of_dvd (by omega) hdvd
    omega
  · intro x hx
    rw [Finset.mem_erase] at hx
    rw [Finset.mem_Icc]
    have hval : x.val < p := ZMod.val_lt x
    have hpos : 0 < x.val := ZMod.val_pos.mpr hx.1
    exact ⟨hpos, Nat.le_sub_one_of_lt hval⟩
  · intro a ha
    rw [Finset.mem_Icc] at ha
    exact ZMod.val_cast_of_lt (by omega)
  · intro x _
    exact ZMod.natCast_zmod_val x
  · intro a _; rfl

/-- Power sum of `x⁻¹` over the nonzero elements of a finite field vanishes for
`1 ≤ κ < |K|-1`. -/
lemma sum_erase_inv_pow_eq_zero (κ : ℕ) (hκ1 : 1 ≤ κ) (hκ2 : κ < p - 1) :
    ∑ x ∈ (Finset.univ.erase (0 : ZMod p)), (x⁻¹) ^ κ = 0 := by
  haveI : NeZero p := ⟨hp.out.pos.ne'⟩
  -- include 0 back (its term is 0)
  have h0 : (0 : ZMod p)⁻¹ ^ κ = 0 := by
    rw [inv_zero, zero_pow (by omega)]
  have hsplit : ∑ x ∈ (Finset.univ.erase (0 : ZMod p)), (x⁻¹) ^ κ
      = ∑ x : ZMod p, (x⁻¹) ^ κ := by
    rw [← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ (0 : ZMod p)), h0, add_zero]
  -- reindex by inv (involution)
  have hbij : ∑ x : ZMod p, (x⁻¹) ^ κ = ∑ x : ZMod p, x ^ κ := by
    refine Finset.sum_nbij' (fun x => x⁻¹) (fun x => x⁻¹) (fun _ _ => Finset.mem_univ _)
      (fun _ _ => Finset.mem_univ _) (fun a _ => inv_inv a) (fun a _ => inv_inv a) ?_
    intro a _; rfl
  have hcard : Fintype.card (ZMod p) - 1 = p - 1 := by rw [ZMod.card]
  calc ∑ x ∈ (Finset.univ.erase (0 : ZMod p)), (x⁻¹) ^ κ
      = ∑ x : ZMod p, (x⁻¹) ^ κ := hsplit
    _ = ∑ x : ZMod p, x ^ κ := hbij
    _ = 0 := FiniteField.sum_pow_lt_card_sub_one (ZMod p) κ (by rw [hcard]; exact hκ2)

/-- The p-adic harmonic sum `Hz κ = ∑_{i=1}^{p-1} i^{-κ}` in `ℤ_[p]`. -/
noncomputable def Hz (κ : ℕ) : ℤ_[p] := ∑ i ∈ Finset.Icc 1 (p - 1), (iv i) ^ κ

lemma norm_Hz_le_one (κ : ℕ) : ‖(Hz κ : ℤ_[p])‖ ≤ 1 := PadicInt.norm_le_one _

lemma toZMod_iv {i : ℕ} (h : ¬ p ∣ i) :
    PadicInt.toZMod (iv i) = ((i : ZMod p))⁻¹ := by
  have hi1 : PadicInt.toZMod (iv i) * (i : ZMod p) = 1 := by
    have h2 := congrArg PadicInt.toZMod (iv_mul_cancel h)
    rw [map_mul, map_one, map_natCast] at h2
    exact h2
  have hne : (i : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]; exact h
  calc PadicInt.toZMod (iv i)
      = PadicInt.toZMod (iv i) * ((i : ZMod p) * (i : ZMod p)⁻¹) := by
        rw [mul_inv_cancel₀ hne, mul_one]
    _ = (PadicInt.toZMod (iv i) * (i : ZMod p)) * (i : ZMod p)⁻¹ := by ring
    _ = (i : ZMod p)⁻¹ := by rw [hi1, one_mul]

/-- Reduction mod `p` of `Hz κ`. -/
lemma toZMod_Hz (κ : ℕ) :
    PadicInt.toZMod (Hz κ) = ∑ i ∈ Finset.Icc 1 (p - 1), ((i : ZMod p)⁻¹) ^ κ := by
  rw [Hz, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_Icc] at hi
  have hnd : ¬ p ∣ i := fun hd => by have := Nat.le_of_dvd (by omega) hd; omega
  rw [map_pow, toZMod_iv hnd]

/-- `Hz κ` is divisible by `p` for `1 ≤ κ < p - 1` (power-sum vanishing). -/
lemma dvd_Hz {κ : ℕ} (hκ1 : 1 ≤ κ) (hκ2 : κ < p - 1) : (p : ℤ_[p]) ∣ Hz κ := by
  apply dvd_of_toZMod_zero
  rw [toZMod_Hz]
  calc ∑ i ∈ Finset.Icc 1 (p - 1), ((i : ZMod p)⁻¹) ^ κ
      = ∑ x ∈ Finset.univ.erase (0 : ZMod p), (x⁻¹) ^ κ :=
        sum_Icc_castZMod (fun x => (x⁻¹) ^ κ)
    _ = 0 := sum_erase_inv_pow_eq_zero κ hκ1 hκ2

/-- Convenience: the mod-`p` vanishing of inverse power sums over `Icc 1 (p-1)`. -/
lemma sum_Icc_inv_pow_zero {κ : ℕ} (hκ1 : 1 ≤ κ) (hκ2 : κ < p - 1) :
    ∑ i ∈ Finset.Icc 1 (p - 1), ((i : ZMod p)⁻¹) ^ κ = 0 :=
  (sum_Icc_castZMod (fun x => (x⁻¹) ^ κ)).trans (sum_erase_inv_pow_eq_zero κ hκ1 hκ2)

/-- The "paired" sum used in the Wolstenholme argument. -/
noncomputable def Tsum : ℤ_[p] := ∑ i ∈ Finset.Icc 1 (p - 1), iv i * iv (p - i)

/-- Pairing identity `i⁻¹ + (p-i)⁻¹ = p · (i⁻¹ (p-i)⁻¹)`. -/
lemma pair_term {i : ℕ} (hi1 : 1 ≤ i) (hi2 : i ≤ p - 1) :
    iv i + iv (p - i) = (p : ℤ_[p]) * (iv i * iv (p - i)) := by
  have hip : i ≤ p := by omega
  have hnd : ¬ p ∣ i := fun hd => by have := Nat.le_of_dvd (by omega) hd; omega
  have hnd' : ¬ p ∣ (p - i) := fun hd => by have := Nat.le_of_dvd (by omega) hd; omega
  have ha : (i : ℤ_[p]) * iv i = 1 := mul_iv_cancel hnd
  have hb : ((p - i : ℕ) : ℤ_[p]) * iv (p - i) = 1 := mul_iv_cancel hnd'
  have hab : (i : ℤ_[p]) + ((p - i : ℕ) : ℤ_[p]) = (p : ℤ_[p]) := by
    rw [← Nat.cast_add, Nat.add_sub_cancel' hip]
  linear_combination (-(iv (p - i))) * ha + (-(iv i)) * hb +
    (iv i * iv (p - i)) * hab

/-- Reflection `∑ (p-i)⁻¹ = ∑ i⁻¹`. -/
lemma sum_iv_reflect :
    ∑ i ∈ Finset.Icc 1 (p - 1), iv (p := p) (p - i) = ∑ i ∈ Finset.Icc 1 (p - 1), iv (p := p) i := by
  refine Finset.sum_nbij' (fun i => p - i) (fun i => p - i) ?_ ?_ ?_ ?_ ?_
  · intro a ha; simp only [Finset.mem_Icc] at ha ⊢; omega
  · intro a ha; simp only [Finset.mem_Icc] at ha ⊢; omega
  · intro a ha; simp only [Finset.mem_Icc] at ha; show p - (p - a) = a; omega
  · intro a ha; simp only [Finset.mem_Icc] at ha; show p - (p - a) = a; omega
  · intro a ha; rfl

/-- `2 · Hz 1 = p · Tsum`. -/
lemma two_Hz_one : (2 : ℤ_[p]) * Hz 1 = (p : ℤ_[p]) * Tsum := by
  have hHz : Hz 1 = ∑ i ∈ Finset.Icc 1 (p - 1), iv (p := p) i := by
    rw [Hz]; exact Finset.sum_congr rfl (fun i _ => pow_one _)
  rw [hHz, Tsum]
  calc (2 : ℤ_[p]) * ∑ i ∈ Finset.Icc 1 (p - 1), iv i
      = (∑ i ∈ Finset.Icc 1 (p - 1), iv i) + (∑ i ∈ Finset.Icc 1 (p - 1), iv i) := by
        rw [two_mul]
    _ = (∑ i ∈ Finset.Icc 1 (p - 1), iv i) + (∑ i ∈ Finset.Icc 1 (p - 1), iv (p - i)) := by
        rw [sum_iv_reflect]
    _ = ∑ i ∈ Finset.Icc 1 (p - 1), (iv i + iv (p - i)) := by rw [← Finset.sum_add_distrib]
    _ = ∑ i ∈ Finset.Icc 1 (p - 1), (p : ℤ_[p]) * (iv i * iv (p - i)) :=
        Finset.sum_congr rfl (fun i hi => by
          rw [Finset.mem_Icc] at hi; exact pair_term hi.1 hi.2)
    _ = (p : ℤ_[p]) * ∑ i ∈ Finset.Icc 1 (p - 1), (iv i * iv (p - i)) := by rw [Finset.mul_sum]

/-- `p ∣ Tsum`. -/
lemma dvd_Tsum (hp5 : 5 ≤ p) : (p : ℤ_[p]) ∣ Tsum := by
  apply dvd_of_toZMod_zero
  rw [Tsum, map_sum]
  have hterm : ∀ i ∈ Finset.Icc 1 (p - 1),
      PadicInt.toZMod (iv i * iv (p - i)) = -(((i : ZMod p)⁻¹) ^ 2) := by
    intro i hi
    rw [Finset.mem_Icc] at hi
    have hnd : ¬ p ∣ i := fun hd => by have := Nat.le_of_dvd (by omega) hd; omega
    have hnd' : ¬ p ∣ (p - i) := fun hd => by have := Nat.le_of_dvd (by omega) hd; omega
    rw [map_mul, toZMod_iv hnd, toZMod_iv hnd']
    have hcast : ((p - i : ℕ) : ZMod p) = -(i : ZMod p) := by
      rw [Nat.cast_sub (by omega), ZMod.natCast_self, zero_sub]
    rw [hcast, inv_neg]; ring
  rw [Finset.sum_congr rfl hterm]
  have h0 := sum_Icc_inv_pow_zero (p := p) (κ := 2) (by norm_num) (by omega)
  calc ∑ i ∈ Finset.Icc 1 (p - 1), -(((i : ZMod p)⁻¹) ^ 2)
      = -(∑ i ∈ Finset.Icc 1 (p - 1), ((i : ZMod p)⁻¹) ^ 2) := by rw [Finset.sum_neg_distrib]
    _ = 0 := by rw [h0, neg_zero]

/-- **Wolstenholme (order 2 part):** `p² ∣ Hz 1` for `p ≥ 5`. -/
lemma dvd_sq_Hz_one (hp5 : 5 ≤ p) : (p : ℤ_[p]) ^ 2 ∣ Hz 1 := by
  obtain ⟨s, hs⟩ := dvd_Tsum hp5
  have h2 : (2 : ℤ_[p]) * Hz 1 = (p : ℤ_[p]) ^ 2 * s := by
    rw [two_Hz_one, hs]; ring
  have hu : IsUnit (2 : ℤ_[p]) := by
    rw [PadicInt.isUnit_iff]
    have hcast : ((2 : ℕ) : ℤ_[p]) = 2 := by norm_cast
    rw [← hcast]
    exact norm_cast_eq_one (fun hd => by have := Nat.le_of_dvd (by norm_num) hd; omega)
  obtain ⟨w, hw⟩ := hu.exists_right_inv
  refine ⟨w * s, ?_⟩
  calc Hz 1 = w * ((2 : ℤ_[p]) * Hz 1) := by
        rw [← mul_assoc, mul_comm w (2 : ℤ_[p]), hw, one_mul]
    _ = w * ((p : ℤ_[p]) ^ 2 * s) := by rw [h2]
    _ = (p : ℤ_[p]) ^ 2 * (w * s) := by ring

/-- **Wolstenholme (order 1 part):** `p ∣ Hz 2` for `p ≥ 5`. -/
lemma dvd_Hz_two (hp5 : 5 ≤ p) : (p : ℤ_[p]) ∣ Hz 2 :=
  dvd_Hz (by norm_num) (by omega)

/-! ## The block factor `1 + w t` and the bound `padicLog (w t) ∈ p³ ℤ_[p]` -/

omit hp in
/-- For `p ≥ 5` and `v ≥ 1`, `v + 3 ≤ p^v`. -/
lemma pow_ge (hp5 : 5 ≤ p) : ∀ v : ℕ, 1 ≤ v → v + 3 ≤ p ^ v := by
  intro v
  induction v with
  | zero => intro h; omega
  | succ m ih =>
    intro _
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm; simpa using (by omega : 4 ≤ p)
    · have hih := ih hm
      have hpm : 1 ≤ p ^ m := Nat.one_le_pow _ _ (by omega)
      have hps : p ^ (m + 1) = p * p ^ m := by rw [pow_succ, mul_comm]
      nlinarith [hih, hpm, hps]

omit hp in
/-- For `p ≥ 5` and `κ ≥ 3`, `v_p(κ) ≤ κ - 3`. -/
lemma padicVal_le_sub_three (hp5 : 5 ≤ p) {κ : ℕ} (hκ : 3 ≤ κ) :
    padicValNat p κ ≤ κ - 3 := by
  have hpv : p ^ (padicValNat p κ) ≤ κ := Nat.le_of_dvd (by omega) pow_padicValNat_dvd
  rcases Nat.eq_zero_or_pos (padicValNat p κ) with h0 | hpos
  · omega
  · have := pow_ge hp5 (padicValNat p κ) hpos
    omega

/-- A public copy of the `n`-th term of the log series. -/
noncomputable def logT (x : ℤ_[p]) (n : ℕ) : ℚ_[p] :=
  (-1) ^ n * (x : ℚ_[p]) ^ (n + 1) / (n + 1)

lemma padicLog_eq_logT (x : ℤ_[p]) : padicLog x = ∑' n, logT x n := rfl

lemma summable_logT (x : ℤ_[p]) (hx : ‖x‖ < 1) : Summable (logT x) :=
  summable_logTerm x hx

/-- The block factor `1 + w_t = ∏_{i=1}^{p-1}(1 + t p / i)`, term by term. -/
noncomputable def wfac (t i : ℕ) : ℤ_[p] := (↑(t * p) : ℤ_[p]) * iv i

lemma norm_wfac_le (t i : ℕ) : ‖(wfac t i : ℤ_[p])‖ ≤ (p : ℝ)⁻¹ := by
  rw [wfac, norm_mul]
  calc ‖(↑(t * p) : ℤ_[p])‖ * ‖iv i‖
      ≤ ‖(↑(t * p) : ℤ_[p])‖ * 1 :=
        mul_le_mul_of_nonneg_left (PadicInt.norm_le_one _) (norm_nonneg _)
    _ = ‖(↑(t * p) : ℤ_[p])‖ := mul_one _
    _ ≤ (p : ℝ)⁻¹ := by
        rw [Nat.cast_mul, norm_mul, ← PadicInt.norm_p (p := p)]
        exact mul_le_of_le_one_left (norm_nonneg _) (PadicInt.norm_le_one _)

lemma norm_wfac_lt (hp5 : 5 ≤ p) (t i : ℕ) : ‖(wfac t i : ℤ_[p])‖ < 1 := by
  refine lt_of_le_of_lt (norm_wfac_le t i) ?_
  rw [inv_lt_one₀ (by exact_mod_cast hp.out.pos)]
  exact_mod_cast (by omega : 1 < p)

lemma coe_wfac {t i : ℕ} (h : ¬ p ∣ i) :
    ((wfac t i : ℤ_[p]) : ℚ_[p]) = (↑(t * p) : ℚ_[p]) * (↑i)⁻¹ := by
  rw [wfac]
  push_cast [coe_iv h]
  ring

/-- `1 + w t = ∏_i (1 + wfac t i)`. -/
noncomputable def oneAddW (t : ℕ) : ℤ_[p] := ∏ i ∈ Finset.Icc 1 (p - 1), (1 + wfac t i)

/-- `w t = ∏_i (1 + wfac t i) - 1`. -/
noncomputable def w (t : ℕ) : ℤ_[p] := oneAddW t - 1

lemma coe_Hz (κ : ℕ) :
    ((Hz κ : ℤ_[p]) : ℚ_[p]) = ∑ i ∈ Finset.Icc 1 (p - 1), ((↑i : ℚ_[p])⁻¹) ^ κ := by
  rw [Hz, PadicInt.coe_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_Icc] at hi
  have hnd : ¬ p ∣ i := fun hd => by have := Nat.le_of_dvd (by omega) hd; omega
  rw [PadicInt.coe_pow, coe_iv hnd]

/-- Regrouped `n`-th term of `∑_i padicLog (wfac t i)`, with the harmonic sum factored out. -/
lemma term_val (t n : ℕ) :
    ∑ i ∈ Finset.Icc 1 (p - 1), logT (wfac t i) n
      = (-1) ^ n * (↑(t * p) : ℚ_[p]) ^ (n + 1) / ((n : ℚ_[p]) + 1) * ((Hz (n + 1) : ℤ_[p]) : ℚ_[p]) := by
  rw [coe_Hz, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_Icc] at hi
  have hnd : ¬ p ∣ i := fun hd => by have := Nat.le_of_dvd (by omega) hd; omega
  rw [logT, coe_wfac hnd, mul_pow]
  ring

/-- `‖(t p : ℚ_[p])‖ ≤ p⁻¹`. -/
lemma norm_natCast_tp_le (t : ℕ) : ‖(↑(t * p) : ℚ_[p])‖ ≤ (p : ℝ)⁻¹ := by
  rw [← PadicInt.coe_natCast, PadicInt.padic_norm_e_of_padicInt]
  rw [Nat.cast_mul, norm_mul, ← PadicInt.norm_p (p := p)]
  exact mul_le_of_le_one_left (norm_nonneg _) (PadicInt.norm_le_one _)

/-- `‖n+1‖⁻¹ = p^{v_p(n+1)}`. -/
lemma norm_natCast_succ_inv (n : ℕ) :
    ‖((n : ℚ_[p]) + 1)‖⁻¹ = (p : ℝ) ^ (padicValNat p (n + 1) : ℤ) := by
  have hm0 : ((n + 1 : ℕ) : ℚ_[p]) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have hcast : ((n : ℚ_[p]) + 1) = ((n + 1 : ℕ) : ℚ_[p]) := by push_cast; ring
  rw [hcast, Padic.norm_eq_zpow_neg_valuation hm0, Padic.valuation_natCast,
    zpow_neg, inv_inv]

/-- `‖Hz 1‖ ≤ p^{-2}`. -/
lemma norm_Hz_one_le (hp5 : 5 ≤ p) : ‖(Hz 1 : ℤ_[p])‖ ≤ (p : ℝ) ^ (-2 : ℤ) := by
  have := (dvd_iff_norm_le (Hz 1) 2).mp (dvd_sq_Hz_one hp5)
  simpa using this

/-- `‖Hz 2‖ ≤ p^{-1}`. -/
lemma norm_Hz_two_le (hp5 : 5 ≤ p) : ‖(Hz 2 : ℤ_[p])‖ ≤ (p : ℝ) ^ (-1 : ℤ) := by
  have hd : (p : ℤ_[p]) ^ 1 ∣ Hz 2 := by rw [pow_one]; exact dvd_Hz_two hp5
  have := (dvd_iff_norm_le (Hz 2) 1).mp hd
  simpa using this

/-- The core `p^{-3}` estimate on the harmonic-weighted power factor. -/
lemma harmonic_factor_bound (hp5 : 5 ≤ p) (n : ℕ) :
    (p : ℝ) ^ (-(↑(n + 1)) : ℤ) * (p : ℝ) ^ (padicValNat p (n + 1) : ℤ) * ‖(Hz (n + 1) : ℤ_[p])‖
      ≤ (p : ℝ) ^ (-3 : ℤ) := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.out.one_le
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  set v : ℤ := (padicValNat p (n + 1) : ℤ) with hv
  -- combine the two powers of p
  have hcomb : (p : ℝ) ^ (-(↑(n + 1)) : ℤ) * (p : ℝ) ^ v
      = (p : ℝ) ^ (v - (↑(n + 1))) := by
    rw [← zpow_add₀ (ne_of_gt hp0)]; ring_nf
  rw [hcomb]
  match n, (rfl : n = n) with
  | 0, _ =>
    have hH : ‖(Hz 1 : ℤ_[p])‖ ≤ (p : ℝ) ^ (-2 : ℤ) := norm_Hz_one_le hp5
    have hvv : v = 0 := by rw [hv]; norm_num [padicValNat.one]
    calc (p : ℝ) ^ (v - (↑(0 + 1))) * ‖(Hz (0 + 1) : ℤ_[p])‖
        ≤ (p : ℝ) ^ (v - (↑(0 + 1))) * (p : ℝ) ^ (-2 : ℤ) := by
          apply mul_le_mul_of_nonneg_left hH (by positivity)
      _ = (p : ℝ) ^ (-3 : ℤ) := by
          rw [← zpow_add₀ (ne_of_gt hp0)]; rw [hvv]; norm_num
  | 1, _ =>
    have hH : ‖(Hz 2 : ℤ_[p])‖ ≤ (p : ℝ) ^ (-1 : ℤ) := norm_Hz_two_le hp5
    have hvv : v = 0 := by
      have h2 : padicValNat p 2 = 0 :=
        padicValNat.eq_zero_of_not_dvd (fun hd => by have := Nat.le_of_dvd (by norm_num) hd; omega)
      rw [hv]; norm_num [h2]
    calc (p : ℝ) ^ (v - (↑(1 + 1))) * ‖(Hz (1 + 1) : ℤ_[p])‖
        ≤ (p : ℝ) ^ (v - (↑(1 + 1))) * (p : ℝ) ^ (-1 : ℤ) := by
          apply mul_le_mul_of_nonneg_left hH (by positivity)
      _ = (p : ℝ) ^ (-3 : ℤ) := by
          rw [← zpow_add₀ (ne_of_gt hp0)]; rw [hvv]; norm_num
  | (m + 2), _ =>
    have hH : ‖(Hz (m + 2 + 1) : ℤ_[p])‖ ≤ 1 := norm_Hz_le_one _
    have hexp : v - (↑(m + 2 + 1)) ≤ (-3 : ℤ) := by
      have hle : padicValNat p (m + 2 + 1) ≤ (m + 2 + 1) - 3 :=
        padicVal_le_sub_three hp5 (by omega)
      rw [hv]; omega
    calc (p : ℝ) ^ (v - (↑(m + 2 + 1))) * ‖(Hz (m + 2 + 1) : ℤ_[p])‖
        ≤ (p : ℝ) ^ (v - (↑(m + 2 + 1))) * 1 := by
          apply mul_le_mul_of_nonneg_left hH (by positivity)
      _ = (p : ℝ) ^ (v - (↑(m + 2 + 1))) := mul_one _
      _ ≤ (p : ℝ) ^ (-3 : ℤ) := zpow_le_zpow_right₀ hp1 hexp

/-- Each regrouped term has norm `≤ p^{-3}`. -/
lemma norm_term_le (hp5 : 5 ≤ p) (t n : ℕ) :
    ‖∑ i ∈ Finset.Icc 1 (p - 1), logT (wfac (p := p) t i) n‖ ≤ (p : ℝ) ^ (-3 : ℤ) := by
  rw [term_val]
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hnorm : ‖(-1 : ℚ_[p]) ^ n * (↑(t * p)) ^ (n + 1) / ((n : ℚ_[p]) + 1) *
        ((Hz (n + 1) : ℤ_[p]) : ℚ_[p])‖
      = ‖(↑(t * p) : ℚ_[p])‖ ^ (n + 1) * ‖((n : ℚ_[p]) + 1)‖⁻¹ * ‖(Hz (n + 1) : ℤ_[p])‖ := by
    rw [norm_mul, norm_div, norm_mul, norm_pow, norm_pow, norm_neg, norm_one, one_pow,
        one_mul, PadicInt.padic_norm_e_of_padicInt, div_eq_mul_inv]
  rw [hnorm, norm_natCast_succ_inv]
  -- now bound
  have hApow : ‖(↑(t * p) : ℚ_[p])‖ ^ (n + 1) ≤ (p : ℝ) ^ (-(↑(n + 1)) : ℤ) := by
    refine le_trans (pow_le_pow_left₀ (norm_nonneg _) (norm_natCast_tp_le t) (n + 1)) ?_
    rw [inv_pow, ← zpow_natCast (p : ℝ) (n + 1), ← zpow_neg]
  calc ‖(↑(t * p) : ℚ_[p])‖ ^ (n + 1) * (p : ℝ) ^ (padicValNat p (n + 1) : ℤ) *
        ‖(Hz (n + 1) : ℤ_[p])‖
      ≤ (p : ℝ) ^ (-(↑(n + 1)) : ℤ) * (p : ℝ) ^ (padicValNat p (n + 1) : ℤ) *
          ‖(Hz (n + 1) : ℤ_[p])‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        apply mul_le_mul_of_nonneg_right hApow (by positivity)
    _ ≤ (p : ℝ) ^ (-3 : ℤ) := harmonic_factor_bound hp5 n

/-- **Key bound:** `padicLog (w t) ∈ p³ ℤ_[p]`, i.e. `‖padicLog (w t)‖ ≤ p^{-3}`. -/
lemma norm_padicLog_w_le (hp5 : 5 ≤ p) (t : ℕ) :
    ‖padicLog (w (p := p) t)‖ ≤ (p : ℝ) ^ (-3 : ℤ) := by
  have hp3 : 3 ≤ p := by omega
  have hwfac_lt : ∀ i ∈ Finset.Icc 1 (p - 1), ‖(wfac t i : ℤ_[p])‖ < 1 :=
    fun i _ => norm_wfac_lt hp5 t i
  have hlog : padicLog (w (p := p) t) = ∑ i ∈ Finset.Icc 1 (p - 1), padicLog (wfac t i) := by
    rw [w, oneAddW]; exact padicLog_prod hp3 _ _ hwfac_lt
  have hsummable : ∀ i ∈ Finset.Icc 1 (p - 1), Summable (fun n => logT (wfac t i) n) :=
    fun i _ => summable_logT (wfac t i) (norm_wfac_lt hp5 t i)
  have hlog2 : padicLog (w (p := p) t)
      = ∑' n, ∑ i ∈ Finset.Icc 1 (p - 1), logT (wfac t i) n := by
    rw [hlog,
      show (∑ i ∈ Finset.Icc 1 (p - 1), padicLog (wfac t i))
          = ∑ i ∈ Finset.Icc 1 (p - 1), ∑' n, logT (wfac t i) n from
        Finset.sum_congr rfl (fun i _ => padicLog_eq_logT _)]
    exact (Summable.tsum_finsetSum hsummable).symm
  rw [hlog2]
  exact IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (by positivity)
    (fun n => norm_term_le hp5 t n)

/-! ## The p-free factorial `W(m)` and its block decomposition -/

/-- `(p-1)!` in `ℤ_[p]`. -/
noncomputable def factp : ℤ_[p] := ∏ i ∈ Finset.Icc 1 (p - 1), (↑i : ℤ_[p])

/-- The `t`-th block product `∏_{i=1}^{p-1} (t p + i)`. -/
noncomputable def Pblock (t : ℕ) : ℤ_[p] := ∏ i ∈ Finset.Icc 1 (p - 1), (↑(t * p + i) : ℤ_[p])

/-- `W(m) = ∏_{1 ≤ j ≤ m, p ∤ j} j`. -/
noncomputable def Wfac (m : ℕ) : ℤ_[p] :=
  ∏ j ∈ (Finset.Icc 1 m).filter (fun j => ¬ p ∣ j), (↑j : ℤ_[p])

lemma norm_factp : ‖(factp : ℤ_[p])‖ = 1 := by
  rw [factp, norm_prod]
  apply Finset.prod_eq_one
  intro i hi
  rw [Finset.mem_Icc] at hi
  exact norm_cast_eq_one (fun hd => by have := Nat.le_of_dvd (by omega) hd; omega)

lemma isUnit_factp : IsUnit (factp : ℤ_[p]) := PadicInt.isUnit_iff.mpr norm_factp

lemma Pblock_eq (t : ℕ) : (Pblock t : ℤ_[p]) = factp * oneAddW t := by
  rw [factp, oneAddW, ← Finset.prod_mul_distrib, Pblock]
  apply Finset.prod_congr rfl
  intro i hi
  rw [Finset.mem_Icc] at hi
  have hnd : ¬ p ∣ i := fun hd => by have := Nat.le_of_dvd (by omega) hd; omega
  rw [wfac]
  push_cast
  have hiv : (↑i : ℤ_[p]) * iv i = 1 := mul_iv_cancel hnd
  linear_combination (-((t : ℤ_[p]) * (p : ℤ_[p]))) * hiv

/-- **Block decomposition:** `W(p·N) = ∏_{t<N} Pblock t`. -/
lemma Wfac_block (N : ℕ) : (Wfac (p * N) : ℤ_[p]) = ∏ t ∈ Finset.range N, Pblock t := by
  have hp0 : 0 < p := hp.out.pos
  rw [Wfac, Nat.mul_comm p N]
  simp only [Pblock]
  rw [← Finset.prod_product']
  refine (Finset.prod_nbij' (fun x => x.1 * p + x.2) (fun n => (n / p, n % p)) ?_ ?_ ?_ ?_ ?_).symm
  · rintro ⟨t, i⟩ hx
    simp only [Finset.mem_product, Finset.mem_range, Finset.mem_Icc] at hx
    obtain ⟨ht, hi1, hi2⟩ := hx
    simp only [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨by omega, ?_⟩, ?_⟩
    · have hbound : (t + 1) * p ≤ N * p := mul_le_mul_right' (by omega) p
      have : t * p + p ≤ N * p := by rw [add_mul, one_mul] at hbound; exact hbound
      omega
    · intro hd
      have hpi : p ∣ i := (Nat.dvd_add_right (dvd_mul_left p t)).mp hd
      have := Nat.le_of_dvd (by omega) hpi
      omega
  · rintro n hn
    simp only [Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨hn1, hn2⟩, hnd⟩ := hn
    simp only [Finset.mem_product, Finset.mem_range, Finset.mem_Icc]
    have hmod : n % p ≠ 0 := fun h => hnd (Nat.dvd_of_mod_eq_zero h)
    have hmodlt : n % p < p := Nat.mod_lt n hp0
    refine ⟨?_, ?_, ?_⟩
    · rw [Nat.div_lt_iff_lt_mul hp0]
      rcases lt_or_eq_of_le hn2 with hlt | heq
      · exact hlt
      · exact absurd (heq.symm ▸ dvd_mul_left p N) hnd
    · omega
    · omega
  · rintro ⟨t, i⟩ hx
    simp only [Finset.mem_product, Finset.mem_range, Finset.mem_Icc] at hx
    obtain ⟨ht, hi1, hi2⟩ := hx
    have hmod : (t * p + i) % p = i := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right]; exact Nat.mod_eq_of_lt (by omega)
    have hdiv : (t * p + i) / p = t := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hp0, Nat.div_eq_of_lt (by omega), zero_add]
    simp [hmod, hdiv]
  · rintro n hn
    show n / p * p + n % p = n
    rw [Nat.mul_comm (n / p) p]
    exact Nat.div_add_mod n p
  · rintro ⟨t, i⟩ _; rfl

/-! ## Final assembly: the balanced supercongruence mod `p³` -/

/-- Ultrametric triangle inequality for subtraction in `ℤ_[p]`. -/
lemma norm_sub_le_max' (a b : ℤ_[p]) : ‖a - b‖ ≤ max ‖a‖ ‖b‖ := by
  rw [sub_eq_add_neg]
  refine (IsUltrametricDist.norm_add_le_max a (-b)).trans ?_
  rw [norm_neg]

lemma norm_w_lt (hp5 : 5 ≤ p) (t : ℕ) : ‖(w (p := p) t)‖ < 1 := by
  rw [w, oneAddW]
  exact norm_prod_one_add_sub_one_lt _ _ (fun i _ => norm_wfac_lt hp5 t i)

/-- The product over a family `s` of `∏_{t < cnt a} (1 + w t)`, i.e. the analytic
part of `∏ W(c_a · W)`. -/
noncomputable def Aprod {ι : Type*} (s : Finset ι) (cnt : ι → ℕ) : ℤ_[p] :=
  ∏ a ∈ s, ∏ t ∈ Finset.range (cnt a), oneAddW t

lemma Aprod_eq_sigma {ι : Type*} (s : Finset ι) (cnt : ι → ℕ) :
    Aprod (p := p) s cnt = ∏ x ∈ s.sigma (fun a => Finset.range (cnt a)), (1 + w (p := p) x.2) := by
  rw [Aprod, Finset.prod_sigma]
  apply Finset.prod_congr rfl
  intro a _
  apply Finset.prod_congr rfl
  intro t _
  rw [w]; ring

lemma padicLog_Aprod (hp5 : 5 ≤ p) {ι : Type*} (s : Finset ι) (cnt : ι → ℕ) :
    padicLog (Aprod (p := p) s cnt - 1)
      = ∑ x ∈ s.sigma (fun a => Finset.range (cnt a)), padicLog (w (p := p) x.2) := by
  rw [Aprod_eq_sigma]
  exact padicLog_prod (by omega) _ _ (fun x _ => norm_w_lt hp5 x.2)

lemma norm_Aprod_sub_one_lt (hp5 : 5 ≤ p) {ι : Type*} (s : Finset ι) (cnt : ι → ℕ) :
    ‖Aprod (p := p) s cnt - 1‖ < 1 := by
  rw [Aprod_eq_sigma]
  exact norm_prod_one_add_sub_one_lt _ _ (fun x _ => norm_w_lt hp5 x.2)

lemma norm_padicLog_Aprod_le (hp5 : 5 ≤ p) {ι : Type*} (s : Finset ι) (cnt : ι → ℕ) :
    ‖padicLog (Aprod (p := p) s cnt - 1)‖ ≤ (p : ℝ) ^ (-3 : ℤ) := by
  rw [padicLog_Aprod hp5]
  exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)
    (fun x _ => norm_padicLog_w_le hp5 x.2)

/-- If `u, v` are close to `1` and their logs are both divisible by `p³`, then `p³ ∣ u - v`. -/
lemma dvd_sub_of_logs (hp5 : 5 ≤ p) (u v : ℤ_[p])
    (hu : ‖u - 1‖ < 1) (hv : ‖v - 1‖ < 1)
    (hlu : ‖padicLog (u - 1)‖ ≤ (p : ℝ) ^ (-3 : ℤ))
    (hlv : ‖padicLog (v - 1)‖ ≤ (p : ℝ) ^ (-3 : ℤ)) :
    (p : ℤ_[p]) ^ 3 ∣ (u - v) := by
  have hp3 : 3 ≤ p := by omega
  -- v is a unit
  have hvnorm : ‖v‖ = 1 := by
    have : ‖v‖ = ‖(v - 1) + 1‖ := by ring_nf
    rw [this]
    have h1 : ‖((1 : ℤ_[p]))‖ = 1 := norm_one
    have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm
      (x := v - 1) (y := (1 : ℤ_[p])) (by rw [h1]; exact ne_of_lt hv)
    rw [this, h1]
    exact max_eq_right (le_of_lt hv)
  set vinv : ℤ_[p] := PadicInt.inv v with hvinv
  have hvvinv : v * vinv = 1 := PadicInt.mul_inv hvnorm
  set r : ℤ_[p] := u * vinv with hr
  -- r - 1 = (u - v) * vinv
  have hrsub : r - 1 = (u - v) * vinv := by
    rw [hr]
    have : u * vinv - 1 = u * vinv - v * vinv := by rw [hvvinv]
    rw [this]; ring
  have hvinv_norm : ‖vinv‖ = 1 := by
    have := congrArg norm hvvinv
    rw [norm_mul, hvnorm, one_mul, norm_one] at this
    exact this
  have huvnorm : ‖u - v‖ < 1 := by
    calc ‖u - v‖ = ‖(u - 1) - (v - 1)‖ := by ring_nf
      _ ≤ max ‖u - 1‖ ‖v - 1‖ := norm_sub_le_max' _ _
      _ < 1 := max_lt hu hv
  have hrsubnorm : ‖r - 1‖ < 1 := by
    rw [hrsub, norm_mul, hvinv_norm, mul_one]; exact huvnorm
  -- padicLog r = padicLog u - padicLog v via padicLog_mul with x=r-1, y=v-1
  have hrv : r * v = u := by rw [hr]; rw [mul_assoc, mul_comm vinv v, hvvinv, mul_one]
  have hmul := padicLog_mul hp3 (r - 1) (v - 1) hrsubnorm hv
  have hexp : (r - 1) + (v - 1) + (r - 1) * (v - 1) = r * v - 1 := by ring
  rw [hexp, hrv] at hmul
  -- so padicLog (u - 1) = padicLog (r - 1) + padicLog (v - 1)
  have hlogr : padicLog (r - 1) = padicLog (u - 1) - padicLog (v - 1) := by
    rw [hmul]; ring
  have hlogr_le : ‖padicLog (r - 1)‖ ≤ (p : ℝ) ^ (-3 : ℤ) := by
    rw [hlogr]
    calc ‖padicLog (u - 1) - padicLog (v - 1)‖
        ≤ max ‖padicLog (u - 1)‖ ‖padicLog (v - 1)‖ := by
          rw [sub_eq_add_neg]
          exact (IsUltrametricDist.norm_add_le_max _ _).trans (by rw [norm_neg])
      _ ≤ (p : ℝ) ^ (-3 : ℤ) := max_le hlu hlv
  have hdvd : (p : ℤ_[p]) ^ 3 ∣ (r - 1) :=
    sub_one_dvd_of_padicLog hp3 r hrsubnorm 3 (by simpa using hlogr_le)
  -- u - v = (r - 1) * v
  have huv : u - v = (r - 1) * v := by
    rw [hrsub, mul_assoc]
    rw [show vinv * v = 1 from by rw [mul_comm]; exact hvvinv, mul_one]
  rw [huv]
  exact hdvd.mul_right v

/-- `∏_{i∈s} W(c_i · W) = factp^(∑ c_i M') · Aprod s (c · M')` when `W = p · M'`. -/
lemma Wprod_eq {ι : Type*} (Wn M' : ℕ) (hWeq : Wn = p * M')
    (s : Finset ι) (c : ι → ℕ) :
    (∏ i ∈ s, Wfac (c i * Wn))
      = (factp : ℤ_[p]) ^ (∑ i ∈ s, c i * M') * Aprod (p := p) s (fun i => c i * M') := by
  rw [Aprod, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  have hci : c i * Wn = p * (c i * M') := by rw [hWeq]; ring
  rw [hci, Wfac_block]
  rw [show (∏ t ∈ Finset.range (c i * M'), Pblock t)
      = ∏ t ∈ Finset.range (c i * M'), (factp * oneAddW t) from
    Finset.prod_congr rfl (fun t _ => Pblock_eq t)]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]

/-- **Balanced supercongruence (mod `p³`).**
For a prime `p ≥ 5`, positive coefficients `c`, sign split into `num`/`den`, `p ∣ W`
and balanced condition `∑_num c = ∑_den c`, we have
`p³ ∣ (∏_{num} W(c_i·W) - ∏_{den} W(c_i·W))`. -/
theorem balanced_supercongruence (hp5 : 5 ≤ p) {ι : Type*}
    (num den : Finset ι) (c : ι → ℕ) (Wn : ℕ) (hW : p ∣ Wn)
    (hbal : ∑ i ∈ num, c i = ∑ i ∈ den, c i) :
    (p : ℤ_[p]) ^ 3 ∣ ((∏ i ∈ num, Wfac (c i * Wn)) - (∏ i ∈ den, Wfac (c i * Wn))) := by
  obtain ⟨M', hWeq⟩ := hW
  rw [Wprod_eq Wn M' hWeq num c, Wprod_eq Wn M' hWeq den c]
  have hexp : (∑ i ∈ num, c i * M') = (∑ i ∈ den, c i * M') := by
    rw [← Finset.sum_mul, ← Finset.sum_mul, hbal]
  rw [hexp, ← mul_sub]
  have hdvd : (p : ℤ_[p]) ^ 3 ∣ (Aprod num (fun i => c i * M') - Aprod den (fun i => c i * M')) :=
    dvd_sub_of_logs hp5 _ _
      (norm_Aprod_sub_one_lt hp5 _ _) (norm_Aprod_sub_one_lt hp5 _ _)
      (norm_padicLog_Aprod_le hp5 _ _) (norm_padicLog_Aprod_le hp5 _ _)
  exact hdvd.mul_left _

end PKaz

#print axioms PKaz.balanced_supercongruence
#print axioms PKaz.dvd_sq_Hz_one
#print axioms PKaz.dvd_Hz_two
#print axioms PKaz.norm_padicLog_w_le
#print axioms PKaz.Wfac_block
