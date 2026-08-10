import FormalConjectures.Util.ProblemImports

open Nat Finset BigOperators

namespace Sun

/- ============================================================
   Building block: harmonic-type sums mod p
   ============================================================ -/

variable {p : ℕ}

/-- Sum of `x^s` over all of `ZMod p` is 0 when `0 < s < p - 1`. -/
theorem sum_pow_zmod [Fact p.Prime] (s : ℕ) (h : s < p - 1) :
    ∑ x : ZMod p, x ^ s = 0 := by
  have hc : Fintype.card (ZMod p) = p := ZMod.card p
  apply FiniteField.sum_pow_lt_card_sub_one
  rw [hc]; exact h

/-- Harmonic sum mod p: `∑_{x} (x⁻¹)^s = 0` for `1 ≤ s < p-1`. -/
theorem harmonic_modp [Fact p.Prime] (s : ℕ) (hs2 : s < p - 1) :
    ∑ x : ZMod p, (x⁻¹)^s = 0 := by
  have h1 : ∑ x : ZMod p, (x⁻¹)^s = ∑ x : ZMod p, x^s := by
    have h := Equiv.sum_comp (Function.Involutive.toPerm (Inv.inv : ZMod p → ZMod p) inv_inv)
      (fun y => y^s)
    simpa [Function.Involutive.coe_toPerm] using h
  rw [h1]; exact sum_pow_zmod s hs2

/-- Convert a sum over `ZMod p` into a sum over `range p` via the natural cast. -/
theorem zmod_sum_range {M : Type*} [AddCommMonoid M] [NeZero p] (f : ZMod p → M) :
    ∑ x : ZMod p, f x = ∑ r ∈ Finset.range p, f (r : ZMod p) := by
  apply Finset.sum_nbij' (i := fun x : ZMod p => x.val) (j := fun r : ℕ => (r : ZMod p))
  · intro a _; simp [Finset.mem_range, ZMod.val_lt]
  · intro b _; exact Finset.mem_univ _
  · intro a _; exact ZMod.natCast_rightInverse a
  · intro b hb; exact ZMod.val_cast_of_lt (Finset.mem_range.mp hb)
  · intro a _; rw [ZMod.natCast_rightInverse a]

/-- `Icc 1 (p-1)` form: sum of `f` over `range p` equals `f 0 + ` sum over `Icc 1 (p-1)`. -/
theorem sum_range_eq_icc {M : Type*} [AddCommMonoid M] (hp : 0 < p) (g : ℕ → M) :
    ∑ r ∈ Finset.range p, g r = g 0 + ∑ r ∈ Finset.Icc 1 (p-1), g r := by
  have : Finset.range p = insert 0 (Finset.Icc 1 (p-1)) := by
    ext x
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  rw [this, Finset.sum_insert (by simp)]

/-- `Icc`-form harmonic sum mod p: `∑_{r=1}^{p-1} (r⁻¹)^s = 0` for `1 ≤ s < p-1`. -/
theorem harmonic_modp_icc [Fact p.Prime] (s : ℕ) (hs1 : 1 ≤ s) (hs2 : s < p - 1) :
    ∑ r ∈ Finset.Icc 1 (p-1), (((r : ZMod p))⁻¹)^s = 0 := by
  have hp : 0 < p := (Fact.out (p := p.Prime)).pos
  have hne : NeZero p := ⟨hp.ne'⟩
  have h := harmonic_modp s hs2
  rw [zmod_sum_range (fun x : ZMod p => (x⁻¹)^s)] at h
  rw [sum_range_eq_icc hp (fun r => (((r : ZMod p))⁻¹)^s)] at h
  simp only [Nat.cast_zero, inv_zero] at h
  rw [zero_pow (by omega : s ≠ 0), zero_add] at h
  exact h

/- ============================================================
   Wolstenholme mod p^2
   ============================================================ -/

/-- For `T : ZMod (p^2)` whose reduction mod `p` is `0`, we have `p * T = 0`. -/
theorem p_mul_eq_zero_of_castHom_zero (hp : 0 < p) (T : ZMod (p^2))
    (h : (ZMod.castHom (dvd_pow_self p (two_ne_zero)) (ZMod p)) T = 0) :
    (p : ZMod (p^2)) * T = 0 := by
  have hne : NeZero p := ⟨hp.ne'⟩
  have hpd : p ∣ T.val := by
    rw [ZMod.castHom_apply, ← ZMod.natCast_val, ZMod.natCast_eq_zero_iff] at h
    exact h
  obtain ⟨c, hc⟩ := hpd
  have e1 : (p : ZMod (p^2)) * T = ((p * T.val : ℕ) : ZMod (p^2)) := by
    rw [Nat.cast_mul, ZMod.natCast_zmod_val]
  rw [e1, hc]
  have e2 : p * (p * c) = p^2 * c := by ring
  rw [e2, Nat.cast_mul, ZMod.natCast_self, zero_mul]

/-- The natural reduction `ZMod (p^2) → ZMod p` as a ring hom. -/
local notation "red₂" => (ZMod.castHom (dvd_pow_self p (two_ne_zero)) (ZMod p))

/-- `(jp + r)` is a unit in `ZMod (p^2)` when `1 ≤ r ≤ p-1`. -/
theorem isUnit_jp_add [Fact p.Prime] (j r : ℕ) (hr1 : 1 ≤ r) (hr2 : r ≤ p - 1) :
    IsUnit ((j * p + r : ℕ) : ZMod (p^2)) := by
  rw [ZMod.isUnit_iff_coprime]
  have hpp : p.Prime := Fact.out
  have hrp : ¬ p ∣ (j * p + r) := by
    intro hd
    have : p ∣ r := (Nat.dvd_add_right ⟨j, by ring⟩).mp hd
    have := Nat.le_of_dvd (by omega) this
    omega
  have hcop : Nat.Coprime (j * p + r) p := (hpp.coprime_iff_not_dvd.mpr hrp).symm
  exact hcop.pow_right 2

/-- `r` is a unit in `ZMod (p^2)` for `1 ≤ r ≤ p-1`. -/
theorem isUnit_cast [Fact p.Prime] (r : ℕ) (h1 : 1 ≤ r) (h2 : r ≤ p - 1) :
    IsUnit ((r : ℕ) : ZMod (p^2)) := by
  have := isUnit_jp_add 0 r h1 h2
  simpa using this

/-- pairing identity for inverses of units `a, b` in a comm ring with `ZMod`-style inverse. -/
theorem inv_add_inv_of_units (a b : ZMod (p^2)) (ha : IsUnit a) (hb : IsUnit b) :
    a⁻¹ + b⁻¹ = (a + b) * (a * b)⁻¹ := by
  have hmul : (a * b) * (a⁻¹ * b⁻¹) = 1 := by
    have e : (a * b) * (a⁻¹ * b⁻¹) = (a * a⁻¹) * (b * b⁻¹) := by ring
    rw [e, ZMod.mul_inv_of_unit _ ha, ZMod.mul_inv_of_unit _ hb, mul_one]
  have hinv : (a * b)⁻¹ = a⁻¹ * b⁻¹ := ZMod.inv_eq_of_mul_eq_one (p^2) _ _ hmul
  rw [hinv]
  have e1 : (a + b) * (a⁻¹ * b⁻¹) = b⁻¹ * (a * a⁻¹) + a⁻¹ * (b * b⁻¹) := by ring
  rw [e1, ZMod.mul_inv_of_unit _ ha, ZMod.mul_inv_of_unit _ hb, mul_one, mul_one, add_comm]

/-- The reduction `red₂` preserves inverses of units. -/
theorem red₂_inv [Fact p.Prime] (x : ZMod (p^2)) (hx : IsUnit x) :
    red₂ (x⁻¹) = (red₂ x)⁻¹ := by
  have h1 : red₂ x * red₂ (x⁻¹) = 1 := by
    rw [← map_mul, ZMod.mul_inv_of_unit _ hx, map_one]
  exact (ZMod.inv_eq_of_mul_eq_one p _ _ h1).symm

/-- `2` is a unit in `ZMod (p^2)` for odd prime `p`. -/
theorem isUnit_two [Fact p.Prime] (hp5 : 5 ≤ p) : IsUnit (2 : ZMod (p^2)) := by
  have hpp : p.Prime := Fact.out
  rw [show (2 : ZMod (p^2)) = ((2 : ℕ) : ZMod (p^2)) by norm_num, ZMod.isUnit_iff_coprime]
  have : Nat.Coprime 2 p := by
    rw [Nat.coprime_primes Nat.prime_two hpp]; omega
  exact this.pow_right 2

/-- Basic Wolstenholme: `∑_{r=1}^{p-1} r⁻¹ = 0` in `ZMod (p^2)`. -/
theorem wolstenholme_two [Fact p.Prime] (hp5 : 5 ≤ p) :
    ∑ r ∈ Finset.Icc 1 (p-1), (((r : ℕ) : ZMod (p^2)))⁻¹ = 0 := by
  have hpp : p.Prime := Fact.out
  have hp0 : 0 < p := hpp.pos
  set S := ∑ r ∈ Finset.Icc 1 (p-1), (((r : ℕ) : ZMod (p^2)))⁻¹ with hSdef
  -- reflection r ↦ p - r
  have hrefl : S = ∑ r ∈ Finset.Icc 1 (p-1), ((((p - r : ℕ)) : ZMod (p^2)))⁻¹ := by
    apply Finset.sum_nbij' (i := fun r => p - r) (j := fun r => p - r)
    · intro a ha; simp only [Finset.mem_Icc] at *; omega
    · intro a ha; simp only [Finset.mem_Icc] at *; omega
    · intro a ha; simp only [Finset.mem_Icc] at ha; omega
    · intro a ha; simp only [Finset.mem_Icc] at ha; omega
    · intro a ha; simp only [Finset.mem_Icc] at ha
      have : p - (p - a) = a := by omega
      rw [this]
  -- T : the paired sum
  set T := ∑ r ∈ Finset.Icc 1 (p-1),
      ((((r : ℕ) : ZMod (p^2)) * (((p - r : ℕ)) : ZMod (p^2))))⁻¹ with hTdef
  have h2S : 2 * S = (p : ZMod (p^2)) * T := by
    have : S + S = ∑ r ∈ Finset.Icc 1 (p-1),
        ((((r : ℕ) : ZMod (p^2)))⁻¹ + ((((p - r : ℕ)) : ZMod (p^2)))⁻¹) := by
      rw [Finset.sum_add_distrib, ← hrefl]
    rw [two_mul, this, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    simp only [Finset.mem_Icc] at hr
    have hru : IsUnit (((r : ℕ) : ZMod (p^2))) := by
      exact isUnit_cast r hr.1 hr.2
    have hpru : IsUnit ((((p - r : ℕ)) : ZMod (p^2))) := by
      exact isUnit_cast (p - r) (by omega) (by omega)
    rw [inv_add_inv_of_units _ _ hru hpru]
    congr 1
    rw [← Nat.cast_add]
    have : r + (p - r) = p := by omega
    rw [this]
  -- reduce T mod p is zero
  have hTred : red₂ T = 0 := by
    rw [hTdef, map_sum]
    rw [show (0 : ZMod p) = -(∑ r ∈ Finset.Icc 1 (p-1), ((((r:ℕ):ZMod p))⁻¹)^2) by
        rw [harmonic_modp_icc 2 (by norm_num) (by omega)]; ring]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro r hr
    simp only [Finset.mem_Icc] at hr
    have hru : IsUnit (((r : ℕ) : ZMod (p^2)) * (((p - r : ℕ)) : ZMod (p^2))) := by
      apply IsUnit.mul
      · exact isUnit_cast r hr.1 hr.2
      · exact isUnit_cast (p - r) (by omega) (by omega)
    rw [red₂_inv _ hru, map_mul]
    -- red₂ (↑r) = ↑r, red₂ (↑(p-r)) = ↑(p-r) = -↑r in ZMod p
    have e1 : red₂ (((r : ℕ) : ZMod (p^2))) = ((r : ℕ) : ZMod p) := map_natCast _ r
    have e2 : red₂ ((((p - r : ℕ)) : ZMod (p^2))) = -(((r : ℕ) : ZMod p)) := by
      rw [map_natCast, Nat.cast_sub (by omega), ZMod.natCast_self, zero_sub]
    rw [e1, e2]
    rw [show ((r:ℕ):ZMod p) * -((r:ℕ):ZMod p) = -(((r:ℕ):ZMod p)^2) by ring]
    rw [inv_neg, inv_pow]
  -- conclude
  have hpT : (p : ZMod (p^2)) * T = 0 := p_mul_eq_zero_of_castHom_zero hp0 T hTred
  rw [hpT] at h2S
  exact (IsUnit.mul_right_eq_zero (isUnit_two hp5)).mp h2S

/-- Order-2 sum reduces to 0 mod p, hence `p *` it is `0` in `ZMod (p^2)`. -/
theorem p_mul_sumsq [Fact p.Prime] (hp5 : 5 ≤ p) :
    (p : ZMod (p^2)) * (∑ r ∈ Finset.Icc 1 (p-1), (((r:ℕ):ZMod (p^2))⁻¹)^2) = 0 := by
  have hpp : p.Prime := Fact.out
  apply p_mul_eq_zero_of_castHom_zero hpp.pos
  rw [map_sum]
  rw [← harmonic_modp_icc (p := p) 2 (by norm_num) (by omega)]
  apply Finset.sum_congr rfl
  intro r hr
  simp only [Finset.mem_Icc] at hr
  rw [map_pow, red₂_inv _ (isUnit_cast r hr.1 hr.2), map_natCast]

/-- Shifted Wolstenholme: `∑_{r=1}^{p-1} (jp+r)⁻¹ = 0` in `ZMod (p^2)`. -/
theorem wolstenholme_shift [Fact p.Prime] (hp5 : 5 ≤ p) (j : ℕ) :
    ∑ r ∈ Finset.Icc 1 (p-1), (((j * p + r : ℕ) : ZMod (p^2)))⁻¹ = 0 := by
  have hpp : p.Prime := Fact.out
  have key : ∀ r ∈ Finset.Icc 1 (p-1),
      (((j * p + r : ℕ) : ZMod (p^2)))⁻¹
        = ((r:ℕ):ZMod (p^2))⁻¹ - (j * p : ZMod (p^2)) * (((r:ℕ):ZMod (p^2))⁻¹)^2 := by
    intro r hr
    simp only [Finset.mem_Icc] at hr
    have hru : IsUnit ((r:ℕ):ZMod (p^2)) := isUnit_cast r hr.1 hr.2
    have hp2 : (p : ZMod (p^2))^2 = 0 := by
      rw [show ((p:ZMod (p^2)))^2 = ((p^2 : ℕ) : ZMod (p^2)) by push_cast; ring, ZMod.natCast_self]
    have hr1 : ((r:ℕ):ZMod (p^2)) * ((r:ℕ):ZMod (p^2))⁻¹ = 1 := ZMod.mul_inv_of_unit _ hru
    have ha2 : ((j:ZMod (p^2)) * (p:ZMod (p^2)))^2 = 0 := by rw [mul_pow, hp2, mul_zero]
    apply ZMod.inv_eq_of_mul_eq_one
    push_cast
    linear_combination (1 - (j:ZMod (p^2))*(p:ZMod (p^2)) * ((r:ℕ):ZMod (p^2))⁻¹) * hr1
      - (((r:ℕ):ZMod (p^2))⁻¹)^2 * ha2
  rw [Finset.sum_congr rfl key, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [wolstenholme_two hp5]
  rw [show (j * p : ZMod (p^2)) = (j : ZMod (p^2)) * (p : ZMod (p^2)) by ring]
  rw [mul_assoc, p_mul_sumsq hp5, mul_zero, sub_zero]

end Sun
