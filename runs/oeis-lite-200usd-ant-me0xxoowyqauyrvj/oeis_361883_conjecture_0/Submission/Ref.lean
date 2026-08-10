import FormalConjectures.Util.ProblemImports

open Nat Finset BigOperators

namespace Ref

variable {p : ℕ}

/-- In `ZMod (p^2)`, if the reduction of `X` to `ZMod p` is `0`, then `p * X = 0`. -/
theorem pmul_eq_zero (hp : 0 < p) (X : ZMod (p ^ 2))
    (h : (ZMod.castHom (dvd_pow_self p two_ne_zero) (ZMod p)) X = 0) :
    (p : ZMod (p ^ 2)) * X = 0 := by
  have hne : NeZero p := ⟨hp.ne'⟩
  have hpd : p ∣ X.val := by
    rw [ZMod.castHom_apply, ← ZMod.natCast_val, ZMod.natCast_eq_zero_iff] at h
    exact h
  obtain ⟨c, hc⟩ := hpd
  have e1 : (p : ZMod (p ^ 2)) * X = ((p * X.val : ℕ) : ZMod (p ^ 2)) := by
    rw [Nat.cast_mul, ZMod.natCast_zmod_val]
  rw [e1, hc, show p * (p * c) = p ^ 2 * c by ring, Nat.cast_mul,
      ZMod.natCast_self, zero_mul]

/-- `i` is a unit in `ZMod (p^2)` for `1 ≤ i ≤ p-1`. -/
theorem isUnit_cast2 [Fact p.Prime] (i : ℕ) (h1 : 1 ≤ i) (h2 : i ≤ p - 1) :
    IsUnit ((i : ℕ) : ZMod (p ^ 2)) := by
  have hp : p.Prime := Fact.out
  rw [ZMod.isUnit_iff_coprime]
  have hnd : ¬ p ∣ i := by intro hd; have := Nat.le_of_dvd (by omega) hd; omega
  exact (hp.coprime_iff_not_dvd.mpr hnd).symm.pow_right 2

/-- Harmonic order-2 sum vanishes mod p (recalled). -/
theorem harm2_p [Fact p.Prime] (hp5 : 5 ≤ p) :
    ∑ i ∈ Icc 1 (p - 1), ((i : ZMod p)⁻¹) ^ 2 = 0 := by
  -- reuse the standard FiniteField argument
  have hp0 : 0 < p := (Fact.out (p := p.Prime)).pos
  have hne : NeZero p := ⟨hp0.ne'⟩
  have key : ∑ x : ZMod p, (x⁻¹) ^ 2 = 0 := by
    have h := Equiv.sum_comp (Function.Involutive.toPerm (Inv.inv : ZMod p → ZMod p) inv_inv)
      (fun y => y ^ 2)
    simp only [Function.Involutive.coe_toPerm] at h
    rw [h]
    apply FiniteField.sum_pow_lt_card_sub_one
    rw [ZMod.card]; omega
  rw [show (∑ x : ZMod p, (x⁻¹)^2) = ∑ r ∈ Finset.range p, (((r : ZMod p))⁻¹)^2 by
    apply Finset.sum_nbij' (i := fun x : ZMod p => x.val) (j := fun r : ℕ => (r : ZMod p))
    · intro a _; simp [Finset.mem_range, ZMod.val_lt]
    · intro b _; exact Finset.mem_univ _
    · intro a _; exact ZMod.natCast_rightInverse a
    · intro b hb; exact ZMod.val_cast_of_lt (Finset.mem_range.mp hb)
    · intro a _; rw [ZMod.natCast_rightInverse a]] at key
  rw [show Finset.range p = insert 0 (Finset.Icc 1 (p-1)) by
    ext x; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega,
    Finset.sum_insert (by simp)] at key
  simp only [Nat.cast_zero, inv_zero] at key
  rw [zero_pow (by norm_num), zero_add] at key
  exact key

/-- **Wolstenholme**: `∑_{i=1}^{p-1} i⁻¹ ≡ 0 (mod p²)`, i.e. `= 0` in `ZMod (p²)`. -/
theorem wolstenholme_H1 [Fact p.Prime] (hp5 : 5 ≤ p) :
    ∑ i ∈ Icc 1 (p - 1), ((i : ZMod (p ^ 2))⁻¹) = 0 := by
  have hp : p.Prime := Fact.out
  have hp0 : 0 < p := hp.pos
  have hne : NeZero p := ⟨hp0.ne'⟩
  set s := ∑ i ∈ Icc 1 (p - 1), ((i : ZMod (p ^ 2))⁻¹) with hs
  -- reflection: s = ∑ (p - i)⁻¹
  have hrefl : s = ∑ i ∈ Icc 1 (p - 1), (((p - i : ℕ) : ZMod (p ^ 2))⁻¹) := by
    rw [hs]
    apply Finset.sum_nbij' (i := fun x => p - x) (j := fun x => p - x)
    · intro a ha; simp only [Finset.mem_Icc] at *; omega
    · intro a ha; simp only [Finset.mem_Icc] at *; omega
    · intro a ha; simp only [Finset.mem_Icc] at ha; omega
    · intro a ha; simp only [Finset.mem_Icc] at ha; omega
    · intro a ha; simp only [Finset.mem_Icc] at ha; rw [show p - (p - a) = a by omega]
  -- 2 s = ∑ (i⁻¹ + (p-i)⁻¹) = p · X  where X = ∑ (i (p-i))⁻¹
  have hpair : ∀ i ∈ Icc 1 (p - 1),
      ((i : ZMod (p^2))⁻¹) + (((p - i : ℕ) : ZMod (p^2))⁻¹)
        = (p : ZMod (p^2)) * (((i * (p - i) : ℕ) : ZMod (p^2))⁻¹) := by
    intro i hi
    simp only [Finset.mem_Icc] at hi
    have hprod : (((i * (p - i) : ℕ)) : ZMod (p^2)) = (i : ZMod (p^2)) * ((p - i : ℕ) : ZMod (p^2)) := by
      push_cast; ring
    have hsum' : (p : ZMod (p^2)) = (i : ZMod (p^2)) + ((p - i : ℕ) : ZMod (p^2)) := by
      rw [Nat.cast_sub (by omega)]; ring
    rw [hprod, hsum']
    set a := (i : ZMod (p^2)) with ha
    set b := ((p - i : ℕ) : ZMod (p^2)) with hb
    have hua : IsUnit a := isUnit_cast2 i hi.1 hi.2
    have hub : IsUnit b := isUnit_cast2 (p - i) (by omega) (by omega)
    have haa : a * a⁻¹ = 1 := ZMod.mul_inv_of_unit a hua
    have hbb : b * b⁻¹ = 1 := ZMod.mul_inv_of_unit b hub
    have hab : (a * b) * (a * b)⁻¹ = 1 := ZMod.mul_inv_of_unit (a * b) (hua.mul hub)
    have e1 : (a * b) * (a⁻¹ + b⁻¹) = a + b := by
      rw [mul_add, show a * b * a⁻¹ = b * (a * a⁻¹) by ring,
          show a * b * b⁻¹ = a * (b * b⁻¹) by ring, haa, hbb]; ring
    have e2 : (a * b) * ((a + b) * (a * b)⁻¹) = a + b := by
      rw [show (a * b) * ((a + b) * (a * b)⁻¹) = (a + b) * ((a * b) * (a * b)⁻¹) by ring,
          hab, mul_one]
    exact (hua.mul hub).mul_right_injective (e1.trans e2.symm)
  have h2s : (2 : ZMod (p^2)) * s = (p : ZMod (p^2)) * ∑ i ∈ Icc 1 (p - 1), (((i * (p - i) : ℕ) : ZMod (p^2))⁻¹) := by
    have : (2 : ZMod (p^2)) * s = s + s := by ring
    rw [this]
    nth_rewrite 2 [hrefl]
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl hpair
  -- Now show p · X = 0
  set X := ∑ i ∈ Icc 1 (p - 1), (((i * (p - i) : ℕ) : ZMod (p^2))⁻¹) with hX
  have hpX : (p : ZMod (p^2)) * X = 0 := by
    apply pmul_eq_zero hp0
    -- reduction of X to ZMod p equals -harm2 = 0
    rw [hX, map_sum]
    have hcastle : ∀ i ∈ Icc 1 (p - 1),
        (ZMod.castHom (dvd_pow_self p two_ne_zero) (ZMod p)) ((((i * (p - i) : ℕ)) : ZMod (p^2))⁻¹)
          = - (((i : ZMod p)⁻¹) ^ 2) := by
      intro i hi
      simp only [Finset.mem_Icc] at hi
      have hu : IsUnit (((i * (p - i) : ℕ)) : ZMod (p^2)) := by
        rw [Nat.cast_mul]
        exact (isUnit_cast2 i hi.1 hi.2).mul (isUnit_cast2 (p - i) (by omega) (by omega))
      set F := ZMod.castHom (dvd_pow_self p two_ne_zero) (ZMod p) with hF
      have hone : ((i * (p - i) : ℕ) : ZMod (p^2)) * (((i * (p - i) : ℕ) : ZMod (p^2))⁻¹) = 1 :=
        ZMod.mul_inv_of_unit _ hu
      have hmul1 : F ((i * (p - i) : ℕ) : ZMod (p^2)) * F (((i * (p - i) : ℕ) : ZMod (p^2))⁻¹) = 1 := by
        rw [← map_mul, hone, map_one]
      have hcu : F ((i * (p - i) : ℕ) : ZMod (p^2)) = -((i : ZMod p))^2 := by
        rw [hF, map_natCast, Nat.cast_mul,
            show ((p - i : ℕ) : ZMod p) = (p : ZMod p) - i by rw [Nat.cast_sub (by omega)],
            ZMod.natCast_self]
        ring
      rw [hcu] at hmul1
      have hthis : F (((i * (p - i) : ℕ) : ZMod (p^2))⁻¹) = (-((i : ZMod p))^2)⁻¹ :=
        eq_inv_of_mul_eq_one_right hmul1
      rw [hthis, ← neg_inv, inv_pow]
    rw [Finset.sum_congr rfl hcastle]
    rw [Finset.sum_neg_distrib]
    rw [harm2_p hp5]
    simp
  -- 2 is a unit, so s = 0
  have hu2 : IsUnit (2 : ZMod (p^2)) := by
    rw [show (2 : ZMod (p^2)) = ((2 : ℕ) : ZMod (p^2)) by norm_num, ZMod.isUnit_iff_coprime]
    have : ¬ p ∣ 2 := by intro hd; have := Nat.le_of_dvd (by norm_num) hd; omega
    exact (hp.coprime_iff_not_dvd.mpr this).symm.pow_right 2
  have : (2 : ZMod (p^2)) * s = 0 := by rw [h2s]; exact hpX
  exact (hu2.mul_right_eq_zero).mp this

/-- `s * C(m,s) = m * C(m-1,s-1)`, the absorption identity (integer form). -/
theorem choose_absorb (m s : ℕ) (hs : 1 ≤ s) (hsm : s ≤ m) :
    s * (m.choose s) = m * ((m - 1).choose (s - 1)) := by
  obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  rw [Nat.add_one_mul_choose_eq]
  ring

/-- For `1 ≤ s ≤ p-1`, `p^(v_p m) ∣ C(m,s)` (the power-sum divisibility seed). -/
theorem padic_dvd_choose [Fact p.Prime] (hp : 2 ≤ p) (m s : ℕ) (hs1 : 1 ≤ s) (hsp : s ≤ p - 1)
    (hsm : s ≤ m) :
    p ^ (padicValNat p m) ∣ m.choose s := by
  have hpp : p.Prime := Fact.out
  -- s * C(m,s) = m * C(m-1,s-1).  p ∤ s, so v_p(s*C) = v_p(C). v_p(m*..) ≥ v_p(m).
  have habs := choose_absorb m s hs1 hsm
  have hpns : ¬ p ∣ s := by intro hd; have := Nat.le_of_dvd (by omega) hd; omega
  have hmne : m ≠ 0 := by omega
  have hcne : m.choose s ≠ 0 := Nat.choose_pos hsm |>.ne'
  -- valuations
  have hsne : s ≠ 0 := by omega
  have hvs : padicValNat p s = 0 := padicValNat.eq_zero_of_not_dvd hpns
  have key : padicValNat p (s * m.choose s) = padicValNat p (m * (m - 1).choose (s - 1)) := by
    rw [habs]
  rw [padicValNat.mul hsne hcne, hvs, zero_add] at key
  have hpos : 0 < (m - 1).choose (s - 1) := Nat.choose_pos (by omega)
  have hge : padicValNat p m ≤ padicValNat p (m * (m - 1).choose (s - 1)) := by
    rw [padicValNat.mul hmne hpos.ne']; omega
  rw [← key] at hge
  calc p ^ (padicValNat p m) ∣ p ^ (padicValNat p (m.choose s)) := pow_dvd_pow p hge
    _ ∣ m.choose s := pow_padicValNat_dvd

end Ref
