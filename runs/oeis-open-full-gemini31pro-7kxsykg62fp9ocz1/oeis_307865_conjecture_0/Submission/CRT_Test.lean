import Mathlib

open Nat ZMod

theorem odd_mod_two_eq_zero {u : ℕ} (hu_odd : Odd u) (hu_pos : 0 < u) (h2 : (2 : ZMod u) = 0) : u = 1 := by
  have h_dvd : u ∣ 2 := by
    rw [← CharP.cast_eq_zero_iff (ZMod u) u]
    exact h2
  have h_le : u ≤ 2 := Nat.le_of_dvd zero_lt_two h_dvd
  rcases hu_odd with ⟨k, hk⟩
  omega

theorem isUnit_map_ringEquiv {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S) (x : R) (hx : IsUnit x) : IsUnit (e x) := by
  rw [isUnit_iff_exists_inv] at hx ⊢
  rcases hx with ⟨x_inv, hx_inv⟩
  use e x_inv
  rw [← map_mul e, hx_inv, map_one e]

theorem isUnit_of_pow_eq_m_one {R : Type*} [CommRing R] {b : R} {n : ℕ} (hn : n > 0) (hbn : b ^ n = -1) : IsUnit b := by
  have H : b * (- (b ^ (n - 1))) = 1 := by
    calc b * (- (b ^ (n - 1))) = - (b ^ 1 * b ^ (n - 1)) := by ring
      _ = - (b ^ (1 + (n - 1))) := by rw [← pow_add]
      _ = - (b ^ n) := by
        have : 1 + (n - 1) = n := by omega
        rw [this]
      _ = - (-1) := by rw [hbn]
      _ = 1 := by ring
  exact ⟨⟨b, (- (b ^ (n - 1))), H, by rw [mul_comm, H]⟩, rfl⟩

theorem crt_contradiction {m u v n : ℕ} (huv : m = u * v) (hcop : Coprime u v)
    (hu : 1 < u) (hv : 1 < v) (hm_odd : Odd m) (hn : n > 0)
    (b : ZMod m) (hbn : b ^ n = -1)
    (h_pseudo : ∀ x : ZMod m, IsUnit x → x ^ n = 1 ∨ x ^ n = -1) : False := by
  subst huv
  have e : ZMod (u * v) ≃+* ZMod u × ZMod v := ZMod.chineseRemainder hcop
  let y := e b
  let x_tup : ZMod u × ZMod v := (y.1, 1)
  let x := e.symm x_tup
  have hx_tup : e x = x_tup := RingEquiv.apply_symm_apply e x_tup
  have hy1 : y.1 ^ n = -1 := by
    have h1 : e (b ^ n) = e (-1) := congrArg e hbn
    simp only [map_pow, map_neg, map_one] at h1
    exact congrArg Prod.fst h1
  have hb_unit : IsUnit b := isUnit_of_pow_eq_m_one hn hbn
  have hy_unit : IsUnit y := isUnit_map_ringEquiv e b hb_unit
  have hx_tup_unit : IsUnit x_tup := by
    rw [isUnit_iff_exists_inv] at hy_unit ⊢
    rcases hy_unit with ⟨y_inv, hy_inv⟩
    use (y_inv.1, 1)
    ext
    · have h_fst : (y * y_inv).1 = (1 : ZMod u × ZMod v).1 := congrArg Prod.fst hy_inv
      exact h_fst
    · exact mul_one 1
  have hx_unit : IsUnit x := isUnit_map_ringEquiv e.symm x_tup hx_tup_unit
  rcases h_pseudo x hx_unit with h1 | h2
  · have he1 : e (x ^ n) = e 1 := congrArg e h1
    simp only [map_pow, map_one] at he1
    have he1_tup : x_tup ^ n = 1 := by
      calc x_tup ^ n = (e x) ^ n := by rw [hx_tup]
        _ = 1 := he1
    have hy1_n : y.1 ^ n = 1 := by
      have hh : (x_tup ^ n).1 = (1 : ZMod u × ZMod v).1 := congrArg Prod.fst he1_tup
      exact hh
    rw [hy1] at hy1_n
    have h_u_div_2 : (2 : ZMod u) = 0 := by
      calc (2 : ZMod u) = 1 + 1 := by ring
        _ = (-1 : ZMod u) + 1 := congrArg (· + 1) hy1_n.symm
        _ = 0 := by ring
    have hu_odd : Odd u := hm_odd.of_mul_left
    have hu_pos : 0 < u := by omega
    have hu_eq_1 := odd_mod_two_eq_zero hu_odd hu_pos h_u_div_2
    omega
  · have he1 : e (x ^ n) = e (-1) := congrArg e h2
    simp only [map_pow, map_neg, map_one] at he1
    have he1_tup : x_tup ^ n = -1 := by
      calc x_tup ^ n = (e x) ^ n := by rw [hx_tup]
        _ = -1 := he1
    have h1_n : (1 : ZMod v) ^ n = -1 := by
      have hh : (x_tup ^ n).2 = (-1 : ZMod u × ZMod v).2 := congrArg Prod.snd he1_tup
      exact hh
    simp only [one_pow] at h1_n
    have h_v_div_2 : (2 : ZMod v) = 0 := by
      calc (2 : ZMod v) = 1 + 1 := by ring
        _ = (-1 : ZMod v) + 1 := congrArg (· + 1) h1_n
        _ = 0 := by ring
    have hv_odd : Odd v := hm_odd.of_mul_right
    have hv_pos : 0 < v := by omega
    have hv_eq_1 := odd_mod_two_eq_zero hv_odd hv_pos h_v_div_2
    omega

