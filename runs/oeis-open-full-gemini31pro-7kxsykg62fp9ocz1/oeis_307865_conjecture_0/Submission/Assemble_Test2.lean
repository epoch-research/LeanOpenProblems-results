import Mathlib
import Submission.PrimePower_Test
import Submission.CRT_Test
import Submission.Assemble_Test

open Nat ZMod Finset

def a_test (n : ℕ) : ℕ :=
  let m : ℕ := 2 * n + 1
  (Ico 1 m).filter (fun b : ℕ => (b : ZMod m) ^ n = (-1 : ZMod m)) |>.card

def IsAbsoluteEulerPseudoprime (m : ℕ) : Prop :=
  m > 1 ∧ ¬ Nat.Prime m ∧
  (∀ b : ℕ, Nat.Coprime b m → (b : ZMod m) ^ ((m - 1) / 2) = 1 ∨ (b : ZMod m) ^ ((m - 1) / 2) = -1)

theorem conjecture_test {n : ℕ} (h : IsAbsoluteEulerPseudoprime (2 * n + 1)) : a_test n = 0 := by
  let m := 2 * n + 1
  have hm : m = 2 * n + 1 := rfl
  have hm_odd : Odd m := odd_two_mul_add_one n
  have hm_gt_1 : m > 1 := h.1
  have h_not_prime : ¬ Nat.Prime m := h.2.1
  have hn_pos : n > 0 := by omega
  have hm_pos : m > 0 := by omega
  have h_pseudo : ∀ x : ZMod m, IsUnit x → x ^ n = 1 ∨ x ^ n = -1 := by
    intro x hx
    have h_coprime : Coprime x.val m := by
      have : x = ((x.val : ℕ) : ZMod m) := (ZMod.natCast_zmod_val x).symm
      rw [this] at hx
      exact (ZMod.isUnit_iff_coprime x.val m).mp hx
    have h_val : (x.val : ZMod m) = x := ZMod.natCast_zmod_val x
    have h_sub : (m - 1) / 2 = n := by omega
    rcases h.2.2 x.val h_coprime with h1 | h2
    · left; rw [h_val, h_sub] at h1; exact h1
    · right; rw [h_val, h_sub] at h2; exact h2
  by_contra h_neq
  have h_pos : 0 < ((Ico 1 m).filter (fun b : ℕ => (b : ZMod m) ^ n = -1)).card := Nat.pos_of_ne_zero h_neq
  rcases card_pos.mp h_pos with ⟨b_nat, hb_mem⟩
  rw [mem_filter] at hb_mem
  have hb_ico : b_nat ∈ Ico 1 m := hb_mem.1
  have hbn : (b_nat : ZMod m) ^ n = -1 := hb_mem.2
  let b : ZMod m := b_nat
  have hbn_b : b ^ n = -1 := hbn
  have h_exists_p : ∃ p, p.Prime ∧ p ∣ m := Nat.exists_prime_and_dvd hm_gt_1.ne'
  rcases h_exists_p with ⟨p, hp, hp_dvd⟩
  have hp_props := padic_props hp hm_pos hp_dvd
  let k := padicValNat p m
  let v := m / p ^ k
  rcases hp_props with ⟨hk_pos, h_m_eq, h_coprime⟩
  have hv_gt_0 : 1 ≤ v := Nat.pos_of_ne_zero (by intro h; have : m / p ^ k = 0 := h; rw [this, mul_zero] at h_m_eq; omega)
  rcases eq_or_lt_of_le hv_gt_0 with hv_eq | hv_gt
  · have hv1 : v = 1 := hv_eq.symm
    have hm_pk : p ^ k = m := by
      calc p ^ k = p ^ k * 1 := by ring
        _ = p ^ k * v := by rw [← hv1]
        _ = m := h_m_eq.symm
    have hk_ge_2 : 2 ≤ k := by
      by_contra hk_lt
      have hk1 : k = 1 := by omega
      have hp_m : p = m := by
        calc p = p ^ 1 := by ring
          _ = p ^ k := by rw [hk1]
          _ = m := hm_pk
      subst hp_m
      exact h_not_prime hp
    have h_pseudo_pk : ∀ x : ZMod (p ^ k), IsUnit x → x ^ n = 1 ∨ x ^ n = -1 := by
      intro x hx
      let e : ZMod m ≃+* ZMod (p ^ k) := ZMod.ringEquivCongr hm_pk.symm
      have he_unit : IsUnit (e.symm x) := isUnit_map_ringEquiv e.symm x hx
      rcases h_pseudo (e.symm x) he_unit with h1 | h2
      · left
        have := congrArg e h1
        simp only [map_pow, map_one] at this
        have h_e_symm : e (e.symm x) = x := RingEquiv.apply_symm_apply e x
        rw [h_e_symm] at this
        exact this
      · right
        have := congrArg e h2
        simp only [map_pow, map_neg, map_one] at this
        have h_e_symm : e (e.symm x) = x := RingEquiv.apply_symm_apply e x
        rw [h_e_symm] at this
        exact this
    exact prime_power_contradiction hp hk_ge_2 hm_pk h_pseudo_pk
  · let u := p ^ k
    have hu_gt_1 : 1 < u := Nat.one_lt_pow hk_pos.ne' hp.one_lt
    exact crt_contradiction h_m_eq h_coprime hu_gt_1 hv_gt hm_odd hn_pos b hbn_b h_pseudo
