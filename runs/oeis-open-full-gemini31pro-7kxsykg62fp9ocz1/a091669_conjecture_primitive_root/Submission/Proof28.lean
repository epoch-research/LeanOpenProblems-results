import Mathlib
import Submission.Spec
import Submission.Proof27

open Nat BigOperators

lemma is_primitive_root_of_P_mod_n_eq_one (n : ℕ) (hn_prime : n.Prime) (hn2 : n > 2)
  (hP : (((Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1) : ℕ) : ZMod n) = 1) :
  IsPrimitiveRoot (2 : ZMod n) (n - 1) := by
  haveI : Fact n.Prime := ⟨hn_prime⟩
  have h_unit : (2 : ZMod n) ≠ 0 := by
    intro h
    have : n ∣ 2 := (CharP.cast_eq_zero_iff (ZMod n) n 2).mp h
    have : n = 2 := (Nat.prime_dvd_prime_iff_eq hn_prime Nat.prime_two).mp this
    omega
  have h_order_dvd : orderOf (2 : ZMod n) ∣ n - 1 := ZMod.orderOf_dvd_card_sub_one h_unit
  by_contra h_not_prim
  rw [IsPrimitiveRoot.iff_orderOf] at h_not_prim
  have h_order_lt : orderOf (2 : ZMod n) < n - 1 := lt_of_le_of_ne (Nat.le_of_dvd (by omega) h_order_dvd) h_not_prim
  let d : ℕ := orderOf (2 : ZMod n)
  have hd_pos : d ≥ 1 := by
    have hd_zero : d = 0 → n - 1 = 0 := by
      intro h
      have : 0 ∣ n - 1 := by
        rw [← h]
        exact h_order_dvd
      exact eq_zero_of_zero_dvd this
    omega
  have hd_le : d ≤ n - 2 := by omega
  have h_d_in : d ∈ Finset.Ico 1 (n - 1) := by
    rw [Finset.mem_Ico]
    exact ⟨hd_pos, h_order_lt⟩
  have h_dvd_prod : (2 ^ d - 1) ∣ (Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1) := by
    exact Finset.dvd_prod_of_mem (fun k => 2 ^ k - 1) h_d_in
  have h_2d_mod : ((2 ^ d - 1 : ℕ) : ZMod n) = 0 := by
    have h_pow : (2 : ZMod n) ^ d = 1 := pow_orderOf_eq_one (2 : ZMod n)
    have h_pow_nat : ((2 ^ d : ℕ) : ZMod n) = 1 := by
      calc ((2 ^ d : ℕ) : ZMod n) = (2 : ZMod n) ^ d := by push_cast; rfl
        _ = 1 := h_pow
    have h_sub : 2 ^ d - 1 + 1 = 2 ^ d := by
      have hd_pos_pow : 2 ^ d ≥ 1 := Nat.one_le_pow d 2 (by omega)
      omega
    have h_sub_zmod : (((2 ^ d - 1 : ℕ) : ZMod n) + 1) = ((2 ^ d : ℕ) : ZMod n) := by
      calc (((2 ^ d - 1 : ℕ) : ZMod n) + 1) = (((2 ^ d - 1 : ℕ) : ZMod n) + (1 : ℕ) : ZMod n) := by push_cast; rfl
        _ = (((2 ^ d - 1 + 1 : ℕ) : ZMod n)) := by rw [Nat.cast_add]
        _ = ((2 ^ d : ℕ) : ZMod n) := by rw [h_sub]
    rw [h_pow_nat] at h_sub_zmod
    calc ((2 ^ d - 1 : ℕ) : ZMod n) = ((2 ^ d - 1 : ℕ) : ZMod n) + 1 - 1 := by ring
      _ = 1 - 1 := by rw [h_sub_zmod]
      _ = 0 := by ring
  have h_prod_zero : (((Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1) : ℕ) : ZMod n) = 0 := by
    rcases h_dvd_prod with ⟨c, hc⟩
    rw [hc, Nat.cast_mul, h_2d_mod, zero_mul]
  rw [hP] at h_prod_zero
  have : (1 : ZMod n) ≠ 0 := by
    exact one_ne_zero
  exact this h_prod_zero
