import Mathlib

open Nat ZMod

theorem padic_props {p m : ℕ} (hp : p.Prime) (hm : m > 0) (hpm : p ∣ m) :
    let k := padicValNat p m
    let v := m / p ^ k
    k > 0 ∧ m = p ^ k * v ∧ Coprime (p ^ k) v := by
  intro k v
  haveI : Fact p.Prime := ⟨hp⟩
  have hk_def : k = padicValNat p m := rfl
  have hm_neq : m ≠ 0 := by omega
  have h_pk_dvd : p ^ k ∣ m := by
    rw [padicValNat_dvd_iff k m]
    right
    rfl
  have h_m_eq : m = p ^ k * v := by
    calc m = m / p ^ k * p ^ k := (Nat.div_mul_cancel h_pk_dvd).symm
      _ = p ^ k * (m / p ^ k) := mul_comm _ _
  have h_k_pos : k > 0 := by
    have : p ^ 1 ∣ m := by rw [pow_one]; exact hpm
    have : 1 ≤ k := by
      have hh := (padicValNat_dvd_iff 1 m).mp this
      rcases hh with h_zero | h_le
      · exfalso; exact hm_neq h_zero
      · exact h_le
    omega
  have hp_not_dvd_v : ¬ p ∣ v := by
    intro hp_dvd_v
    have : p ^ (k + 1) ∣ m := by
      rw [h_m_eq, pow_succ]
      exact mul_dvd_mul_left (p ^ k) hp_dvd_v
    have : k + 1 ≤ k := by
      have hh := (padicValNat_dvd_iff (k + 1) m).mp this
      rcases hh with h_zero | h_le
      · exfalso; exact hm_neq h_zero
      · exact h_le
    omega
  have h_coprime : Coprime (p ^ k) v := by
    apply Nat.coprime_of_dvd
    intro q hq hq_dvd_pk
    have hqp : q = p := by
      have : q ∣ p := Nat.Prime.dvd_of_dvd_pow hq hq_dvd_pk
      exact (Nat.Prime.eq_one_or_self_of_dvd hp q this).resolve_left (Nat.Prime.ne_one hq)
    subst hqp
    exact hp_not_dvd_v
  exact ⟨h_k_pos, h_m_eq, h_coprime⟩
