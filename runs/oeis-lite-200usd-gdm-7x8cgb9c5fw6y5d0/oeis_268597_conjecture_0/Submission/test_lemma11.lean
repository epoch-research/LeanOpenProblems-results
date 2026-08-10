import FormalConjectures.Util.ProblemImports

open Nat Set

lemma goldbach_witness_case {n : ℕ} {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q) (hp_odd : p ≥ 3) (hpq : p < q) (hsum : p + q = n + 2) :
  ∃ x, x > 0 ∧ (x - 1) % Nat.totient x = n := by
  use p * q
  have hp_pos : p > 0 := hp.pos
  have hq_pos : q > 0 := hq.pos
  have h_x_pos : p * q > 0 := by positivity
  refine ⟨h_x_pos, ?_⟩
  have h_cop : Nat.Coprime p q := by
    rw [Nat.Prime.coprime_iff_not_dvd hp]
    intro hdvd
    have h_or := hq.eq_one_or_self_of_dvd p hdvd
    have hp_ne_1 := hp.ne_one
    omega
  have h_tot : (p * q).totient = (p - 1) * (q - 1) := by
    rw [Nat.totient_mul h_cop]
    have h_totp := Nat.totient_prime hp
    have h_totq := Nat.totient_prime hq
    rw [h_totp, h_totq]
  rw [h_tot]
  have h_eq : p * q - 1 = (p - 1) * (q - 1) + n := by
    have hp_eq : p = p - 1 + 1 := by omega
    have hq_eq : q = q - 1 + 1 := by omega
    nth_rw 1 [hp_eq]
    nth_rw 1 [hq_eq]
    generalize hp_sub : p - 1 = u
    generalize hq_sub : q - 1 = v
    have h_ring : (u + 1) * (v + 1) = u * v + u + v + 1 := by ring
    have h_sum_uv : u + v = n := by omega
    omega
  rw [h_eq]
  have h_mod_self : ((p - 1) * (q - 1) + n) % ((p - 1) * (q - 1)) = n % ((p - 1) * (q - 1)) := by
    have h_rw : (p - 1) * (q - 1) + n = n + ((p - 1) * (q - 1)) * 1 := by ring
    rw [h_rw]
    exact Nat.add_mul_mod_self_left n ((p - 1) * (q - 1)) 1
  rw [h_mod_self]
  have h_lt : n < (p - 1) * (q - 1) := by
    have hu_ge : p - 1 ≥ 2 := by omega
    have hv_ge : q - 1 ≥ 3 := by omega
    generalize hp_sub : p - 1 = u at hu_ge ⊢
    generalize hq_sub : q - 1 = v at hv_ge ⊢
    have h_sum_uv : u + v = n := by omega
    nlinarith
  rw [Nat.mod_eq_of_lt h_lt]
