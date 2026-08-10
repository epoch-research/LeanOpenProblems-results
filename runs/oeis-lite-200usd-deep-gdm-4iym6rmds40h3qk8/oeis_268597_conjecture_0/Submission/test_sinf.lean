import Mathlib

open Nat Set

theorem solve_goldbach (n : ℕ) (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) 
    (hp2 : p ≠ 2) (hq2 : q ≠ 2) (h_sum : p + q = n + 2) :
    p * q ∈ { x : ℕ | x > 0 ∧ (x - 1) % Nat.totient x = n } := by
  simp only [mem_setOf_eq]
  have h_x_pos : p * q > 0 := Nat.mul_pos hp.pos hq.pos
  refine ⟨h_x_pos, ?_⟩
  have h_tot : Nat.totient (p * q) = (p - 1) * (q - 1) := by
    rw [Nat.totient_mul hpq.symm.coprime_iff_not_dvd.mpr (by
      intro hdvd
      have hp_eq : p = q := hp.eq_one_or_self_of_dvd hdvd |>.resolve_left hq.ne_one |>.symm
      exact hpq hp_eq
    )]
    rw [hp.totient, hq.totient]
  rw [h_tot]
  have h_eq : p * q - 1 = (p - 1) * (q - 1) + n := by
    have h1 : (p - 1) * (q - 1) = p * q - (p + q) + 1 := by
      have hp_ge : p ≥ 1 := hp.pos
      have hq_ge : q ≥ 1 := hq.pos
      omega
    rw [h1]
    rw [h_sum]
    omega
  rw [h_eq]
  have h_lt : n < (p - 1) * (q - 1) := by
    have h_p3 : p ≥ 3 := by
      have : p ≥ 2 := hp.two_le
      omega
    have h_q3 : q ≥ 3 := by
      have : q ≥ 2 := hq.two_le
      omega
    have h1 : (p - 1) * (q - 1) = p * q - p - q + 1 := by omega
    rw [h1]
    have h2 : p * q ≥ 3 * q := by
      exact Nat.mul_le_mul_right q h_p3
    have h3 : 3 * q = q + q + q := by ring
    omega
  rw [Nat.add_mod_self_left]
  exact Nat.mod_eq_of_lt h_lt



noncomputable def A268597 (n : ℕ) : ℕ :=
  sInf { x : ℕ | x > 0 ∧ (x - 1) % Nat.totient x = n }

theorem A268597_pos_iff (n : ℕ) : A268597 n > 0 ↔ ∃ x > 0, (x - 1) % Nat.totient x = n := by
  constructor
  · intro h
    have h_ne := Nat.nonempty_of_pos_sInf h
    rcases h_ne with ⟨x, hx⟩
    exact ⟨x, hx.1, hx.2⟩
  · intro h
    rcases h with ⟨x, hx1, hx2⟩
    have h_ne : { y : ℕ | y > 0 ∧ (y - 1) % Nat.totient y = n }.Nonempty := ⟨x, hx1, hx2⟩
    have h_mem := Nat.sInf_mem h_ne
    exact h_mem.1

theorem oeis_268597_conjecture_test (n : ℕ) : A268597 n > 0 := by
  unfold A268597 sInf
  dsimp [Nat.instInfSet]
  split_ifs with h
  · have h_spec := @Nat.find_spec (fun x => x > 0 ∧ (x - 1) % Nat.totient x = n) (fun _ => Classical.propDecidable _) h
    exact h_spec.1
  · sorry


















