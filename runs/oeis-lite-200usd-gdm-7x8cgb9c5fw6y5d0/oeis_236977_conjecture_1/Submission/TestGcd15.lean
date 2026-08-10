import FormalConjectures.Util.ProblemImports

open Nat

def totient_oracle_loop : Nat → Nat → Nat
  | 0, _ => 0
  | fuel + 1, n =>
    if n ≤ 1 then n
    else
      let p := n.minFac
      let m := n / p
      if m % p == 0 then
        p * totient_oracle_loop fuel m
      else
        (p - 1) * totient_oracle_loop fuel m

theorem totient_eq_oracle (fuel : Nat) (n : Nat) (h_fuel : n ≤ fuel) : totient n = totient_oracle_loop fuel n := by
  induction fuel generalizing n with
  | zero =>
    have hn : n = 0 := by omega
    subst hn
    rfl
  | succ m ih =>
    by_cases hn : n ≤ 1
    · rcases n with _ | _ | n'
      · rfl
      · rfl
      · omega
    · have h_n2 : n ≥ 2 := by omega
      have hp_prime : n.minFac.Prime := minFac_prime (by omega)
      have hp_dvd : n.minFac ∣ n := minFac_dvd n
      let p := n.minFac
      let k := n / p
      have hk_div : n = p * k := (Nat.mul_div_cancel' hp_dvd).symm
      have hp_ge2 : p ≥ 2 := Nat.Prime.two_le hp_prime
      have hk_lt : k < n := by
        rw [hk_div]
        have : k < p * k := by
          calc k < 2 * k := by omega
          _ ≤ p * k := Nat.mul_le_mul_right k hp_ge2
        exact this
      have hk_le : k ≤ m := by omega
      have ih_k := ih k hk_le
      simp only [totient_oracle_loop, hn, if_false]
      by_cases h_dvd : k % p == 0
      · have h_dvd_prop : p ∣ k := Nat.dvd_of_mod_eq_zero (Nat.eq_of_beq_eq_true h_dvd)
        rw [if_pos h_dvd]
        rw [hk_div]
        rw [totient_mul_of_prime_of_dvd hp_prime h_dvd_prop]
        rw [ih_k]
      · have h_not_dvd_prop : ¬ p ∣ k := by
          intro hd
          have hd2 : k % p = 0 := Nat.mod_eq_zero_of_dvd hd
          have hd3 : (k % p == 0) = true := Nat.beq_true_of_eq hd2
          rw [hd3] at h_dvd
          contradiction
        rw [if_neg h_dvd]
        rw [hk_div]
        rw [totient_mul_of_prime_of_not_dvd hp_prime h_not_dvd_prop]
        rw [ih_k]
