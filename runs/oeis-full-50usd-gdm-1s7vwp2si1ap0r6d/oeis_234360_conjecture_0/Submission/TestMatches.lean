import FormalConjectures.Util.ProblemImports

set_option exponentiation.threshold 2000
set_option maxRecDepth 200000

open Nat Finset

def powMod (b e m : ℕ) : ℕ :=
  if h : e = 0 then 1
  else if e % 2 = 1 then
    have : e / 2 < e := Nat.div_lt_self (Nat.pos_of_ne_zero h) (Nat.le_refl 2)
    (powMod b (e / 2) m) ^ 2 * b % m
  else
    have : e / 2 < e := Nat.div_lt_self (Nat.pos_of_ne_zero h) (Nat.le_refl 2)
    (powMod b (e / 2) m) ^ 2 % m

theorem powMod_eq (b e m : ℕ) (hm : 1 < m) : powMod b e m = b ^ e % m := sorry

lemma coprime_two_of_prime_ne_two {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) : Coprime 2 p := by
  have h_dvd : ¬ p ∣ 2 := by
    intro hd
    have : p ≤ 2 := Nat.le_of_dvd (by decide) hd
    have : 2 ≤ p := hp.two_le
    have : p = 2 := by omega
    exact h2 this
  have h_cop : Coprime p 2 := hp.coprime_iff_not_dvd.mpr h_dvd
  exact h_cop.symm

lemma not_prime_of_fermat_test_failed {p : ℕ} (hp2 : p ≠ 2) (h_pow : powMod 2 (p - 1) p % p ≠ 1) : ¬ p.Prime := by
  intro hp
  have hp1 : 1 < p := hp.one_lt
  have h_cop : Coprime 2 p := coprime_two_of_prime_ne_two hp hp2
  have h_fermat := Nat.ModEq.pow_card_sub_one_eq_one hp h_cop
  unfold Nat.ModEq at h_fermat
  rw [Nat.mod_eq_of_lt hp1] at h_fermat
  have h_powMod := powMod_eq 2 (p - 1) p hp1
  rw [h_fermat] at h_powMod
  have h_mod2 : powMod 2 (p - 1) p % p = 1 % p := by rw [h_powMod]
  rw [Nat.mod_eq_of_lt hp1] at h_mod2
  exact h_pow h_mod2

lemma k_not_prime_ind_83 : ¬ Nat.Prime ((83 + 2) ^ 330 - (83 + 1)) := not_prime_of_fermat_test_failed (by decide) (by decide)
