import FormalConjectures.Util.ProblemImports

open Nat BigOperators Finset

def a (n : ℕ) : ℕ :=
  let A018804_n : ℕ := (Finset.Ico 1 (n + 1)).sum fun k => Nat.gcd k n
  n / Nat.gcd n (1 + A018804_n)

lemma gcd_of_prime_lt (p : ℕ) (hp : Nat.Prime p) (k : ℕ) (hk1 : 1 ≤ k) (hk2 : k < p) : Nat.gcd k p = 1 := by
  have h_not_dvd : ¬ p ∣ k := Nat.not_dvd_of_pos_of_lt (by omega) hk2
  have h_coprime : Nat.Coprime k p := ((Nat.Prime.coprime_iff_not_dvd hp).mpr h_not_dvd).symm
  exact h_coprime

theorem sum_prime (p : ℕ) (hp : Nat.Prime p) :
    (Finset.Ico 1 (p + 1)).sum (fun k => Nat.gcd k p) = 2 * p - 1 := by
  have hp_ge1 : 1 ≤ p := hp.pos
  rw [Finset.sum_Ico_succ_top hp_ge1]
  have h_const : ∑ k ∈ Finset.Ico 1 p, Nat.gcd k p = ∑ k ∈ Finset.Ico 1 p, 1 := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [Finset.mem_Ico] at hx
    exact gcd_of_prime_lt p hp x hx.1 hx.2
  rw [h_const]
  simp only [Finset.sum_const, card_Ico, smul_eq_mul, mul_one]
  have : Nat.gcd p p = p := Nat.gcd_self p
  rw [this]
  omega

theorem a_prime (p : ℕ) (hp : Nat.Prime p) : a p = 1 := by
  unfold a
  have h_sum := sum_prime p hp
  dsimp only
  rw [h_sum]
  have hp_ge2 : 2 ≤ p := hp.two_le
  have h_add : 1 + (2 * p - 1) = 2 * p := by omega
  rw [h_add]
  have h_gcd : Nat.gcd p (2 * p) = p := by
    apply Nat.gcd_eq_left
    exact dvd_mul_left p 2
  rw [h_gcd]
  exact Nat.div_self hp.pos

#check Nat.exists_prime_and_dvd




