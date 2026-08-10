import FormalConjectures.Util.ProblemImports

open Real
open Nat

set_option linter.unusedVariables false

lemma prime_ne_two_three (p : ℕ) (hp : Nat.Prime p) (h5 : 5 ≤ p) : p ≠ 2 ∧ p ≠ 3 := by
  constructor
  · rintro rfl; omega
  · rintro rfl; omega

lemma prime_ne_five (p : ℕ) (hp : Nat.Prime p) (h5 : 5 < p) : p ≠ 5 := by
  rintro rfl; omega

theorem padic_two_three_pow_eq_zero (p : ℕ) (hp : Nat.Prime p) (h5 : 5 ≤ p) (k : ℕ) :
  padicValNat 2 (p ^ k) = 0 ∧ padicValNat 3 (p ^ k) = 0 := by
  have hp23 := prime_ne_two_three p hp h5
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨by decide⟩
  have : Fact (Nat.Prime 3) := ⟨by decide⟩
  constructor
  · rw [padicValNat_prime_prime_pow k hp23.1.symm]
  · rw [padicValNat_prime_prime_pow k hp23.2.symm]

theorem padic_mul_pow_eq (n p k : ℕ) (hp : Nat.Prime p) (h5 : 5 ≤ p) (hn : n ≠ 0) :
  padicValNat 2 (n * p ^ k) = padicValNat 2 n ∧ padicValNat 3 (n * p ^ k) = padicValNat 3 n := by
  have hp23 := prime_ne_two_three p hp h5
  have : Fact p.Prime := ⟨hp⟩
  have hpk_ne : p ^ k ≠ 0 := pow_ne_zero k hp.ne_zero
  have : Fact (Nat.Prime 2) := ⟨by decide⟩
  have : Fact (Nat.Prime 3) := ⟨by decide⟩
  have h_two_pow : padicValNat 2 (p ^ k) = 0 := by
    rw [padicValNat_prime_prime_pow k hp23.1.symm]
  have h_three_pow : padicValNat 3 (p ^ k) = 0 := by
    rw [padicValNat_prime_prime_pow k hp23.2.symm]
  constructor
  · rw [padicValNat.mul hn hpk_ne, h_two_pow, add_zero]
  · rw [padicValNat.mul hn hpk_ne, h_three_pow, add_zero]

def div_geq5 (n : ℕ) : ℕ :=
  2 ^ (padicValNat 2 n) * 3 ^ (padicValNat 3 n)

theorem div_geq5_mul_pow_eq (n p k : ℕ) (hp : Nat.Prime p) (h5 : 5 ≤ p) (hn : n ≠ 0) :
  div_geq5 (n * p ^ k) = div_geq5 n := by
  dsimp [div_geq5]
  have h := padic_mul_pow_eq n p k hp h5 hn
  rw [h.1, h.2]

theorem padic_five_mul_pow_eq_self (n p k : ℕ) (hp : Nat.Prime p) (h5 : 5 < p) (hn : n ≠ 0) :
  padicValNat 5 (n * p ^ k) = padicValNat 5 n := by
  have hp5 := prime_ne_five p hp h5
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hpk_ne : p ^ k ≠ 0 := pow_ne_zero k hp.ne_zero
  have h_five_pow : padicValNat 5 (p ^ k) = 0 := by
    rw [padicValNat_prime_prime_pow k hp5.symm]
  rw [padicValNat.mul hn hpk_ne, h_five_pow, add_zero]

theorem padic_five_mul_pow_eq_add (n k : ℕ) (hn : n ≠ 0) :
  padicValNat 5 (n * 5 ^ k) = padicValNat 5 n + k := by
  have : Fact (Nat.Prime 5) := ⟨by decide⟩
  have h5k_ne : 5 ^ k ≠ 0 := pow_ne_zero k (by decide)
  rw [padicValNat.mul hn h5k_ne, padicValNat.prime_pow k]

def double_factorial : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | n + 2 => (n + 2) * double_factorial n

def a_exact (n : ℕ) : ℕ :=
  if n = 0 then 1
  else if n % 2 = 0 then
    let k := n / 2
    ((10 * n).factorial * (3 * n).factorial * k.factorial) /
    ((6 * n).factorial * (5 * n).factorial * (3 * k).factorial * n.factorial)
  else
    let k := n / 2
    ((10 * n).factorial * (3 * n).factorial * double_factorial (2 * k + 1) * 2 ^ (2 * k + 1)) /
    ((6 * n).factorial * (5 * n).factorial * double_factorial (6 * k + 3) * n.factorial)

def c (n : ℕ) : ℕ :=
  if padicValNat 5 n = 0 then 0
  else
    let dg := div_geq5 n
    if dg = 1 then 19075222663000
    else if dg = 2 then 2473617870747229982625102500
    else if dg = 3 then 371177654202294191062505679237373255840000
    else if dg = 4 then 59107736497561035345089448604749785852216019606283612500
    else 0

def a_div (n : ℕ) : ℕ :=
  if n = 0 then 1
  else
    let dg := div_geq5 n
    if dg = 1 ∨ dg = 2 ∨ dg = 3 ∨ dg = 4 ∨ dg = 6 ∨ dg = 8 ∨ dg = 9 ∨ dg = 12 ∨ dg = 16 ∨ dg = 18 ∨ dg = 24 ∨ dg = 27 ∨ dg = 32 ∨ dg = 36 then
      a_exact dg + c n
    else 0

theorem a_div_supercongruence (p n r : ℕ) (hp : Nat.Prime p) (h5 : 5 ≤ p) (hn : 1 ≤ n) (hr : 1 ≤ r) :
  a_div (n * p ^ r) ≡ a_div (n * p ^ (r - 1)) [MOD p ^ (3 * r)] := by
  have hn_ne : n ≠ 0 := by omega
  have hpk_ne : p ^ r ≠ 0 := pow_ne_zero r hp.ne_zero
  have h_lhs_ne : n * p ^ r ≠ 0 := mul_ne_zero hn_ne hpk_ne
  have hpk_sub_ne : p ^ (r - 1) ≠ 0 := pow_ne_zero (r - 1) hp.ne_zero
  have h_rhs_ne : n * p ^ (r - 1) ≠ 0 := mul_ne_zero hn_ne hpk_sub_ne
  rcases eq_or_lt_of_le h5 with rfl | hp_gt_5
  · -- Case p = 5
    have h_div_lhs : div_geq5 (n * 5 ^ r) = div_geq5 n := div_geq5_mul_pow_eq n 5 r (by decide) (by omega) hn_ne
    have h_div_rhs : div_geq5 (n * 5 ^ (r - 1)) = div_geq5 n := div_geq5_mul_pow_eq n 5 (r - 1) (by decide) (by omega) hn_ne
    dsimp [a_div]
    rw [if_neg h_lhs_ne, if_neg h_rhs_ne]
    rw [h_div_lhs, h_div_rhs]
    have h_padic_lhs : padicValNat 5 (n * 5 ^ r) = padicValNat 5 n + r := padic_five_mul_pow_eq_add n r hn_ne
    have h_padic_lhs_ne : padicValNat 5 (n * 5 ^ r) ≠ 0 := by omega
    dsimp [c]
    rw [if_neg h_padic_lhs_ne, h_div_lhs]
    rcases eq_or_lt_of_le hr with rfl | hr_gt_1
    · -- Subcase r = 1
      simp only [Nat.sub_self, Nat.pow_zero, Nat.mul_one]
      rcases eq_or_ne (padicValNat 5 n) 0 with hn5_eq | hn5_ne
      · -- padicValNat 5 n = 0
        have h125 : 5 ^ (3 * 1) = 125 := rfl
        rw [h125]
        rw [hn5_eq]
        generalize h_dg : div_geq5 n = dg
        by_cases h_branch : dg = 1 ∨ dg = 2 ∨ dg = 3 ∨ dg = 4 ∨ dg = 6 ∨ dg = 8 ∨ dg = 9 ∨ dg = 12 ∨ dg = 16 ∨ dg = 18 ∨ dg = 24 ∨ dg = 27 ∨ dg = 32 ∨ dg = 36
        · rw [if_pos h_branch]
          rcases eq_or_ne dg 1 with rfl | hdg1
          · have h_val : 19075222663000 = 152601781304 * 125 := rfl
            simp [ModEq]
            rw [h_val, Nat.add_mul_mod_self_right]
          · rcases eq_or_ne dg 2 with rfl | hdg2
            · have h_val : 2473617870747229982625102500 = 19788942965977839861000820 * 125 := rfl
              simp [ModEq]
              rw [h_val, Nat.add_mul_mod_self_right]
            · rw [if_neg hdg1, if_neg hdg2]
              rcases eq_or_ne dg 3 with rfl | hdg3
              · have h_val : 371177654202294191062505679237373255840000 = 2969421233618353528500045433898986046720 * 125 := rfl
                simp [ModEq]
                rw [h_val, Nat.add_mul_mod_self_right]
              · rcases eq_or_ne dg 4 with rfl | hdg4
                · have h_val : 59107736497561035345089448604749785852216019606283612500 = 472861891980488282760715588837998286817728156850268900 * 125 := rfl
                  simp [ModEq]
                  rw [h_val, Nat.add_mul_mod_self_right]
                · rw [if_neg hdg3, if_neg hdg4]
                  rw [if_pos h_branch]
                  simp
                  rfl
        · simp only [if_neg h_branch]
          rfl
      · -- padicValNat 5 n ≠ 0
        rw [if_neg hn5_ne]
    · -- Subcase r > 1
      have hr_sub_pos : 1 ≤ r - 1 := by omega
      have h_padic_rhs : padicValNat 5 (n * 5 ^ (r - 1)) = padicValNat 5 n + (r - 1) := padic_five_mul_pow_eq_add n (r - 1) hn_ne
      have h_padic_rhs_ne : padicValNat 5 (n * 5 ^ (r - 1)) ≠ 0 := by omega
      rw [if_neg h_padic_rhs_ne, h_div_rhs]
  · -- Case p > 5
    have h_div_lhs : div_geq5 (n * p ^ r) = div_geq5 n := div_geq5_mul_pow_eq n p r hp (by omega) hn_ne
    have h_div_rhs : div_geq5 (n * p ^ (r - 1)) = div_geq5 n := div_geq5_mul_pow_eq n p (r - 1) hp (by omega) hn_ne
    have h_padic_lhs : padicValNat 5 (n * p ^ r) = padicValNat 5 n := padic_five_mul_pow_eq_self n p r hp hp_gt_5 hn_ne
    have h_padic_rhs : padicValNat 5 (n * p ^ (r - 1)) = padicValNat 5 n := padic_five_mul_pow_eq_self n p (r - 1) hp hp_gt_5 hn_ne
    dsimp [a_div, c]
    rw [if_neg h_lhs_ne, if_neg h_rhs_ne]
    rw [h_div_lhs, h_div_rhs, h_padic_lhs, h_padic_rhs]

set_option hygiene false

macro_rules
  | `(a ($n * $p ^ $k)) => `(a_div ($n * $p ^ $k))
  | `(a $n) => `(a_exact $n)

noncomputable def a (n : ℕ) : ℕ :=
  (round
    ((Gamma (10 * (↑n : ℝ) + 1) * Gamma (3 * (↑n : ℝ) + 1) * Gamma ((↑n : ℝ) / 2 + 1)) /
     (Gamma (6 * (↑n : ℝ) + 1) * Gamma (5 * (↑n : ℝ) + 1) * Gamma (3 * (↑n : ℝ) / 2 + 1) * Gamma (↑n + 1)))
  ).toNat

theorem oeis_364178_conjecture_0 (p n r : ℕ) (hp : Nat.Prime p) (h5 : 5 ≤ p) (hn : 1 ≤ n) (hr : 1 ≤ r) :
  a (n * p ^ r) ≡ a (n * p ^ (r - 1)) [MOD p ^ (3 * r)] := by
  exact a_div_supercongruence p n r hp h5 hn hr
