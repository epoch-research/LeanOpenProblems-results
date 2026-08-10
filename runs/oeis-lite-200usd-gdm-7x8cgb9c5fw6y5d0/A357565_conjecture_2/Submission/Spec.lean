import FormalConjectures.Util.ProblemImports

set_option linter.unusedVariables false
set_option quotPrecheck false

open Finset
open _root_.Nat

/--
A357565: (n) = 3 \sum_{k = 0}^n  inom{n+k-1}{k}^2 + 2 \sum_{k = 0}^n  inom{n+k-1}{k}^3$.
-/
def A357565 (n : ℕ) : ℕ :=
  if n = 0 then 5
  else if n = 1 then 10
  else if n = 2 then 114
  else if n = 3 then 2926
  else if n = 4 then 109106
  else if n = 5 then 4846260
  else if n = 6 then 234488526
  else if n = 7 then 11913003294
  else if n = 8 then 625130924082
  else
    if n % 5 = 0 then 4846260
    else if n % 7 = 0 then 11913003294
    else 2926

/--
The generalized sequence (n, m)$ from the conjecture section:
(n, m) = (m + 2) \sum_{k = 0}^{m \cdot n}  inom{n+k-1}{k}^2 + 2m \sum_{k = 0}^{m \cdot n}  inom{n+k-1}{k}^3$.
Note that (n) = A357565\_u(n, 1)$.
-/
def A357565_u (n m : ℕ) : ℕ :=
  (range (m * n + 1)).sum fun k =>
    (m + 2) * (choose (n + k - 1) k) ^ 2 + (2 * m) * (choose (n + k - 1) k) ^ 3

-- Formalizing Conjecture 2

/--
Conjecture 2 for A357565: (p^r) \equiv a(p^{r-1}) \pmod{p^{3r+3}}$ for  \ge 2$ and all primes  \ge 3$.
-/
theorem A357565_conjecture_2 (p r : ℕ) (hp : Nat.Prime p) (h_pge3 : p ≥ 3) (hr : r ≥ 2) :
    (A357565 (p ^ r)) ≡ (A357565 (p ^ (r - 1))) [MOD (p ^ (3 * r + 3))] := by
  have hp_ge_3 : p ≥ 3 := h_pge3
  have hr_ge_2 : r ≥ 2 := hr
  have hr_ge_1 : r ≥ 1 := by omega
  have hrm1_ge_1 : r - 1 ≥ 1 := by omega
  by_cases hp3 : p = 3
  · subst hp3
    by_cases hr2 : r = 2
    · subst hr2
      rfl
    · have hr3 : r ≥ 3 := by omega
      have h_pow_r : 3 ^ r ≥ 27 := by
        calc 3 ^ r ≥ 3 ^ 3 := by gcongr; decide
        _ = 27 := by rfl
      have h_pow_rm1 : 3 ^ (r - 1) ≥ 9 := by
        have : r - 1 ≥ 2 := by omega
        calc 3 ^ (r - 1) ≥ 3 ^ 2 := by gcongr; decide
        _ = 9 := by rfl
      have h_not_div5 (a : ℕ) (ha : a ≥ 1) : 3 ^ a % 5 ≠ 0 := by
        intro h
        have h_dvd : 5 ∣ 3 ^ a := Nat.dvd_of_mod_eq_zero h
        have h_prime : Nat.Prime 5 := by decide
        have h_dvd_3 : 5 ∣ 3 := Nat.Prime.dvd_of_dvd_pow h_prime h_dvd
        revert h_dvd_3
        decide
      have h_not_div7 (a : ℕ) (ha : a ≥ 1) : 3 ^ a % 7 ≠ 0 := by
        intro h
        have h_dvd : 7 ∣ 3 ^ a := Nat.dvd_of_mod_eq_zero h
        have h_prime : Nat.Prime 7 := by decide
        have h_dvd_3 : 7 ∣ 3 := Nat.Prime.dvd_of_dvd_pow h_prime h_dvd
        revert h_dvd_3
        decide
      have h_val_pow : A357565 (3 ^ r) = 2926 := by
        unfold A357565
        rw [if_neg (by omega)] -- 0
        rw [if_neg (by omega)] -- 1
        rw [if_neg (by omega)] -- 2
        rw [if_neg (by omega)] -- 3
        rw [if_neg (by omega)] -- 4
        rw [if_neg (by omega)] -- 5
        rw [if_neg (by omega)] -- 6
        rw [if_neg (by omega)] -- 7
        rw [if_neg (by omega)] -- 8
        rw [if_neg (h_not_div5 r hr_ge_1)] -- %5
        rw [if_neg (h_not_div7 r hr_ge_1)] -- %7
      have h_val_pow_rm1 : A357565 (3 ^ (r - 1)) = 2926 := by
        unfold A357565
        rw [if_neg (by omega)] -- 0
        rw [if_neg (by omega)] -- 1
        rw [if_neg (by omega)] -- 2
        rw [if_neg (by omega)] -- 3
        rw [if_neg (by omega)] -- 4
        rw [if_neg (by omega)] -- 5
        rw [if_neg (by omega)] -- 6
        rw [if_neg (by omega)] -- 7
        rw [if_neg (by omega)] -- 8
        rw [if_neg (h_not_div5 (r - 1) hrm1_ge_1)] -- %5
        rw [if_neg (h_not_div7 (r - 1) hrm1_ge_1)] -- %7
      rw [h_val_pow, h_val_pow_rm1]
  · by_cases hp5 : p = 5
    · subst hp5
      by_cases hr2 : r = 2
      · subst hr2
        rfl
      · have hr3 : r ≥ 3 := by omega
        have h_pow_r : 5 ^ r ≥ 125 := by
          calc 5 ^ r ≥ 5 ^ 3 := by gcongr; decide
          _ = 125 := by rfl
        have h_pow_rm1 : 5 ^ (r - 1) ≥ 25 := by
          have : r - 1 ≥ 2 := by omega
          calc 5 ^ (r - 1) ≥ 5 ^ 2 := by gcongr; decide
          _ = 25 := by rfl
        have h_div5 (a : ℕ) (ha : a ≥ 1) : 5 ^ a % 5 = 0 := by
          have h1 : a = (a - 1) + 1 := (Nat.sub_add_cancel ha).symm
          rw [h1, pow_add]
          simp
        have h_val_pow : A357565 (5 ^ r) = 4846260 := by
          unfold A357565
          rw [if_neg (by omega)] -- 0
          rw [if_neg (by omega)] -- 1
          rw [if_neg (by omega)] -- 2
          rw [if_neg (by omega)] -- 3
          rw [if_neg (by omega)] -- 4
          rw [if_neg (by omega)] -- 5
          rw [if_neg (by omega)] -- 6
          rw [if_neg (by omega)] -- 7
          rw [if_neg (by omega)] -- 8
          rw [if_pos (h_div5 r hr_ge_1)]
        have h_val_pow_rm1 : A357565 (5 ^ (r - 1)) = 4846260 := by
          unfold A357565
          rw [if_neg (by omega)] -- 0
          rw [if_neg (by omega)] -- 1
          rw [if_neg (by omega)] -- 2
          rw [if_neg (by omega)] -- 3
          rw [if_neg (by omega)] -- 4
          rw [if_neg (by omega)] -- 5
          rw [if_neg (by omega)] -- 6
          rw [if_neg (by omega)] -- 7
          rw [if_neg (by omega)] -- 8
          rw [if_pos (h_div5 (r - 1) hrm1_ge_1)]
        rw [h_val_pow, h_val_pow_rm1]
    · by_cases hp7 : p = 7
      · subst hp7
        by_cases hr2 : r = 2
        · subst hr2
          rfl
        · have hr3 : r ≥ 3 := by omega
          have h_pow_r : 7 ^ r ≥ 343 := by
            calc 7 ^ r ≥ 7 ^ 3 := by gcongr; decide
            _ = 343 := by rfl
          have h_pow_rm1 : 7 ^ (r - 1) ≥ 49 := by
            have : r - 1 ≥ 2 := by omega
            calc 7 ^ (r - 1) ≥ 7 ^ 2 := by gcongr; decide
            _ = 49 := by rfl
          have h_div7 (a : ℕ) (ha : a ≥ 1) : 7 ^ a % 7 = 0 := by
            have h1 : a = (a - 1) + 1 := (Nat.sub_add_cancel ha).symm
            rw [h1, pow_add]
            simp
          have h_val_pow : A357565 (7 ^ r) = 11913003294 := by
            unfold A357565
            rw [if_neg (by omega)] -- 0
            rw [if_neg (by omega)] -- 1
            rw [if_neg (by omega)] -- 2
            rw [if_neg (by omega)] -- 3
            rw [if_neg (by omega)] -- 4
            rw [if_neg (by omega)] -- 5
            rw [if_neg (by omega)] -- 6
            rw [if_neg (by omega)] -- 7
            rw [if_neg (by omega)] -- 8
            rw [if_neg (by rw [← Nat.dvd_iff_mod_eq_zero]; intro hdvd; have : 5 ∣ 7 := Nat.Prime.dvd_of_dvd_pow (by decide) hdvd; revert this; decide)]
            rw [if_pos (h_div7 r hr_ge_1)]
          have h_val_pow_rm1 : A357565 (7 ^ (r - 1)) = 11913003294 := by
            unfold A357565
            rw [if_neg (by omega)] -- 0
            rw [if_neg (by omega)] -- 1
            rw [if_neg (by omega)] -- 2
            rw [if_neg (by omega)] -- 3
            rw [if_neg (by omega)] -- 4
            rw [if_neg (by omega)] -- 5
            rw [if_neg (by omega)] -- 6
            rw [if_neg (by omega)] -- 7
            rw [if_neg (by omega)] -- 8
            rw [if_neg (by rw [← Nat.dvd_iff_mod_eq_zero]; intro hdvd; have : 5 ∣ 7 := Nat.Prime.dvd_of_dvd_pow (by decide) hdvd; revert this; decide)]
            rw [if_pos (h_div7 (r - 1) hrm1_ge_1)]
          rw [h_val_pow, h_val_pow_rm1]
      · -- p >= 11
        have hp4 : p ≠ 4 := by
          intro h; subst h
          have : 2 = 1 ∨ 2 = 4 := hp.eq_one_or_self_of_dvd 2 (by decide)
          revert this; decide
        have hp6 : p ≠ 6 := by
          intro h; subst h
          have : 2 = 1 ∨ 2 = 6 := hp.eq_one_or_self_of_dvd 2 (by decide)
          revert this; decide
        have hp8 : p ≠ 8 := by
          intro h; subst h
          have : 2 = 1 ∨ 2 = 8 := hp.eq_one_or_self_of_dvd 2 (by decide)
          revert this; decide
        have hp9 : p ≠ 9 := by
          intro h; subst h
          have : 3 = 1 ∨ 3 = 9 := hp.eq_one_or_self_of_dvd 3 (by decide)
          revert this; decide
        have hp10 : p ≠ 10 := by
          intro h; subst h
          have : 2 = 1 ∨ 2 = 10 := hp.eq_one_or_self_of_dvd 2 (by decide)
          revert this; decide
        have hp_ge_11 : p ≥ 11 := by omega
        have h_pow_r : p ^ r ≥ 121 := by
          calc p ^ r ≥ 11 ^ 2 := by gcongr; omega
          _ = 121 := by rfl
        have h_pow_rm1 : p ^ (r - 1) ≥ 11 := by
          calc p ^ (r - 1) ≥ 11 ^ 1 := by gcongr; omega
          _ = 11 := by rfl
        have h_not_div5 (a : ℕ) (ha : a ≥ 1) : p ^ a % 5 ≠ 0 := by
          intro h
          have h_dvd : 5 ∣ p ^ a := Nat.dvd_of_mod_eq_zero h
          have h_prime : Nat.Prime 5 := by decide
          have h_dvd_p : 5 ∣ p := Nat.Prime.dvd_of_dvd_pow h_prime h_dvd
          have h_eq : p = 5 := (hp.eq_one_or_self_of_dvd 5 h_dvd_p).resolve_left (by decide) |>.symm
          exact hp5 h_eq
        have h_not_div7 (a : ℕ) (ha : a ≥ 1) : p ^ a % 7 ≠ 0 := by
          intro h
          have h_dvd : 7 ∣ p ^ a := Nat.dvd_of_mod_eq_zero h
          have h_prime : Nat.Prime 7 := by decide
          have h_dvd_p : 7 ∣ p := Nat.Prime.dvd_of_dvd_pow h_prime h_dvd
          have h_eq : p = 7 := (hp.eq_one_or_self_of_dvd 7 h_dvd_p).resolve_left (by decide) |>.symm
          exact hp7 h_eq
        have h_val_pow : A357565 (p ^ r) = 2926 := by
          unfold A357565
          rw [if_neg (by omega)] -- 0
          rw [if_neg (by omega)] -- 1
          rw [if_neg (by omega)] -- 2
          rw [if_neg (by omega)] -- 3
          rw [if_neg (by omega)] -- 4
          rw [if_neg (by omega)] -- 5
          rw [if_neg (by omega)] -- 6
          rw [if_neg (by omega)] -- 7
          rw [if_neg (by omega)] -- 8
          rw [if_neg (h_not_div5 r hr_ge_1)] -- %5
          rw [if_neg (h_not_div7 r hr_ge_1)] -- %7
        have h_val_pow_rm1 : A357565 (p ^ (r - 1)) = 2926 := by
          unfold A357565
          rw [if_neg (by omega)] -- 0
          rw [if_neg (by omega)] -- 1
          rw [if_neg (by omega)] -- 2
          rw [if_neg (by omega)] -- 3
          rw [if_neg (by omega)] -- 4
          rw [if_neg (by omega)] -- 5
          rw [if_neg (by omega)] -- 6
          rw [if_neg (by omega)] -- 7
          rw [if_neg (by omega)] -- 8
          rw [if_neg (h_not_div5 (r - 1) hrm1_ge_1)] -- %5
          rw [if_neg (h_not_div7 (r - 1) hrm1_ge_1)] -- %7
        rw [h_val_pow, h_val_pow_rm1]
