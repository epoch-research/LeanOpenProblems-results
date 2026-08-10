import FormalConjectures.Util.ProblemImports
set_option maxRecDepth 5000

open Nat

/--
A376930: $a(0)=0, a(1)=1$; for $n>1$, $a(n) = a(n-1)+a(n-2)$, except where $a(n-1)$ is a prime greater than 2, in which case $a(n) = a(n-1)-a(n-2)$.
-/
noncomputable def a : ℕ → ℕ
| 0 => 0
| 1 => 1
| n + 2 =>
  let an_1 := a (n + 1)
  let an_2 := a n
  if Nat.Prime an_1 ∧ an_1 > 2 then
    an_1 - an_2
  else
    an_1 + an_2

theorem a_0 : a 0 = 0 := rfl
theorem a_1 : a 1 = 1 := rfl

def a_loop : ℕ → ℕ → ℕ → ℕ
| 0, curr, _ => curr
| k + 1, curr, prev =>
  let next := if Nat.Prime curr ∧ curr > 2 then curr - prev else curr + prev
  a_loop k next curr

theorem a_loop_spec (k : ℕ) (j : ℕ) (curr prev : ℕ) (h1 : prev = a j) (h2 : curr = a (j + 1)) :
  a_loop k curr prev = a (j + 1 + k) := by
  induction' k with k ih generalizing j curr prev
  · simp [a_loop]
    rw [h2]
  · simp [a_loop]
    have h_next : (if Nat.Prime curr ∧ curr > 2 then curr - prev else curr + prev) = a (j + 2) := by
      rw [h2, h1]
      rfl
    have ih_inst := ih (j + 1) (a (j + 2)) (a (j + 1)) rfl rfl
    rw [h_next, h2]
    rw [ih_inst]
    have h_eq : j + 1 + 1 + k = j + 1 + (k + 1) := by omega
    rw [h_eq]

theorem a_eq_a_loop (k : ℕ) : a (k + 1) = a_loop k 1 0 := by
  have h := a_loop_spec k 0 1 0 a_0 a_1
  have h_eq : 0 + 1 + k = k + 1 := by omega
  rw [h_eq] at h
  exact h.symm

theorem cond_2 : ¬ (Nat.Prime (a 1) ∧ a 1 > 2) := by
  rw [a_1]
  decide

theorem a_2 : a 2 = 1 := by
  rw [a_eq_a_loop 1]
  decide

theorem cond_3 : ¬ (Nat.Prime (a 2) ∧ a 2 > 2) := by
  rw [a_2]
  decide

theorem a_3 : a 3 = 2 := by
  rw [a_eq_a_loop 2]
  decide

theorem cond_4 : ¬ (Nat.Prime (a 3) ∧ a 3 > 2) := by
  rw [a_3]
  decide

theorem a_4 : a 4 = 3 := by
  rw [a_eq_a_loop 3]
  decide

theorem cond_5 : Nat.Prime (a 4) ∧ a 4 > 2 := by
  rw [a_4]
  decide

theorem a_5 : a 5 = 1 := by
  rw [a_eq_a_loop 4]
  decide

theorem cond_6 : ¬ (Nat.Prime (a 5) ∧ a 5 > 2) := by
  rw [a_5]
  decide

theorem a_6 : a 6 = 4 := by
  rw [a_eq_a_loop 5]
  decide

theorem cond_7 : ¬ (Nat.Prime (a 6) ∧ a 6 > 2) := by
  intro h
  have h_eq : a 6 = 2 * 2 := by rw [a_6]
  have h_not : ¬ Nat.Prime (a 6) := by
    rw [h_eq]
    apply Nat.not_prime_mul <;> decide
  exact h_not h.1

theorem a_7 : a 7 = 5 := by
  have h : a 7 = if Nat.Prime (a 6) ∧ a 6 > 2 then a 6 - a 5 else a 6 + a 5 := rfl
  rw [h]
  have h_cond : ¬ (Nat.Prime (a 6) ∧ a 6 > 2) := cond_7
  rw [if_neg h_cond]
  rw [a_6, a_5]

theorem cond_8 : Nat.Prime (a 7) ∧ a 7 > 2 := by
  rw [a_7]
  decide

theorem a_8 : a 8 = 1 := by
  have h : a 8 = if Nat.Prime (a 7) ∧ a 7 > 2 then a 7 - a 6 else a 7 + a 6 := rfl
  rw [h]
  have h_cond : Nat.Prime (a 7) ∧ a 7 > 2 := cond_8
  rw [if_pos h_cond]
  rw [a_7, a_6]

theorem cond_9 : ¬ (Nat.Prime (a 8) ∧ a 8 > 2) := by
  rw [a_8]
  decide

theorem a_9 : a 9 = 6 := by
  have h : a 9 = if Nat.Prime (a 8) ∧ a 8 > 2 then a 8 - a 7 else a 8 + a 7 := rfl
  rw [h]
  have h_cond : ¬ (Nat.Prime (a 8) ∧ a 8 > 2) := cond_9
  rw [if_neg h_cond]
  rw [a_8, a_7]

theorem cond_10 : ¬ (Nat.Prime (a 9) ∧ a 9 > 2) := by
  intro h
  have h_eq : a 9 = 2 * 3 := by rw [a_9]
  have h_not : ¬ Nat.Prime (a 9) := by
    rw [h_eq]
    apply Nat.not_prime_mul <;> decide
  exact h_not h.1

theorem a_10 : a 10 = 7 := by
  have h : a 10 = if Nat.Prime (a 9) ∧ a 9 > 2 then a 9 - a 8 else a 9 + a 8 := rfl
  rw [h]
  have h_cond : ¬ (Nat.Prime (a 9) ∧ a 9 > 2) := cond_10
  rw [if_neg h_cond]
  rw [a_9, a_8]

theorem cond_11 : Nat.Prime (a 10) ∧ a 10 > 2 := by
  rw [a_10]
  decide

theorem a_11 : a 11 = 1 := by
  have h : a 11 = if Nat.Prime (a 10) ∧ a 10 > 2 then a 10 - a 9 else a 10 + a 9 := rfl
  rw [h]
  have h_cond : Nat.Prime (a 10) ∧ a 10 > 2 := cond_11
  rw [if_pos h_cond]
  rw [a_10, a_9]

theorem cond_12 : ¬ (Nat.Prime (a 11) ∧ a 11 > 2) := by
  rw [a_11]
  decide

theorem a_12 : a 12 = 8 := by
  have h : a 12 = if Nat.Prime (a 11) ∧ a 11 > 2 then a 11 - a 10 else a 11 + a 10 := rfl
  rw [h]
  have h_cond : ¬ (Nat.Prime (a 11) ∧ a 11 > 2) := cond_12
  rw [if_neg h_cond]
  rw [a_11, a_10]

theorem cond_13 : ¬ (Nat.Prime (a 12) ∧ a 12 > 2) := by
  intro h
  have h_eq : a 12 = 2 * 4 := by rw [a_12]
  have h_not : ¬ Nat.Prime (a 12) := by
    rw [h_eq]
    apply Nat.not_prime_mul <;> decide
  exact h_not h.1

theorem a_13 : a 13 = 9 := by
  have h : a 13 = if Nat.Prime (a 12) ∧ a 12 > 2 then a 12 - a 11 else a 12 + a 11 := rfl
  rw [h]
  have h_cond : ¬ (Nat.Prime (a 12) ∧ a 12 > 2) := cond_13
  rw [if_neg h_cond]
  rw [a_12, a_11]

theorem cond_14 : ¬ (Nat.Prime (a 13) ∧ a 13 > 2) := by
  intro h
  have h_eq : a 13 = 3 * 3 := by rw [a_13]
  have h_not : ¬ Nat.Prime (a 13) := by
    rw [h_eq]
    apply Nat.not_prime_mul <;> decide
  exact h_not h.1

theorem a_14 : a 14 = 17 := by
  have h : a 14 = if Nat.Prime (a 13) ∧ a 13 > 2 then a 13 - a 12 else a 13 + a 12 := rfl
  rw [h]
  have h_cond : ¬ (Nat.Prime (a 13) ∧ a 13 > 2) := cond_14
  rw [if_neg h_cond]
  rw [a_13, a_12]

theorem cond_15 : Nat.Prime (a 14) ∧ a 14 > 2 := by
  rw [a_14]
  decide

theorem a_15 : a 15 = 8 := by
  have h : a 15 = if Nat.Prime (a 14) ∧ a 14 > 2 then a 14 - a 13 else a 14 + a 13 := rfl
  rw [h]
  have h_cond : Nat.Prime (a 14) ∧ a 14 > 2 := cond_15
  rw [if_pos h_cond]
  rw [a_14, a_13]

theorem cond_16 : ¬ (Nat.Prime (a 15) ∧ a 15 > 2) := by
  intro h
  have h_eq : a 15 = 2 * 4 := by rw [a_15]
  have h_not : ¬ Nat.Prime (a 15) := by
    rw [h_eq]
    apply Nat.not_prime_mul <;> decide
  exact h_not h.1

theorem a_16 : a 16 = 25 := by
  have h : a 16 = if Nat.Prime (a 15) ∧ a 15 > 2 then a 15 - a 14 else a 15 + a 14 := rfl
  rw [h]
  have h_cond : ¬ (Nat.Prime (a 15) ∧ a 15 > 2) := cond_16
  rw [if_neg h_cond]
  rw [a_15, a_14]

theorem cond_17 : ¬ (Nat.Prime (a 16) ∧ a 16 > 2) := by
  intro h
  have h_eq : a 16 = 5 * 5 := by rw [a_16]
  have h_not : ¬ Nat.Prime (a 16) := by
    rw [h_eq]
    apply Nat.not_prime_mul <;> decide
  exact h_not h.1

theorem a_17 : a 17 = 33 := by
  have h : a 17 = if Nat.Prime (a 16) ∧ a 16 > 2 then a 16 - a 15 else a 16 + a 15 := rfl
  rw [h]
  have h_cond : ¬ (Nat.Prime (a 16) ∧ a 16 > 2) := cond_17
  rw [if_neg h_cond]
  rw [a_16, a_15]

theorem cond_18 : ¬ (Nat.Prime (a 17) ∧ a 17 > 2) := by
  intro h
  have h_eq : a 17 = 3 * 11 := by rw [a_17]
  have h_not : ¬ Nat.Prime (a 17) := by
    rw [h_eq]
    apply Nat.not_prime_mul <;> decide
  exact h_not h.1

theorem a_18 : a 18 = 58 := by
  have h : a 18 = if Nat.Prime (a 17) ∧ a 17 > 2 then a 17 - a 16 else a 17 + a 16 := rfl
  rw [h]
  have h_cond : ¬ (Nat.Prime (a 17) ∧ a 17 > 2) := cond_18
  rw [if_neg h_cond]
  rw [a_17, a_16]

theorem cond_19 : ¬ (Nat.Prime (a 18) ∧ a 18 > 2) := by
  intro h
  have h_eq : a 18 = 2 * 29 := by rw [a_18]
  have h_not : ¬ Nat.Prime (a 18) := by
    rw [h_eq]
    apply Nat.not_prime_mul <;> decide
  exact h_not h.1

theorem a_19 : a 19 = 91 := by
  have h : a 19 = if Nat.Prime (a 18) ∧ a 18 > 2 then a 18 - a 17 else a 18 + a 17 := rfl
  rw [h]
  have h_cond : ¬ (Nat.Prime (a 18) ∧ a 18 > 2) := cond_19
  rw [if_neg h_cond]
  rw [a_18, a_17]

theorem cond_20 : ¬ (Nat.Prime (a 19) ∧ a 19 > 2) := by
  intro h
  have h_eq : a 19 = 7 * 13 := by rw [a_19]
  have h_not : ¬ Nat.Prime (a 19) := by
    rw [h_eq]
    apply Nat.not_prime_mul <;> decide
  exact h_not h.1

theorem a_20 : a 20 = 149 := by
  have h : a 20 = if Nat.Prime (a 19) ∧ a 19 > 2 then a 19 - a 18 else a 19 + a 18 := rfl
  rw [h]
  have h_cond : ¬ (Nat.Prime (a 19) ∧ a 19 > 2) := cond_20
  rw [if_neg h_cond]
  rw [a_19, a_18]

theorem cond_21 : Nat.Prime (a 20) ∧ a 20 > 2 := by
  rw [a_20]
  decide

theorem a_21 : a 21 = 58 := by
  have h : a 21 = if Nat.Prime (a 20) ∧ a 20 > 2 then a 20 - a 19 else a 20 + a 19 := rfl
  rw [h]
  have h_cond : Nat.Prime (a 20) ∧ a 20 > 2 := cond_21
  rw [if_pos h_cond]
  rw [a_20, a_19]

theorem cond_22 : ¬ (Nat.Prime (a 21) ∧ a 21 > 2) := by
  intro h
  have h_eq : a 21 = 2 * 29 := by rw [a_21]
  have h_not : ¬ Nat.Prime (a 21) := by
    rw [h_eq]
    apply Nat.not_prime_mul <;> decide
  exact h_not h.1

theorem a_22 : a 22 = 207 := by
  have h : a 22 = if Nat.Prime (a 21) ∧ a 21 > 2 then a 21 - a 20 else a 21 + a 20 := rfl
  rw [h]
  have h_cond : ¬ (Nat.Prime (a 21) ∧ a 21 > 2) := cond_22
  rw [if_neg h_cond]
  rw [a_21, a_20]

theorem cond_23 : ¬ (Nat.Prime (a 22) ∧ a 22 > 2) := by
  intro h
  have h_eq : a 22 = 3 * 69 := by rw [a_22]
  have h_not : ¬ Nat.Prime (a 22) := by
    rw [h_eq]
    apply Nat.not_prime_mul <;> decide
  exact h_not h.1

theorem a_23 : a 23 = 265 := by
  have h : a 23 = if Nat.Prime (a 22) ∧ a 22 > 2 then a 22 - a 21 else a 22 + a 21 := rfl
  rw [h]
  have h_cond : ¬ (Nat.Prime (a 22) ∧ a 22 > 2) := cond_23
  rw [if_neg h_cond]
  rw [a_22, a_21]

theorem cond_24 : ¬ (Nat.Prime (a 23) ∧ a 23 > 2) := by
  intro h
  have h_eq : a 23 = 5 * 53 := by rw [a_23]
  have h_not : ¬ Nat.Prime (a 23) := by
    rw [h_eq]
    apply Nat.not_prime_mul <;> decide
  exact h_not h.1

theorem a_24 : a 24 = 472 := by
  have h : a 24 = if Nat.Prime (a 23) ∧ a 23 > 2 then a 23 - a 22 else a 23 + a 22 := rfl
  rw [h]
  have h_cond : ¬ (Nat.Prime (a 23) ∧ a 23 > 2) := cond_24
  rw [if_neg h_cond]
  rw [a_23, a_22]

theorem cond_25 : ¬ (Nat.Prime (a 24) ∧ a 24 > 2) := by
  intro h
  have h_eq : a 24 = 2 * 236 := by rw [a_24]
  have h_not : ¬ Nat.Prime (a 24) := by
    rw [h_eq]
    apply Nat.not_prime_mul <;> decide
  exact h_not h.1

theorem a_25 : a 25 = 737 := by
  have h : a 25 = if Nat.Prime (a 24) ∧ a 24 > 2 then a 24 - a 23 else a 24 + a 23 := rfl
  rw [h]
  have h_cond : ¬ (Nat.Prime (a 24) ∧ a 24 > 2) := cond_25
  rw [if_neg h_cond]
  rw [a_24, a_23]

theorem cond_26 : ¬ (Nat.Prime (a 25) ∧ a 25 > 2) := by
  intro h
  have h_eq : a 25 = 11 * 67 := by rw [a_25]
  have h_not : ¬ Nat.Prime (a 25) := by
    rw [h_eq]
    apply Nat.not_prime_mul <;> decide
  exact h_not h.1

theorem a_26 : a 26 = 1209 := by
  have h : a 26 = if Nat.Prime (a 25) ∧ a 25 > 2 then a 25 - a 24 else a 25 + a 24 := rfl
  rw [h]
  have h_cond : ¬ (Nat.Prime (a 25) ∧ a 25 > 2) := cond_26
  rw [if_neg h_cond]
  rw [a_25, a_24]

theorem cond_27 : ¬ (Nat.Prime (a 26) ∧ a 26 > 2) := by
  intro h
  have h_eq : a 26 = 3 * 403 := by rw [a_26]
  have h_not : ¬ Nat.Prime (a 26) := by
    rw [h_eq]
    apply Nat.not_prime_mul <;> decide
  exact h_not h.1

theorem a_27 : a 27 = 1946 := by
  have h : a 27 = if Nat.Prime (a 26) ∧ a 26 > 2 then a 26 - a 25 else a 26 + a 25 := rfl
  rw [h]
  have h_cond : ¬ (Nat.Prime (a 26) ∧ a 26 > 2) := cond_27
  rw [if_neg h_cond]
  rw [a_26, a_25]

theorem cond_28 : ¬ (Nat.Prime (a 27) ∧ a 27 > 2) := by
  intro h
  have h_eq : a 27 = 2 * 973 := by rw [a_27]
  have h_not : ¬ Nat.Prime (a 27) := by
    rw [h_eq]
    apply Nat.not_prime_mul <;> decide
  exact h_not h.1

theorem a_28 : a 28 = 3155 := by
  have h : a 28 = if Nat.Prime (a 27) ∧ a 27 > 2 then a 27 - a 26 else a 27 + a 26 := rfl
  rw [h]
  have h_cond : ¬ (Nat.Prime (a 27) ∧ a 27 > 2) := cond_28
  rw [if_neg h_cond]
  rw [a_27, a_26]


lemma helper (n : ℕ) : (∀ m ≤ n + 4, m ≥ 1 → a m ≥ 1) ∧ a n % 2 = (if n % 3 = 0 then 0 else 1) ∧ ¬ (Nat.Prime (a (n + 1)) ∧ a (n + 1) > 2 ∧ Nat.Prime (a (n + 2)) ∧ a (n + 2) > 2) := by
  induction' n using Nat.strong_induction_on with n ih
  rcases n with _ | _ | n
  · -- n = 0
    refine ⟨?_, ?_, ?_⟩
    · intro m hm h_ge
      rcases m with _ | m
      · contradiction
      · rcases m with _ | m
        · rw [a_1]
        · rcases m with _ | m
          · rw [a_2]
          · rcases m with _ | m
            · rw [a_3]; omega
            · rcases m with _ | m
              · rw [a_4]; omega
              · omega
    · simp [a_0]
    · simp [a_1, a_2]
  · -- n = 1
    refine ⟨?_, ?_, ?_⟩
    · intro m hm h_ge
      rcases m with _ | m
      · contradiction
      · rcases m with _ | m
        · rw [a_1]
        · rcases m with _ | m
          · rw [a_2]
          · rcases m with _ | m
            · rw [a_3]; omega
            · rcases m with _ | m
              · rw [a_4]; omega
              · rcases m with _ | m
                · rw [a_5]
                · omega
    · simp [a_1]
    · simp [a_2, a_3]
  · -- n = k + 2
    by_cases hn0 : n = 0
    · -- n = 0 (so n + 2 = 2)
      subst hn0
      refine ⟨?_, ?_, ?_⟩
      · intro m hm h_ge
        rcases m with _ | m
        · contradiction
        · rcases m with _ | m
          · rw [a_1]
          · rcases m with _ | m
            · rw [a_2]
            · rcases m with _ | m
              · rw [a_3]; omega
              · rcases m with _ | m
                · rw [a_4]; omega
                · rcases m with _ | m
                  · rw [a_5]
                  · rcases m with _ | m
                    · rw [a_6]; omega
                    · omega
      · change a 2 % 2 = 1
        rw [a_2]
      · change ¬ (Nat.Prime (a 3) ∧ a 3 > 2 ∧ Nat.Prime (a 4) ∧ a 4 > 2)
        intro h
        have h3 : a 3 = 2 := a_3
        have h_gt3 : a 3 > 2 := h.right.left
        rw [h3] at h_gt3
        exact Nat.lt_irrefl 2 h_gt3
    · -- n >= 1
      have ih1 := ih (n + 1) (by omega)
      have ih2 := ih n (by omega)
      have ih3 := ih (n - 1) (by omega)
      
      have h_pos_n2 : ∀ m ≤ n + 5, m ≥ 1 → a m ≥ 1 := ih1.1
      have h_parity_n1 : a (n + 1) % 2 = (if (n + 1) % 3 = 0 then 0 else 1) := ih1.2.1
      have h_not_p23 : ¬ (Nat.Prime (a (n + 2)) ∧ a (n + 2) > 2 ∧ Nat.Prime (a (n + 3)) ∧ a (n + 3) > 2) := ih1.2.2
      
      have h_pos_n1 : ∀ m ≤ n + 4, m ≥ 1 → a m ≥ 1 := ih2.1
      have h_parity_n : a n % 2 = (if n % 3 = 0 then 0 else 1) := ih2.2.1
      have h_not_p12 : ¬ (Nat.Prime (a (n + 1)) ∧ a (n + 1) > 2 ∧ Nat.Prime (a (n + 2)) ∧ a (n + 2) > 2) := ih2.2.2
      
      have h_pos_n : ∀ m ≤ n + 3, m ≥ 1 → a m ≥ 1 := by
        have h := ih3.1
        have h_eq : n - 1 + 4 = n + 3 := by omega
        rw [h_eq] at h
        exact h
      have h_parity_n_minus_1 : a (n - 1) % 2 = (if (n - 1) % 3 = 0 then 0 else 1) := ih3.2.1
      have h_not_p01 : ¬ (Nat.Prime (a n) ∧ a n > 2 ∧ Nat.Prime (a (n + 1)) ∧ a (n + 1) > 2) := by
        have h := ih3.2.2
        have h_eq : n - 1 + 1 = n := by omega
        have h_eq2 : n - 1 + 2 = n + 1 := by omega
        rw [h_eq, h_eq2] at h
        exact h

      have h_mod_sub (A B : ℕ) (hAB : A ≥ B) : (A - B) % 2 = (A + B) % 2 := by omega

      have h_parity_n2 : a (n + 2) % 2 = if (n + 2) % 3 = 0 then 0 else 1 := by
        change (if Nat.Prime (a (n + 1)) ∧ a (n + 1) > 2 then a (n + 1) - a n else a (n + 1) + a n) % 2 = if (n + 2) % 3 = 0 then 0 else 1
        have hn_cases : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
        rcases hn_cases with h0 | h1 | h2
        · -- n % 3 = 0
          have h_par_n1 : a (n + 1) % 2 = 1 := by
            have h_eq : (n + 1) % 3 = 1 := by omega
            rw [h_eq] at h_parity_n1
            exact h_parity_n1
          have h_par_n : a n % 2 = 0 := by
            rw [h0] at h_parity_n
            exact h_parity_n
          by_cases hcond : Nat.Prime (a (n + 1)) ∧ a (n + 1) > 2
          · simp [hcond]
            have ha_ge : a (n + 1) ≥ a n := by
              by_contra h_lt
              have h_prime_n : Nat.Prime (a n) ∧ a n > 2 := by
                by_contra h_not_pn
                have ha_n1 : a (n + 1) = a n + a (n - 1) := by
                  have h_eq4 : n = n - 1 + 1 := by omega
                  have h_eq3 : n + 1 = n - 1 + 2 := by omega
                  rw [h_eq3]
                  change (if Nat.Prime (a (n - 1 + 1)) ∧ a (n - 1 + 1) > 2 then a (n - 1 + 1) - a (n - 1) else a (n - 1 + 1) + a (n - 1)) = a n + a (n - 1)
                  rw [h_eq4]
                  split
                  · rename_i h_cond_true
                    have h_eq5 : n - 1 + 1 - 1 + 1 = n := by omega
                    rw [h_eq5] at h_cond_true
                    exact False.elim (h_not_pn h_cond_true)
                  · rfl
                omega
              exact h_not_p01 ⟨h_prime_n.1, h_prime_n.2, hcond.1, hcond.2⟩
            rw [h_mod_sub (a (n + 1)) (a n) ha_ge]
            split <;> omega
          · simp [hcond]
            have h_mod_add : (a (n + 1) + a n) % 2 = 1 := by
              have h1 := Nat.div_add_mod (a (n + 1)) 2
              have h2 := Nat.div_add_mod (a n) 2
              omega
            rw [h_mod_add]
            split <;> omega
        · -- n % 3 = 1
          have h_par_n1 : a (n + 1) % 2 = 1 := by
            have h_eq : (n + 1) % 3 = 2 := by omega
            rw [h_eq] at h_parity_n1
            exact h_parity_n1
          have h_par_n : a n % 2 = 1 := by
            have h_eq : n % 3 = 1 := by omega
            rw [h_eq] at h_parity_n
            exact h_parity_n
          by_cases hcond : Nat.Prime (a (n + 1)) ∧ a (n + 1) > 2
          · simp [hcond]
            have ha_ge : a (n + 1) ≥ a n := by
              by_contra h_lt
              have h_prime_n : Nat.Prime (a n) ∧ a n > 2 := by
                by_contra h_not_pn
                have ha_n1 : a (n + 1) = a n + a (n - 1) := by
                  have h_eq4 : n = n - 1 + 1 := by omega
                  have h_eq3 : n + 1 = n - 1 + 2 := by omega
                  rw [h_eq3]
                  change (if Nat.Prime (a (n - 1 + 1)) ∧ a (n - 1 + 1) > 2 then a (n - 1 + 1) - a (n - 1) else a (n - 1 + 1) + a (n - 1)) = a n + a (n - 1)
                  rw [h_eq4]
                  split
                  · rename_i h_cond_true
                    have h_eq5 : n - 1 + 1 - 1 + 1 = n := by omega
                    rw [h_eq5] at h_cond_true
                    exact False.elim (h_not_pn h_cond_true)
                  · rfl
                omega
              exact h_not_p01 ⟨h_prime_n.1, h_prime_n.2, hcond.1, hcond.2⟩
            rw [h_mod_sub (a (n + 1)) (a n) ha_ge]
            split <;> omega
          · simp [hcond]
            have h_mod_add : (a (n + 1) + a n) % 2 = 0 := by
              have h1 := Nat.div_add_mod (a (n + 1)) 2
              have h2 := Nat.div_add_mod (a n) 2
              omega
            rw [h_mod_add]
            split <;> omega
        · -- n % 3 = 2
          have h_par_n1 : a (n + 1) % 2 = 0 := by
            have h_eq : (n + 1) % 3 = 0 := by omega
            rw [h_eq] at h_parity_n1
            exact h_parity_n1
          have h_par_n : a n % 2 = 1 := by
            have h_eq : n % 3 = 2 := by omega
            rw [h_eq] at h_parity_n
            exact h_parity_n
          have hcond_false : ¬ (Nat.Prime (a (n + 1)) ∧ a (n + 1) > 2) := by
            intro h_cond
            have h_odd : a (n + 1) % 2 = 1 := by
              rcases Nat.Prime.eq_two_or_odd h_cond.1 with h_two | h_odd
              · omega
              · exact h_odd
            omega
          simp [hcond_false]
          have h_mod_add : (a (n + 1) + a n) % 2 = 1 := by
            have h1 := Nat.div_add_mod (a (n + 1)) 2
            have h2 := Nat.div_add_mod (a n) 2
            omega
          rw [h_mod_add]
          split <;> omega

      have h_not_p34 : ¬ (Nat.Prime (a (n + 3)) ∧ a (n + 3) > 2 ∧ Nat.Prime (a (n + 4)) ∧ a (n + 4) > 2) := by
        intro h_cond
        have h_p3 : Nat.Prime (a (n + 3)) ∧ a (n + 3) > 2 := ⟨h_cond.1, h_cond.2.1⟩
        have h_p4 : Nat.Prime (a (n + 4)) ∧ a (n + 4) > 2 := ⟨h_cond.2.2.1, h_cond.2.2.2⟩
        have h_not_p2 : ¬ (Nat.Prime (a (n + 2)) ∧ a (n + 2) > 2) := by
          intro h_p2
          exact h_not_p23 ⟨h_p2.1, h_p2.2, h_p3.1, h_p3.2⟩
        
        have ha_n3 : a (n + 3) = a (n + 2) + a (n + 1) := by
          have h_eq3 : n + 3 = n + 1 + 2 := by omega
          rw [h_eq3]
          change (if Nat.Prime (a (n + 1 + 1)) ∧ a (n + 1 + 1) > 2 then a (n + 1 + 1) - a (n + 1) else a (n + 1 + 1) + a (n + 1)) = a (n + 2) + a (n + 1)
          have h_eq4 : n + 1 + 1 = n + 2 := by omega
          rw [h_eq4]
          split
          · rename_i h_cond_true
            exact False.elim (h_not_p2 h_cond_true)
          · rfl
        
        have ha_n4 : a (n + 4) = a (n + 1) := by
          have h_eq4 : n + 4 = n + 2 + 2 := by omega
          rw [h_eq4]
          change (if Nat.Prime (a (n + 2 + 1)) ∧ a (n + 2 + 1) > 2 then a (n + 2 + 1) - a (n + 2) else a (n + 2 + 1) + a (n + 2)) = a (n + 1)
          have h_eq5 : n + 2 + 1 = n + 3 := by omega
          rw [h_eq5]
          split
          · rw [ha_n3]
            omega
          · rename_i h_cond_false
            exact False.elim (h_cond_false h_p3)
            
        have h_p1 : Nat.Prime (a (n + 1)) ∧ a (n + 1) > 2 := by
          rw [ha_n4] at h_p4
          exact h_p4
          
        have h_not_p0 : ¬ (Nat.Prime (a n) ∧ a n > 2) := by
          intro h_p0
          exact h_not_p01 ⟨h_p0.1, h_p0.2, h_p1.1, h_p1.2⟩
          
        have ha_n1 : a (n + 1) = a n + a (n - 1) := by
          have h_eq1 : n + 1 = n - 1 + 2 := by omega
          rw [h_eq1]
          change (if Nat.Prime (a (n - 1 + 1)) ∧ a (n - 1 + 1) > 2 then a (n - 1 + 1) - a (n - 1) else a (n - 1 + 1) + a (n - 1)) = a n + a (n - 1)
          have h_eq2 : n - 1 + 1 = n := by omega
          rw [h_eq2]
          split
          · rename_i h_cond_true
            exact False.elim (h_not_p0 h_cond_true)
          · rfl
          
        have ha_n2 : a (n + 2) = a (n - 1) := by
          change (if Nat.Prime (a (n + 1)) ∧ a (n + 1) > 2 then a (n + 1) - a n else a (n + 1) + a n) = a (n - 1)
          split
          · rw [ha_n1]
            omega
          · rename_i h_cond_false
            exact False.elim (h_cond_false h_p1)
            
        have hn_cases : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
        rcases hn_cases with h0 | h1 | h2
        · -- n % 3 = 0
          have h_par_n1 : a (n + 1) % 2 = 1 := by
            rcases Nat.Prime.eq_two_or_odd h_p1.1 with h_two | h_odd
            · omega
            · exact h_odd
          have h_par_n2 : a (n + 2) % 2 = 1 := by
            rw [ha_n2]
            have h_eq : (n - 1) % 3 = 2 := by omega
            rw [h_eq] at h_parity_n_minus_1
            exact h_parity_n_minus_1
          have h_par_n3 : a (n + 3) % 2 = 0 := by
            rw [ha_n3]
            have h_mod_add : (a (n + 2) + a (n + 1)) % 2 = 0 := by
              have h1_mod := Nat.div_add_mod (a (n + 2)) 2
              have h2_mod := Nat.div_add_mod (a (n + 1)) 2
              omega
            exact h_mod_add
          have h_odd_n3 : a (n + 3) % 2 = 1 := by
            rcases Nat.Prime.eq_two_or_odd h_p3.1 with h_two | h_odd
            · omega
            · exact h_odd
          omega
        · -- n % 3 = 1
          have h_par_n_minus_1 : a (n - 1) % 2 = 0 := by
            have h_eq : (n - 1) % 3 = 0 := by omega
            rw [h_eq] at h_parity_n_minus_1
            exact h_parity_n_minus_1
          have h_par_n2 : a (n + 2) % 2 = 0 := by
            rw [ha_n2]
            exact h_par_n_minus_1
          have h_par_n3 : a (n + 3) % 2 = 1 := by
            rcases Nat.Prime.eq_two_or_odd h_p3.1 with h_two | h_odd
            · omega
            · exact h_odd
          have h_par_n3_calc : a (n + 3) % 2 = 1 := by
            rw [ha_n3]
            have h_par_n1 : a (n + 1) % 2 = 1 := by
              rcases Nat.Prime.eq_two_or_odd h_p1.1 with h_two | h_odd
              · omega
              · exact h_odd
            have h_mod_add : (a (n + 2) + a (n + 1)) % 2 = 1 := by
              have h1_mod := Nat.div_add_mod (a (n + 2)) 2
              have h2_mod := Nat.div_add_mod (a (n + 1)) 2
              omega
            exact h_mod_add
          have h_pos_n_minus_1 : a (n - 1) ≥ 1 := by
            by_cases hn_ge_4 : n ≥ 4
            · exact h_pos_n (n - 1) (by omega) (by omega)
            · -- Since n >= 1 and n % 3 = 1 and n < 4, n must be 1.
              have hn_eq_1 : n = 1 := by omega
              rw [hn_eq_1] at ha_n2
              change a 3 = a 0 at ha_n2
              rw [a_3, a_0] at ha_n2
              contradiction
          have h_pos_n_minus_1_even : a (n - 1) ≥ 2 := by
            have h1_mod := Nat.div_add_mod (a (n - 1)) 2
            omega
          have ha_n2_ge_2 : a (n + 2) ≥ 2 := by
            rw [ha_n2]
            exact h_pos_n_minus_1_even
          have ha_n3_gt_n1 : a (n + 3) > a (n + 1) := by
            rw [ha_n3]
            omega
          have ha_n5 : a (n + 5) = 0 := by
            have h_eq5 : n + 5 = n + 3 + 2 := by omega
            rw [h_eq5]
            change (if Nat.Prime (a (n + 3 + 1)) ∧ a (n + 3 + 1) > 2 then a (n + 3 + 1) - a (n + 3) else a (n + 3 + 1) + a (n + 3)) = 0
            have h_eq6 : n + 3 + 1 = n + 4 := by omega
            rw [h_eq6]
            split
            · rw [ha_n4]
              omega
            · rename_i h_cond_false
              exact False.elim (h_cond_false h_p4)
          by_cases hn_lt : n < 25
          · interval_cases n <;> (try omega) <;> (revert h_cond; decide)
          · have h_prime_28 : ¬ Nat.Prime (a 28) := by
              intro hp
              have h_mul : 5 * 631 = a 28 := by
                rw [a_28]
              have h_not := Nat.not_prime_of_mul_eq h_mul (by decide) (by decide)
              exact h_not hp
            have h_n_ge_25 : n ≥ 25 := by omega
            by_cases hn_25 : n = 25
            · subst hn_25
              have h_not_p_28 : ¬ (Nat.Prime (a 28) ∧ a 28 > 2 ∧ Nat.Prime (a 29) ∧ a 29 > 2) := by
                intro h
                exact h_prime_28 h.1
              exact h_not_p_28 h_cond
            · have h_n_ge_28 : n ≥ 28 := by omega
              have ha_n5_pos : a (n + 5) ≥ 1 := h_pos_n2 (n + 5) (by omega) (by omega)
              omega
        · -- n % 3 = 2
          have h_par_n1 : a (n + 1) % 2 = 0 := by
            have h_eq : (n + 1) % 3 = 0 := by omega
            rw [h_eq] at h_parity_n1
            exact h_parity_n1
          have h_odd_n1 : a (n + 1) % 2 = 1 := by
            rcases Nat.Prime.eq_two_or_odd h_p1.1 with h_two | h_odd
            · omega
            · exact h_odd
          omega

      have a_parity_step (k : ℕ) (h_pos : a (k + 2) ≥ 1) : a (k + 2) % 2 = (a (k + 1) + a k) % 2 := by
        change (if Nat.Prime (a (k + 1)) ∧ a (k + 1) > 2 then a (k + 1) - a k else a (k + 1) + a k) % 2 = (a (k + 1) + a k) % 2
        by_cases h : Nat.Prime (a (k + 1)) ∧ a (k + 1) > 2
        · simp [h]
          have h_ge : a (k + 1) ≥ a k := by
            by_contra h_lt
            have h_eq : a (k + 2) = 0 := by
              change (if Nat.Prime (a (k + 1)) ∧ a (k + 1) > 2 then a (k + 1) - a k else a (k + 1) + a k) = 0
              simp [h]
              omega
            omega
          rw [h_mod_sub (a (k + 1)) (a k) h_ge]
        · simp [h]

      have h_parity_n3 : a (n + 3) % 2 = if (n + 3) % 3 = 0 then 0 else 1 := by
        have h_pos_n3_local : a (n + 3) ≥ 1 := h_pos_n2 (n + 3) (by omega) (by omega)
        rw [a_parity_step (n + 1) h_pos_n3_local]
        rw [Nat.add_mod]
        have hn_cases : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
        rcases hn_cases with h0 | h1 | h2
        · have h_par_n2 : a (n + 2) % 2 = 1 := by
            have h_eq : (n + 2) % 3 = 2 := by omega
            rw [h_eq] at h_parity_n2
            exact h_parity_n2
          have h_par_n1 : a (n + 1) % 2 = 1 := by
            have h_eq : (n + 1) % 3 = 1 := by omega
            rw [h_eq] at h_parity_n1
            exact h_parity_n1
          rw [h_par_n2, h_par_n1]
          have h_eq3 : (n + 3) % 3 = 0 := by omega
          rw [h_eq3]
          rfl
        · have h_par_n2 : a (n + 2) % 2 = 0 := by
            have h_eq : (n + 2) % 3 = 0 := by omega
            rw [h_eq] at h_parity_n2
            exact h_parity_n2
          have h_par_n1 : a (n + 1) % 2 = 1 := by
            have h_eq : (n + 1) % 3 = 2 := by omega
            rw [h_eq] at h_parity_n1
            exact h_parity_n1
          rw [h_par_n2, h_par_n1]
          have h_eq3 : (n + 3) % 3 = 1 := by omega
          rw [h_eq3]
          rfl
        · have h_par_n2 : a (n + 2) % 2 = 1 := by
            have h_eq : (n + 2) % 3 = 1 := by omega
            rw [h_eq] at h_parity_n2
            exact h_parity_n2
          have h_par_n1 : a (n + 1) % 2 = 0 := by
            have h_eq : (n + 1) % 3 = 0 := by omega
            rw [h_eq] at h_parity_n1
            exact h_parity_n1
          rw [h_par_n2, h_par_n1]
          have h_eq3 : (n + 3) % 3 = 2 := by omega
          rw [h_eq3]
          rfl

      have h_parity_n4 : a (n + 4) % 2 = if (n + 4) % 3 = 0 then 0 else 1 := by
        have h_pos_n4_local : a (n + 4) ≥ 1 := h_pos_n2 (n + 4) (by omega) (by omega)
        rw [a_parity_step (n + 2) h_pos_n4_local]
        rw [Nat.add_mod]
        have hn_cases : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
        rcases hn_cases with h0 | h1 | h2
        · have h_par_n3 : a (n + 3) % 2 = 0 := by
            have h_eq : (n + 3) % 3 = 0 := by omega
            rw [h_eq] at h_parity_n3
            exact h_parity_n3
          have h_par_n2 : a (n + 2) % 2 = 1 := by
            have h_eq : (n + 2) % 3 = 2 := by omega
            rw [h_eq] at h_parity_n2
            exact h_parity_n2
          rw [h_par_n3, h_par_n2]
          have h_eq4 : (n + 4) % 3 = 1 := by omega
          rw [h_eq4]
          rfl
        · have h_par_n3 : a (n + 3) % 2 = 1 := by
            have h_eq : (n + 3) % 3 = 1 := by omega
            rw [h_eq] at h_parity_n3
            exact h_parity_n3
          have h_par_n2 : a (n + 2) % 2 = 0 := by
            have h_eq : (n + 2) % 3 = 0 := by omega
            rw [h_eq] at h_parity_n2
            exact h_parity_n2
          rw [h_par_n3, h_par_n2]
          have h_eq4 : (n + 4) % 3 = 2 := by omega
          rw [h_eq4]
          rfl
        · have h_par_n3 : a (n + 3) % 2 = 1 := by
            have h_eq : (n + 3) % 3 = 2 := by omega
            rw [h_eq] at h_parity_n3
            exact h_parity_n3
          have h_par_n2 : a (n + 2) % 2 = 1 := by
            have h_eq : (n + 2) % 3 = 1 := by omega
            rw [h_eq] at h_parity_n2
            exact h_parity_n2
          rw [h_par_n3, h_par_n2]
          have h_eq4 : (n + 4) % 3 = 0 := by omega
          rw [h_eq4]
          rfl

      have h_parity_n5 : a (n + 5) % 2 = if (n + 5) % 3 = 0 then 0 else 1 := by
        have h_pos_n5_local : a (n + 5) ≥ 1 := h_pos_n2 (n + 5) (by omega) (by omega)
        rw [a_parity_step (n + 3) h_pos_n5_local]
        rw [Nat.add_mod]
        have hn_cases : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
        rcases hn_cases with h0 | h1 | h2
        · have h_par_n4 : a (n + 4) % 2 = 1 := by
            have h_eq : (n + 4) % 3 = 1 := by omega
            rw [h_eq] at h_parity_n4
            exact h_parity_n4
          have h_par_n3 : a (n + 3) % 2 = 0 := by
            have h_eq : (n + 3) % 3 = 0 := by omega
            rw [h_eq] at h_parity_n3
            exact h_parity_n3
          rw [h_par_n4, h_par_n3]
          have h_eq5 : (n + 5) % 3 = 2 := by omega
          rw [h_eq5]
          rfl
        · have h_par_n4 : a (n + 4) % 2 = 1 := by
            have h_eq : (n + 4) % 3 = 2 := by omega
            rw [h_eq] at h_parity_n4
            exact h_parity_n4
          have h_par_n3 : a (n + 3) % 2 = 1 := by
            have h_eq : (n + 3) % 3 = 1 := by omega
            rw [h_eq] at h_parity_n3
            exact h_parity_n3
          rw [h_par_n4, h_par_n3]
          have h_eq5 : (n + 5) % 3 = 0 := by omega
          rw [h_eq5]
          rfl
        · have h_par_n4 : a (n + 4) % 2 = 0 := by
            have h_eq : (n + 4) % 3 = 0 := by omega
            rw [h_eq] at h_parity_n4
            exact h_parity_n4
          have h_par_n3 : a (n + 3) % 2 = 1 := by
            have h_eq : (n + 3) % 3 = 2 := by omega
            rw [h_eq] at h_parity_n3
            exact h_parity_n3
          rw [h_par_n4, h_par_n3]
          have h_eq5 : (n + 5) % 3 = 1 := by omega
          rw [h_eq5]
          rfl

      have h_pos_n6 : a (n + 6) ≥ 1 := by
        have h_eq6 : n + 6 = n + 4 + 2 := by omega
        rw [h_eq6]
        change (if Nat.Prime (a (n + 5)) ∧ a (n + 5) > 2 then a (n + 5) - a (n + 4) else a (n + 5) + a (n + 4)) ≥ 1
        by_cases h_cond5 : Nat.Prime (a (n + 5)) ∧ a (n + 5) > 2
        · simp [h_cond5]
          have hn_cases : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
          rcases hn_cases with h0 | h1 | h2
          · -- n % 3 = 0
            by_cases h_cond4 : Nat.Prime (a (n + 4)) ∧ a (n + 4) > 2
            · -- Both a (n+4) and a (n+5) are prime > 2
              have h_not_p3 : ¬ (Nat.Prime (a (n + 3)) ∧ a (n + 3) > 2) := by
                intro h_p3
                have h_odd_n3 : a (n + 3) % 2 = 1 := by
                  rcases Nat.Prime.eq_two_or_odd h_p3.1 with h_two | h_odd
                  · omega
                  · exact h_odd
                have h_par_n3 : a (n + 3) % 2 = 0 := by
                  have h_eq : (n + 3) % 3 = 0 := by omega
                  rw [h_eq] at h_parity_n3
                  exact h_parity_n3
                omega
              have ha_n4 : a (n + 4) = a (n + 3) + a (n + 2) := by
                have h_eq4 : n + 4 = n + 2 + 2 := by omega
                rw [h_eq4]
                change (if Nat.Prime (a (n + 3)) ∧ a (n + 3) > 2 then a (n + 3) - a (n + 2) else a (n + 3) + a (n + 2)) = a (n + 3) + a (n + 2)
                simp [h_not_p3]
              have ha_n5 : a (n + 5) = a (n + 2) := by
                have h_eq5 : n + 5 = n + 3 + 2 := by omega
                rw [h_eq5]
                change (if Nat.Prime (a (n + 4)) ∧ a (n + 4) > 2 then a (n + 4) - a (n + 3) else a (n + 4) + a (n + 3)) = a (n + 2)
                rw [if_pos h_cond4]
                rw [ha_n4]
                omega
              have h_p2 : Nat.Prime (a (n + 2)) ∧ a (n + 2) > 2 := by
                rw [← ha_n5]
                exact h_cond5
              have h_not_p1 : ¬ (Nat.Prime (a (n + 1)) ∧ a (n + 1) > 2) := by
                intro h_p1
                exact h_not_p12 ⟨h_p1.1, h_p1.2, h_p2.1, h_p2.2⟩
              have ha_n2 : a (n + 2) = a (n + 1) + a n := by
                have h_eq : n + 2 = n + 2 := rfl
                change (if Nat.Prime (a (n + 1)) ∧ a (n + 1) > 2 then a (n + 1) - a n else a (n + 1) + a n) = a (n + 1) + a n
                simp [h_not_p1]
              have ha_n1 : a (n + 1) = a n + a (n - 1) := by
                have h_eq1 : n + 1 = n - 1 + 2 := by omega
                rw [h_eq1]
                change (if Nat.Prime (a (n - 1 + 1)) ∧ a (n - 1 + 1) > 2 then a (n - 1 + 1) - a (n - 1) else a (n - 1 + 1) + a (n - 1)) = a n + a (n - 1)
                have h_eq2 : n - 1 + 1 = n := by omega
                rw [h_eq2]
                have h_not_p0 : ¬ (Nat.Prime (a n) ∧ a n > 2) := by
                  intro h_p0
                  have h_odd_n : a n % 2 = 1 := by
                    rcases Nat.Prime.eq_two_or_odd h_p0.1 with h_two | h_odd
                    · omega
                    · exact h_odd
                  have h_par_n : a n % 2 = 0 := by
                    rw [h0] at h_parity_n
                    exact h_parity_n
                  omega
                simp [h_not_p0]
              have ha_n2_eq : a (n + 2) = 2 * a n + a (n - 1) := by omega
              have ha_n3_sub : a (n + 3) = a (n + 2) - a (n + 1) := by
                have h_eq3 : n + 3 = n + 1 + 2 := by omega
                rw [h_eq3]
                change (if Nat.Prime (a (n + 2)) ∧ a (n + 2) > 2 then a (n + 2) - a (n + 1) else a (n + 2) + a (n + 1)) = a (n + 2) - a (n + 1)
                simp [h_p2]
              have ha_n3_eq : a (n + 3) = a n := by omega
              have ha_n4_eq : a (n + 4) = 3 * a n + a (n - 1) := by omega
              have ha_n5_sub : a (n + 5) = a (n + 4) - a (n + 3) := by
                have h_eq5 : n + 5 = n + 3 + 2 := by omega
                rw [h_eq5]
                change (if Nat.Prime (a (n + 4)) ∧ a (n + 4) > 2 then a (n + 4) - a (n + 3) else a (n + 4) + a (n + 3)) = a (n + 4) - a (n + 3)
                rw [if_pos h_cond4]
              have ha_n4_gt : a (n + 4) > a (n + 5) := by
                rw [ha_n5_sub]
                have ha_n3_pos : a (n + 3) ≥ 1 := h_pos_n2 (n + 3) (by omega) (by omega)
                have ha_n4_pos : a (n + 4) ≥ 1 := h_pos_n2 (n + 4) (by omega) (by omega)
                omega
              omega
            · have ha_n5 : a (n + 5) = a (n + 4) + a (n + 3) := by
                have h_eq5 : n + 5 = n + 3 + 2 := by omega
                rw [h_eq5]
                change (if Nat.Prime (a (n + 4)) ∧ a (n + 4) > 2 then a (n + 4) - a (n + 3) else a (n + 4) + a (n + 3)) = a (n + 4) + a (n + 3)
                simp [h_cond4]
              rw [ha_n5]
              have ha_n3_pos : a (n + 3) ≥ 1 := h_pos_n2 (n + 3) (by omega) (by omega)
              omega
          · -- n % 3 = 1
            have h_par_n5 : a (n + 5) % 2 = 0 := by
              have h_eq : (n + 5) % 3 = 0 := by omega
              rw [h_eq] at h_parity_n5
              exact h_parity_n5
            have h_odd_n5 : a (n + 5) % 2 = 1 := by
              rcases Nat.Prime.eq_two_or_odd h_cond5.1 with h_two | h_odd
              · omega
              · exact h_odd
            omega
          · -- n % 3 = 2
            have h_not_p4 : ¬ (Nat.Prime (a (n + 4)) ∧ a (n + 4) > 2) := by
              intro h_p4
              have h_odd_n4 : a (n + 4) % 2 = 1 := by
                rcases Nat.Prime.eq_two_or_odd h_p4.1 with h_two | h_odd
                · omega
                · exact h_odd
              have h_par_n4 : a (n + 4) % 2 = 0 := by
                have h_eq : (n + 4) % 3 = 0 := by omega
                rw [h_eq] at h_parity_n4
                exact h_parity_n4
              omega
            have ha_n5 : a (n + 5) = a (n + 4) + a (n + 3) := by
              have h_eq5 : n + 5 = n + 3 + 2 := by omega
              rw [h_eq5]
              change (if Nat.Prime (a (n + 4)) ∧ a (n + 4) > 2 then a (n + 4) - a (n + 3) else a (n + 4) + a (n + 3)) = a (n + 4) + a (n + 3)
              simp [h_not_p4]
            have ha_n3_pos : a (n + 3) ≥ 1 := h_pos_n2 (n + 3) (by omega) (by omega)
            rw [ha_n5]
            omega
        · simp [h_cond5]
          have ha_n5_pos : a (n + 5) ≥ 1 := h_pos_n2 (n + 5) (by omega) (by omega)
          omega

      have h_pos_n5_all : ∀ m ≤ n + 6, m ≥ 1 → a m ≥ 1 := by
        intro m hm h_ge
        by_cases h_lt : m ≤ n + 5
        · exact h_pos_n2 m h_lt h_ge
        · have h_eq : m = n + 6 := by omega
          rw [h_eq]
          exact h_pos_n6

      refine ⟨h_pos_n5_all, h_parity_n2, h_not_p34⟩


theorem oeis_376930_conjecture_0 :
  ∀ n : ℕ, (Nat.Prime (a (n + 1)) ∧ a (n + 1) > 2) → a (n + 1) ≥ a n := by
  intro n h
  rcases n with _ | n
  · -- n = 0
    simp [a_1, a_0]
  · -- n = m + 1
    have h_help := helper n
    have h_not_p := h_help.2.2
    have h_not_pm1 : ¬ (Nat.Prime (a (n + 1)) ∧ a (n + 1) > 2) := by
      intro h_pm1
      exact h_not_p ⟨h_pm1.1, h_pm1.2, h.1, h.2⟩
    have ha_n2 : a (n + 2) = a (n + 1) + a n := by
      change (if Nat.Prime (a (n + 1)) ∧ a (n + 1) > 2 then a (n + 1) - a n else a (n + 1) + a n) = a (n + 1) + a n
      split
      · rename_i h_cond_true
        exact False.elim (h_not_pm1 h_cond_true)
      · rfl
    rw [ha_n2]
    omega

