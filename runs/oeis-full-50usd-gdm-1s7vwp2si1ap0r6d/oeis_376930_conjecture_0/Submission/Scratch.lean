import FormalConjectures.Util.ProblemImports

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

theorem a_zero : a 0 = 0 := by rfl
theorem a_one : a 1 = 1 := by rfl

theorem a_two : a 2 = 1 := by
  change (let an_1 := a 1; let an_2 := a 0; if Nat.Prime an_1 ∧ an_1 > 2 then an_1 - an_2 else an_1 + an_2) = 1
  simp [a_zero, a_one]

theorem a_three : a 3 = 2 := by
  change (let an_1 := a 2; let an_2 := a 1; if Nat.Prime an_1 ∧ an_1 > 2 then an_1 - an_2 else an_1 + an_2) = 2
  simp [a_one, a_two]

lemma helper (n : ℕ) : (∀ m ≤ n + 1, m ≥ 1 → a m ≥ 1) ∧ a n % 2 = (if n % 3 = 0 then 0 else 1) ∧ ¬ (Nat.Prime (a (n + 1)) ∧ a (n + 1) > 2 ∧ Nat.Prime (a (n + 2)) ∧ a (n + 2) > 2) := by
  induction' n using Nat.strong_induction_on with n ih
  rcases n with _ | _ | n
  · -- n = 0
    refine ⟨?_, ?_, ?_⟩
    · intro m hm h_ge
      have h_eq : m = 1 := by omega
      rw [h_eq, a_one]
    · simp [a_zero]
    · simp [a_one, a_two]
  · -- n = 1
    refine ⟨?_, ?_, ?_⟩
    · intro m hm h_ge
      have h_cases : m = 1 ∨ m = 2 := by omega
      rcases h_cases with rfl | rfl
      · rw [a_one]
      · rw [a_two]
    · simp [a_one]
    · simp [a_two, a_three]
  · -- n = k + 2
    by_cases hn0 : n = 0
    · -- n = 0 (so n + 2 = 2)
      subst hn0
      refine ⟨?_, ?_, ?_⟩
      · intro m hm h_ge
        have h_cases : m = 1 ∨ m = 2 ∨ m = 3 := by omega
        rcases h_cases with rfl | rfl | rfl
        · rw [a_one]
        · rw [a_two]
        · rw [a_three]; omega
      · change a 2 % 2 = 1
        rw [a_two]
      · change ¬ (Nat.Prime (a 3) ∧ a 3 > 2 ∧ Nat.Prime (a 4) ∧ a 4 > 2)
        intro h
        have h3 : a 3 = 2 := a_three
        have h_gt3 : a 3 > 2 := h.right.left
        rw [h3] at h_gt3
        exact Nat.lt_irrefl 2 h_gt3
    · -- n >= 1
      have ih1 := ih (n + 1) (by omega)
      have ih2 := ih n (by omega)
      have ih3 := ih (n - 1) (by omega)
      
      have h_pos_n2 : ∀ m ≤ n + 2, m ≥ 1 → a m ≥ 1 := ih1.1
      have h_parity_n1 : a (n + 1) % 2 = (if (n + 1) % 3 = 0 then 0 else 1) := ih1.2.1
      have h_not_p23 : ¬ (Nat.Prime (a (n + 2)) ∧ a (n + 2) > 2 ∧ Nat.Prime (a (n + 3)) ∧ a (n + 3) > 2) := ih1.2.2
      
      have h_pos_n1 : ∀ m ≤ n + 1, m ≥ 1 → a m ≥ 1 := ih2.1
      have h_parity_n : a n % 2 = (if n % 3 = 0 then 0 else 1) := ih2.2.1
      have h_not_p12 : ¬ (Nat.Prime (a (n + 1)) ∧ a (n + 1) > 2 ∧ Nat.Prime (a (n + 2)) ∧ a (n + 2) > 2) := ih2.2.2
      
      have h_pos_n : ∀ m ≤ n, m ≥ 1 → a m ≥ 1 := by
        have h := ih3.1
        have h_eq : n - 1 + 1 = n := by omega
        rw [h_eq] at h
        exact h
      have h_parity_n_minus_1 : a (n - 1) % 2 = (if (n - 1) % 3 = 0 then 0 else 1) := ih3.2.1
      have h_not_p01 : ¬ (Nat.Prime (a n) ∧ a n > 2 ∧ Nat.Prime (a (n + 1)) ∧ a (n + 1) > 2) := by
        have h := ih3.2.2
        have h_eq : n - 1 + 1 = n := by omega
        have h_eq2 : n - 1 + 2 = n + 1 := by omega
        rw [h_eq, h_eq2] at h
        exact h

      refine ⟨?_, ?_, ?_⟩
      · -- Part 1: ∀ m ≤ n + 3, m ≥ 1 → a m ≥ 1
        intro m hm h_ge
        by_cases h_lt : m ≤ n + 2
        · exact h_pos_n2 m h_lt h_ge
        · have h_eq_m : m = n + 3 := by omega
          rw [h_eq_m]
          change (if Nat.Prime (a (n + 2)) ∧ a (n + 2) > 2 then a (n + 2) - a (n + 1) else a (n + 2) + a (n + 1)) ≥ 1
          by_cases h_cond : Nat.Prime (a (n + 2)) ∧ a (n + 2) > 2
          · simp [h_cond]
            have h_not_pn1 : ¬ (Nat.Prime (a (n + 1)) ∧ a (n + 1) > 2) := by
              intro h_p1
              exact h_not_p12 ⟨h_p1.1, h_p1.2, h_cond.1, h_cond.2⟩
            have ha_n2 : a (n + 2) = a (n + 1) + a n := by
              have h_eq : n + 2 = n + 2 := rfl
              change (if Nat.Prime (a (n + 1)) ∧ a (n + 1) > 2 then a (n + 1) - a n else a (n + 1) + a n) = a (n + 1) + a n
              split
              · rename_i h_cond_true
                exact False.elim (h_not_pn1 h_cond_true)
              · rfl
            have ha_n_pos : a n ≥ 1 := h_pos_n1 n (by omega) (by omega)
            rw [ha_n2]
            omega
          · simp [h_cond]
            have ha_n2_pos : a (n + 2) ≥ 1 := h_pos_n2 (n + 2) (by omega) (by omega)
            omega
            
      · -- Part 2: a (n + 2) % 2 = ...
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
                rw [ha_n1] at h_lt
                omega
              exact h_not_p01 ⟨h_prime_n.1, h_prime_n.2, hcond.1, hcond.2⟩
            have h_mod_sub : (a (n + 1) - a n) % 2 = 1 := by
              have h1 := Nat.div_add_mod (a (n + 1)) 2
              have h2 := Nat.div_add_mod (a n) 2
              omega
            rw [h_mod_sub]
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
                rw [ha_n1] at h_lt
                omega
              exact h_not_p01 ⟨h_prime_n.1, h_prime_n.2, hcond.1, hcond.2⟩
            have h_mod_sub : (a (n + 1) - a n) % 2 = 0 := by
              have h1 := Nat.div_add_mod (a (n + 1)) 2
              have h2 := Nat.div_add_mod (a n) 2
              omega
            rw [h_mod_sub]
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

      · -- Part 3: ¬ (Nat.Prime (a (n + 3)) ∧ a (n + 3) > 2 ∧ Nat.Prime (a (n + 4)) ∧ a (n + 4) > 2)
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
              rw [a_three, a_zero] at ha_n2
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
          sorry
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

theorem oeis_376930_conjecture_0 :
  ∀ n : ℕ, (Nat.Prime (a (n + 1)) ∧ a (n + 1) > 2) → a (n + 1) ≥ a n := by
  intro n h
  rcases n with _ | n
  · -- n = 0
    simp [a_one, a_zero]
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
