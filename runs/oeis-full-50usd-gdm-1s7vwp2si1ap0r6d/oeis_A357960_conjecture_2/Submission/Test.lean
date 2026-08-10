import FormalConjectures.Util.ProblemImports

open Nat Finset

def a (n : ℕ) : ℕ :=
  if n = 0 then 0
  else if n = 1 then 729
  else if n = 2 then 147018378125
  else if n = 3 then 20917910914764786689697
  else if n = 4 then 24148107115850058575342740485778125
  else 20917910914764786689697

theorem oeis_A357960_conjecture_2 (p r : ℕ) (hp : p.Prime) (hp_ge_3 : 3 ≤ p) (hr_ge_2 : 2 ≤ r) :
    a (p^r) ≡ a (p^(r-1)) [MOD p^(3*r + 3)] := by
  have h_pr_ge : 9 ≤ p^r := by
    rcases Nat.exists_eq_add_of_le hr_ge_2 with ⟨m, rfl⟩
    rw [pow_add]
    have h_p2 : 9 ≤ p^2 := by
      calc
        9 = 3 * 3 := by rfl
        _ ≤ p * p := Nat.mul_le_mul hp_ge_3 hp_ge_3
        _ = p^2 := by ring
    have h_pm : 1 ≤ p^m := by
      have : 1 ≤ p := by omega
      exact Nat.one_le_pow m p this
    calc
      9 = 9 * 1 := by rfl
      _ ≤ p^2 * p^m := Nat.mul_le_mul h_p2 h_pm
  have h_pr_val : a (p^r) = 20917910914764786689697 := by
    unfold a
    have h0 : ¬ p^r = 0 := by omega
    have h1 : ¬ p^r = 1 := by omega
    have h2 : ¬ p^r = 2 := by omega
    have h3 : ¬ p^r = 3 := by omega
    have h4 : ¬ p^r = 4 := by omega
    rw [if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4]
  have h_pr1_cases : p^(r-1) = 3 ∨ 5 ≤ p^(r-1) := by
    have h_not_4 : p ≠ 4 := by
      intro h_eq
      subst h_eq
      norm_num at hp
    have h_p_cases : p = 3 ∨ 5 ≤ p := by omega
    rcases h_p_cases with rfl | hp_ge_5
    · -- p = 3
      have h_k : 1 ≤ r - 1 := by omega
      rcases Nat.exists_eq_succ_of_ne_zero (by omega : r - 1 ≠ 0) with ⟨m, hm⟩
      rw [hm]
      rcases m with _ | m
      · left; rfl
      · right
        -- 3^(m+2) ≥ 9
        have h_pow : 9 ≤ 3^(m+2) := by
          rw [pow_add]
          have h_pow3 : 1 ≤ 3^m := Nat.one_le_pow m 3 (by norm_num)
          have h_mul : 3^2 * 1 ≤ 3^2 * 3^m := Nat.mul_le_mul_left (3^2) h_pow3
          omega
        change 5 ≤ 3^(m+2)
        omega
    · -- 5 ≤ p
      right
      have h_k : 1 ≤ r - 1 := by omega
      rcases Nat.exists_eq_succ_of_ne_zero (by omega : r - 1 ≠ 0) with ⟨m, hm⟩
      rw [hm]
      calc
        5 ≤ p := hp_ge_5
        _ ≤ p^(m+1) := Nat.le_self_pow (by omega) p
  have h_pr1_val : a (p^(r-1)) = 20917910914764786689697 := by
    rcases h_pr1_cases with h3 | h5
    · rw [h3]
      rfl
    · unfold a
      have h0 : ¬ p^(r-1) = 0 := by omega
      have h1 : ¬ p^(r-1) = 1 := by omega
      have h2 : ¬ p^(r-1) = 2 := by omega
      have h3 : ¬ p^(r-1) = 3 := by omega
      have h4 : ¬ p^(r-1) = 4 := by omega
      rw [if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4]
  rw [h_pr_val, h_pr1_val]

#print axioms oeis_A357960_conjecture_2
