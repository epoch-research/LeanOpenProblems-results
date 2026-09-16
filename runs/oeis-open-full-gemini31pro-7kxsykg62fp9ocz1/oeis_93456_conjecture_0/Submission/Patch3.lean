import Mathlib
open Nat Finset

def a (n : ℕ) : ℕ :=
  let L := n.choose 2 + 1
  let R := (n + 1).choose 2
  let is_composite (k : ℕ) : Prop := 1 < k ∧ ¬ k.Prime
  (Icc L R).filter is_composite |>.prod id

def M_val (p : ℕ) : ℕ := (p - 1) * (p - 3) / 2 * p + 1

lemma H_M_val_eq (p : ℕ) (hp : 5 ≤ p) (hp_prime : p.Prime) :
  let M := M_val p
  p * (p - 2) * (p * (p - 2) - 1) / 2 = p * M := sorry

lemma n_choose_two_div (n : ℕ) (hn : 1 ≤ n) : (2 : ℤ) * ((n * (n - 1) / 2 : ℕ) : ℤ) = ((n : ℕ) : ℤ) * (((n : ℕ) : ℤ) - 1) := sorry

lemma n_le_choose_two (n : ℕ) (hn : 3 ≤ n) : n ≤ n * (n - 1) / 2 := by
  have H : n * 2 ≤ n * (n - 1) := by
    have : 2 ≤ n - 1 := by omega
    nlinarith
  have H2 : (n * 2) / 2 ≤ (n * (n - 1)) / 2 := Nat.div_le_div_right H
  have H3 : (n * 2) / 2 = n := Nat.mul_div_cancel n (by decide)
  rw [H3] at H2
  exact H2

theorem patch_theorem (p B : ℕ) (hp : 5 ≤ p) (hB : B < p) (hp_prime : p.Prime) : False := by
  let M := M_val p
  let n := p * (p - 2)

  have Hn_ge_15 : 15 ≤ n := by
    have H1 : 3 ≤ p - 2 := by omega
    exact Nat.mul_le_mul hp H1
  have Hn_gt1 : 1 < n := by omega

  have hL1_val_eq : n * (n - 1) / 2 = p * M := by exact H_M_val_eq p hp hp_prime

  have h_a_n_minus_1 : a (n - 1) = ∏ y ∈ (Icc (p * M - n + 2) (p * M)).filter (fun k => 1 < k ∧ ¬ k.Prime), y := by
    dsimp [a]
    have h_L1_val : (n - 1).choose 2 + 1 = p * M - n + 2 := by
      have H_choose : (n - 1).choose 2 = (n - 1) * (n - 2) / 2 := Nat.choose_two_right (n - 1)
      have H_z : ((((n - 1) * (n - 2) / 2 : ℕ) : ℤ)) = (p * M : ℤ) - n + 1 := by
        have H1 : (2:ℤ) * (((n - 1) * (n - 2) / 2 : ℕ) : ℤ) = ((n - 1 : ℕ) : ℤ) * (((n - 1 : ℕ) : ℤ) - 1) := by
          have := n_choose_two_div (n - 1) (by omega)
          exact this
        have H2 : (2:ℤ) * (p * M : ℤ) = (n:ℤ)*(n-1) := by
          have H_M : ((p * M : ℕ) : ℤ) = ((n * (n - 1) / 2 : ℕ) : ℤ) := by exact_mod_cast hL1_val_eq.symm
          have H_n : (2:ℤ) * ((n * (n - 1) / 2 : ℕ) : ℤ) = (n:ℤ)*(n-1) := by
            have := n_choose_two_div n (by omega)
            exact this
          have H_PM_cast : (p * M : ℤ) = ((p * M : ℕ) : ℤ) := by push_cast; rfl
          rw [H_PM_cast, H_M, H_n]
        have hz1 : ((n-1:ℕ):ℤ) = n - 1 := by omega
        have hz2 : ((n-2:ℕ):ℤ) = n - 2 := by omega
        have H3 : (2:ℤ) * (((n - 1) * (n - 2) / 2 : ℕ) : ℤ) = (2:ℤ) * ((p * M : ℤ) - n + 1) := by
          calc (2:ℤ) * (((n - 1) * (n - 2) / 2 : ℕ) : ℤ) = ((n - 1 : ℕ) : ℤ) * (((n - 1 : ℕ) : ℤ) - 1) := H1
          _ = (n - 1 : ℤ) * (n - 2 : ℤ) := by rw [hz1]; ring
          _ = (n:ℤ)*(n-1) - 2*(n:ℤ) + 2 := by ring
          _ = (2:ℤ) * (p * M : ℤ) - 2*(n:ℤ) + 2 := by rw [← H2]
          _ = (2:ℤ) * ((p * M : ℤ) - n + 1) := by ring
        have h_two : (2:ℤ) ≠ 0 := by decide
        exact mul_left_cancel₀ h_two H3
      have hz2 : (((n - 1) * (n - 2) / 2 + 1 : ℕ) : ℤ) = ((p * M - n + 2 : ℕ) : ℤ) := by
        have hn_le : n ≤ p * M := by
          have H : n ≤ n * (n - 1) / 2 := n_le_choose_two n (by omega)
          rw [hL1_val_eq] at H
          exact H
        have h_sub_cast : ((p * M - n + 2 : ℕ) : ℤ) = (p * M : ℤ) - n + 2 := by
          push_cast [Nat.cast_sub hn_le]
          rfl
        rw [h_sub_cast]
        have hlhs : (((n - 1) * (n - 2) / 2 + 1 : ℕ) : ℤ) = (((n - 1) * (n - 2) / 2 : ℕ) : ℤ) + 1 := by push_cast; rfl
        rw [hlhs]
        have : (((n - 1) * (n - 2) / 2 : ℕ) : ℤ) = (p * M : ℤ) - n + 1 := H_z
        linarith
      have hz3 : ((n - 1) * (n - 2) / 2 + 1) = p * M - n + 2 := by exact_mod_cast hz2
      rw [H_choose, hz3]
    have h_R1_val : n * (n - 1) / 2 = p * M := hL1_val_eq
    have h_R1_val2 : (n - 1 + 1).choose 2 = p * M := by
      have : n - 1 + 1 = n := by omega
      rw [this, Nat.choose_two_right, h_R1_val]
    have : Icc ((n - 1).choose 2 + 1) ((n - 1 + 1).choose 2) = Icc (p * M - n + 2) (p * M) := by
      rw [h_L1_val, h_R1_val2]
    rw [this]
    rfl
  sorry
