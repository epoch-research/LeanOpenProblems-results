import Mathlib
open Nat Finset

def a (n : ℕ) : ℕ :=
  let L := n.choose 2 + 1
  let R := (n + 1).choose 2
  let is_composite (k : ℕ) : Prop := 1 < k ∧ ¬ k.Prime
  (Icc L R).filter is_composite |>.prod id

def M_val (p : ℕ) : ℕ := (p - 1) * (p - 3) / 2 * p + 1

lemma M_val_ge (p : ℕ) (hp : 5 ≤ p) : p ≤ M_val p := sorry
lemma M_val_mod (p : ℕ) : p ∣ M_val p - 1 := sorry

lemma H_M_val_eq (p : ℕ) (hp : 5 ≤ p) (hp_prime : p.Prime) :
  let M := M_val p
  p * (p - 2) * (p * (p - 2) - 1) / 2 = p * M := sorry

lemma n_choose_two_div (n : ℕ) (hn : 1 ≤ n) : (2 : ℤ) * ((n * (n - 1) / 2 : ℕ) : ℤ) = ((n : ℕ) : ℤ) * (((n : ℕ) : ℤ) - 1) := sorry

theorem patch_theorem (p B : ℕ) (hp : 5 ≤ p) (hB : B < p) (hp_prime : p.Prime) : False := by
  let M := M_val p
  let n := p * (p - 2)

  have Hn_gt1 : 1 < n := by
    have H1 : 3 ≤ p - 2 := by omega
    have H2 : 15 ≤ p * (p - 2) := Nat.mul_le_mul hp H1
    omega
  have Hn_gtB : B < n := by
    have H1 : 3 ≤ p - 2 := by omega
    have H2 : p * 1 ≤ p * (p - 2) := Nat.mul_le_mul_left p (by omega)
    have H3 : p ≤ p * (p - 2) := by omega
    omega

  have hM_ge : p ≤ M := M_val_ge p hp
  have hM_mod : p ∣ M - 1 := M_val_mod p
  
  have hL1_val_eq : n * (n - 1) / 2 = p * M := by
    exact H_M_val_eq p hp hp_prime
  
  have h_a_n : a n = ∏ y ∈ (Icc (p * M + 1) (p * M + n)).filter (fun k => 1 < k ∧ ¬ k.Prime), y := by
    dsimp [a]
    have h_L2 : n.choose 2 + 1 = p * M + 1 := by
      rw [Nat.choose_two_right]
      rw [hL1_val_eq]
    have h_R2 : (n + 1).choose 2 = p * M + n := by
      have H_choose : (n + 1).choose 2 = (n + 1) * n / 2 := by
        have : n + 1 - 1 = n := by omega
        rw [Nat.choose_two_right, this]
      have H_z : (((n + 1) * n / 2 : ℕ) : ℤ) = (p * M + n : ℤ) := by
        have H_n : (((n + 1) * n / 2 : ℕ) : ℤ) = ((n * (n - 1) / 2 : ℕ) : ℤ) + n := by
          have h1 : (2:ℤ) * (((n+1)*n / 2 : ℕ):ℤ) = (n+1:ℤ)*n := by
            have H_div := n_choose_two_div (n+1) (by omega)
            have H_sub : (((n + 1 : ℕ) : ℤ) - 1) = (n : ℤ) := by omega
            rw [H_sub] at H_div
            exact H_div
          have h2 : (2:ℤ) * ((n * (n-1) / 2 : ℕ):ℤ) = (n:ℤ)*((n:ℤ)-1) := by
            have := n_choose_two_div n (by omega)
            exact this
          have H3 : (2:ℤ) * (((n + 1) * n / 2 : ℕ) : ℤ) = (2:ℤ) * (((n * (n - 1) / 2 : ℕ) : ℤ) + n) := by
            calc (2:ℤ) * (((n + 1) * n / 2 : ℕ) : ℤ) = (n+1:ℤ)*n := h1
            _ = (n:ℤ)*((n:ℤ)-1) + 2*(n:ℤ) := by ring
            _ = (2:ℤ) * ((n * (n-1) / 2 : ℕ):ℤ) + 2*(n:ℤ) := by rw [h2]
            _ = (2:ℤ) * (((n * (n - 1) / 2 : ℕ) : ℤ) + n) := by ring
          have h_two : (2:ℤ) ≠ 0 := by decide
          exact mul_left_cancel₀ h_two H3
        have H_M : ((n * (n - 1) / 2 : ℕ) : ℤ) = p * M := by exact_mod_cast hL1_val_eq
        rw [H_M] at H_n
        exact H_n
      rw [H_choose]
      exact_mod_cast H_z
    have : Icc ((n.choose 2) + 1) ((n + 1).choose 2) = Icc (p * M + 1) (p * M + n) := by
      rw [h_L2, h_R2]
    rw [this]
    rfl
  sorry
