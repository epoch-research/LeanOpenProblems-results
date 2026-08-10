import Mathlib

open Nat

def a (m : ℕ) : ℤ :=
  Finset.sum (Finset.range (m + 1)) fun n =>
    Finset.sum (Finset.range (n + 1)) fun k =>
      let exp_x_num := n * (k + 1)
      if exp_x_num ≤ m then
        let remainder := m - exp_x_num
        if (n + 1) ∣ remainder then
          let j : ℕ := remainder / (n + 1)
          let c₁ : ℤ := (n.choose k)
          let c₂ : ℤ := (choose (n + j) j)
          let sign : ℤ := if Even j then 1 else -1
          sign * c₁ * c₂
        else
          0
      else
        0

def term_mod2 (m n k : ℕ) : ZMod 2 :=
  if _h1 : n * (k + 1) ≤ m then
    let remainder := m - n * (k + 1)
    if _h2 : (n + 1) ∣ remainder then
      let j := remainder / (n + 1)
      (n.choose k : ZMod 2) * ((n + j).choose j : ZMod 2)
    else 0
  else 0

def AllPairs (m : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Iic m ×ˢ Finset.Iic m).filter (fun p => p.2 ≤ p.1)

lemma double_sum_eq_sum_all_pairs (m : ℕ) (f : ℕ → ℕ → ZMod 2) :
  Finset.sum (Finset.range (m + 1)) (fun n => Finset.sum (Finset.range (n + 1)) (fun k => f n k)) =
  (AllPairs m).sum (fun p => f p.1 p.2) := by
  have h_range : ∀ (x : ℕ), Finset.range (x + 1) = Finset.Iic x := by
    intro x
    ext y
    simp only [Finset.mem_range, Finset.mem_Iic, Nat.lt_succ_iff]
  rw [h_range m]
  simp_rw [h_range]
  unfold AllPairs
  rw [Finset.sum_filter]
  rw [Finset.sum_product]
  apply Finset.sum_congr rfl
  intro n hn
  have hn_le : n ≤ m := Finset.mem_Iic.mp hn
  have h_split : Finset.Iic m = Finset.Iic n ∪ (Finset.Iic m \ Finset.Iic n) := by
    ext x
    simp only [Finset.mem_Iic, Finset.mem_union, Finset.mem_sdiff]
    omega
  rw [h_split]
  have h_disj : Disjoint (Finset.Iic n) (Finset.Iic m \ Finset.Iic n) := by
    rw [Finset.disjoint_iff_ne]
    intro x hx y hy
    simp only [Finset.mem_Iic, Finset.mem_sdiff] at hx hy
    omega
  rw [Finset.sum_union h_disj]
  have h_zero : ((Finset.Iic m \ Finset.Iic n) : Finset ℕ).sum (fun x => if x ≤ n then f n x else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    simp only [Finset.mem_sdiff, Finset.mem_Iic] at hx
    have : ¬ x ≤ n := hx.2
    simp [this]
  rw [h_zero, add_zero]
  apply Finset.sum_congr rfl
  intro x hx
  simp only [Finset.mem_Iic] at hx
  simp [hx]


lemma a_cast_eq_sum (m : ℕ) : (a m : ZMod 2) = Finset.sum (Finset.range (m + 1)) (fun n => Finset.sum (Finset.range (n + 1)) (fun k => term_mod2 m n k)) := by
  unfold a term_mod2
  push_cast
  congr 1 with n
  congr 1 with k
  split_ifs
  · ring
  · have h_neg : ∀ (y : ZMod 2), -y = y := by decide
    rw [h_neg]
    ring
  · rfl
  · rfl





