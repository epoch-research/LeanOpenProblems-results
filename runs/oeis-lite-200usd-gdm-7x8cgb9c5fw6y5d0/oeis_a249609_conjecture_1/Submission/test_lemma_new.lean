import FormalConjectures.Util.ProblemImports

open Nat List

def a (n : ℕ) : ℕ :=
  -- Define the evil property using the equivalent of popcount via bits and list count.
  let is_evil (k : ℕ) : Bool := (k.bits.count true % 2) = 0

  -- Find the smallest $m$ in $[1, n]$ using bounded recursion.
  let rec find_min_m (m : ℕ) : ℕ :=
    if m > n then 0
    else if is_evil (n.choose m) then m
    else find_min_m (m + 1)

    -- Termination is guaranteed because m strictly increases and is bounded by n.
    termination_by n + 1 - m

  find_min_m 1

lemma find_min_m_ge_of_exists {n m k : ℕ} (hmk : m ≤ k) (hkn : k ≤ n)
    (hevil : ((n.choose k).bits.count true % 2) = 0) :
    a.find_min_m n (fun k => decide ((k.bits.count true % 2) = 0)) m ≥ m := by
  let is_evil_fn := fun (k : ℕ) => decide ((k.bits.count true % 2) = 0)
  have hevil_bool : is_evil_fn (n.choose k) = true := by
    dsimp [is_evil_fn]
    rw [decide_eq_true_iff]
    exact hevil
  induction m using a.find_min_m.induct n is_evil_fn with
  | case1 x hx =>
    omega
  | case2 x hx he =>
    have h_cond : List.count true (n.choose x).bits % 2 = 0 := by
      exact decide_eq_true_iff.mp he
    rw [a.find_min_m.eq_1]
    have hx_not : ¬x > n := hx
    simp [hx_not, h_cond]
  | case3 x hx hne ih =>
    have h_cond : ¬(List.count true (n.choose x).bits % 2 = 0) := by
      rw [decide_eq_true_iff] at hne
      exact hne
    rw [a.find_min_m.eq_1]
    have hx_not : ¬x > n := hx
    simp [hx_not, h_cond]
    have h_xk : x < k := by
      by_contra hc
      have : x = k := by omega
      subst this
      exact h_cond hevil
    have h_x1k : x + 1 ≤ k := by omega
    have ih_val := ih h_x1k
    omega

lemma a_eq (n : ℕ) : a n = a.find_min_m n (fun k => decide ((k.bits.count true % 2) = 0)) 1 := rfl

lemma a_ne_zero_of_exists {n k : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ n)
    (hevil : ((n.choose k).bits.count true % 2) = 0) :
    a n ≠ 0 := by
  rw [a_eq]
  have : a.find_min_m n (fun k => decide ((k.bits.count true % 2) = 0)) 1 ≥ 1 :=
    find_min_m_ge_of_exists hk1 hkn hevil
  omega

lemma a_ne_zero_of_even_popcount {n : ℕ} (hn1 : 1 ≤ n) (heven : n.bits.count true % 2 = 0) : a n ≠ 0 := by
  apply a_ne_zero_of_exists (k := 1) (by omega) hn1
  rw [Nat.choose_one_right]
  exact heven


lemma a3_ne_zero : a 3 ≠ 0 := by
  apply a_ne_zero_of_exists (k := 1) (by omega) (by omega)
  have h_choose : Nat.choose 3 1 = 3 := rfl
  have h_bits : (3 : ℕ).bits = [true, true] := by
    have h_3 : (3 : ℕ) = 2 * 1 + 1 := by norm_num
    rw [h_3, Nat.bit1_bits]
    rw [Nat.one_bits]
  rw [h_choose, h_bits]
  rfl

lemma a4_ne_zero : a 4 ≠ 0 := by
  apply a_ne_zero_of_exists (k := 2) (by omega) (by omega)
  have h_choose : Nat.choose 4 2 = 6 := rfl
  have h_bits : (6 : ℕ).bits = [false, true, true] := by
    have h_6 : (6 : ℕ) = 2 * 3 := by norm_num
    rw [h_6]
    erw [Nat.bit0_bits 3 (by decide)]
    have h_3 : (3 : ℕ) = 2 * 1 + 1 := by norm_num
    rw [h_3, Nat.bit1_bits]
    rw [Nat.one_bits]
  rw [h_choose, h_bits]
  rfl

lemma a5_ne_zero : a 5 ≠ 0 := by
  apply a_ne_zero_of_exists (k := 1) (by omega) (by omega)
  have h_choose : Nat.choose 5 1 = 5 := rfl
  have h_bits : (5 : ℕ).bits = [true, false, true] := by
    have h_5 : (5 : ℕ) = 2 * 2 + 1 := by norm_num
    rw [h_5, Nat.bit1_bits]
    have h_2 : (2 : ℕ) = 2 * 1 := by norm_num
    erw [h_2, Nat.bit0_bits 1 (by decide)]
    rw [Nat.one_bits]
  rw [h_choose, h_bits]
  rfl

lemma a6_ne_zero : a 6 ≠ 0 := by
  apply a_ne_zero_of_exists (k := 1) (by omega) (by omega)
  have h_choose : Nat.choose 6 1 = 6 := rfl
  have h_bits : (6 : ℕ).bits = [false, true, true] := by
    have h_6 : (6 : ℕ) = 2 * 3 := by norm_num
    rw [h_6]
    erw [Nat.bit0_bits 3 (by decide)]
    have h_3 : (3 : ℕ) = 2 * 1 + 1 := by norm_num
    rw [h_3, Nat.bit1_bits]
    rw [Nat.one_bits]
  rw [h_choose, h_bits]
  rfl
