import FormalConjectures.Util.ProblemImports
open Nat

lemma div_add_div_le (a b m : ℕ) : a/m + b/m ≤ (a+b)/m := by
  rcases Nat.eq_zero_or_pos m with h | h
  · simp [h]
  · rw [Nat.le_div_iff_mul_le h, add_mul]
    exact Nat.add_le_add (Nat.div_mul_le_self a m) (Nat.div_mul_le_self b m)

lemma div_add_le (a b m : ℕ) (hm : 0 < m) : (a+b)/m ≤ a/m + b/m + 1 := by
  have ha := Nat.div_add_mod a m; have hb := Nat.div_add_mod b m
  have ha' := Nat.mod_lt a hm; have hb' := Nat.mod_lt b hm
  have : (a+b) < (a/m + b/m + 2) * m := by nlinarith [ha, hb, ha', hb']
  have := (Nat.div_lt_iff_lt_mul hm).2 this; omega

lemma landau_floor3 (a m : ℕ) (hm : 0 < m) :
    9*a/m + 6*a/m + 5*a/m ≤ 18*a/m + 2*a/m := by
  obtain ⟨q, s, hs, rfl⟩ : ∃ q s, s < m ∧ a = m*q+s :=
    ⟨a/m, a%m, Nat.mod_lt _ hm, by rw [Nat.div_add_mod]⟩
  have E : ∀ k : ℕ, k*(m*q+s)/m = k*q + (k*s)/m := by
    intro k; have h : k*(m*q+s) = m*(k*q) + k*s := by ring
    rw [h, Nat.mul_add_div hm]
  rw [E 9, E 6, E 5, E 18, E 2]
  have hs0 : s/m = 0 := Nat.div_eq_of_lt hs
  have LA : ∀ i j k : ℕ, i + j = k → (i*s)/m + (j*s)/m ≤ (k*s)/m := by
    intro i j k h; have := div_add_div_le (i*s) (j*s) m
    rwa [show i*s+j*s=k*s by rw [← h]; ring] at this
  have UA : ∀ i j k : ℕ, i + j = k → (k*s)/m ≤ (i*s)/m + (j*s)/m + 1 := by
    intro i j k h; have := div_add_le (i*s) (j*s) m hm
    rwa [show i*s+j*s=k*s by rw [← h]; ring] at this
  have r1a := LA 9 9 18 rfl;  have r1b := UA 9 9 18 rfl
  have r2a1 := LA 6 6 12 rfl; have r2a2 := LA 12 6 18 rfl
  have r2b1 := UA 6 6 12 rfl; have r2b2 := UA 12 6 18 rfl
  have r3a1 := LA 5 5 10 rfl; have r3a2 := LA 10 5 15 rfl; have r3a3 := LA 15 3 18 rfl
  have r3b1 := UA 5 5 10 rfl; have r3b2 := UA 10 5 15 rfl; have r3b3 := UA 15 3 18 rfl
  have r4a := LA 3 3 6 rfl;   have r4b := UA 3 3 6 rfl
  have r5a := LA 2 1 3 rfl;   have r5b := UA 2 1 3 rfl
  have r6a := LA 2 3 5 rfl;   have r6b := UA 2 3 5 rfl
  have e1 : (1*s)/m = 0 := by rw [show 1*s=s by ring, hs0]
  have b2 : (2*s)/m < 2 := (Nat.div_lt_iff_lt_mul hm).2 (by omega)
  have b3 : (3*s)/m < 3 := (Nat.div_lt_iff_lt_mul hm).2 (by omega)
  have b5 : (5*s)/m < 5 := (Nat.div_lt_iff_lt_mul hm).2 (by omega)
  have b6 : (6*s)/m < 6 := (Nat.div_lt_iff_lt_mul hm).2 (by omega)
  have b9 : (9*s)/m < 9 := (Nat.div_lt_iff_lt_mul hm).2 (by omega)
  have d2a : 3*((6*s)/m) ≤ (18*s)/m := by omega
  have d2b : (18*s)/m ≤ 3*((6*s)/m) + 2 := by omega
  have d3a : 3*((5*s)/m) + (3*s)/m ≤ (18*s)/m := by omega
  have d3b : (18*s)/m ≤ 3*((5*s)/m) + (3*s)/m + 3 := by omega
  clear r2a1 r2a2 r2b1 r2b2 r3a1 r3a2 r3a3 r3b1 r3b2 r3b3 LA UA E
  set A1 := (1*s)/m with hA1
  set A2 := (2*s)/m with hA2
  set A3 := (3*s)/m with hA3
  set A5 := (5*s)/m with hA5
  set A6 := (6*s)/m with hA6
  set A9 := (9*s)/m with hA9
  set A18 := (18*s)/m with hA18
  clear_value A1 A2 A3 A5 A6 A9 A18
  omega
