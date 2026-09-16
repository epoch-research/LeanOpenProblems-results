import Mathlib

open Nat Finset Nat.ModEq ZMod

lemma prod_split_Icc (a b : ℕ) (h : a ≤ b) :
  Finset.prod (Finset.Icc 1 b) id = Finset.prod (Finset.Icc 1 a) id * Finset.prod (Finset.Icc (a + 1) b) id := by
  have h2 : Disjoint (Icc 1 a) (Icc (a + 1) b) := by
    rw [disjoint_iff_ne]
    intro x hx y hy
    simp only [mem_Icc] at hx hy
    omega
  rw [← prod_union h2]
  apply congr_arg (Finset.prod · id)
  ext x
  simp only [mem_union, mem_Icc]
  omega

lemma Icc_1_eq_factorial (m : ℕ) : Finset.prod (Finset.Icc 1 m) id = m.factorial := by
  induction' m with k ih
  · rfl
  · rw [factorial_succ, ← ih]
    have : Icc 1 (k + 1) = insert (k + 1) (Icc 1 k) := by
      ext x
      simp only [mem_Icc, mem_insert]
      omega
    rw [this, prod_insert (by simp only [mem_Icc, not_and]; omega)]
    rfl

lemma factorial_split_q_minus_1 (p q : ℕ) (h : p < q) :
  (q - 1).factorial = p.factorial * Finset.prod (Finset.Icc (p + 1) (q - 1)) id := by
  rw [← Icc_1_eq_factorial (q - 1), ← Icc_1_eq_factorial p]
  exact prod_split_Icc p (q - 1) (by omega)

lemma wilsons_mod (q : ℕ) (hq : Nat.Prime q) : ((q - 1).factorial : ZMod q) = -1 := by
  haveI : Fact (Nat.Prime q) := ⟨hq⟩
  exact ZMod.wilsons_lemma q

lemma AD_equiv (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) (h_gap : q - p > 2) :
  let W := Finset.prod (Finset.Icc (p + 1) (q - 2)) id;
  p.factorial ≡ 1 [MOD q] ↔ W ≡ 1 [MOD q] := by
  intro W
  have h_q_ge_3 : q ≥ 3 := by
    have : p ≥ 2 := Nat.Prime.two_le hp
    omega
  have hW : Finset.prod (Finset.Icc (p + 1) (q - 1)) id = W * (q - 1) := by
    have : Icc (p + 1) (q - 1) = insert (q - 1) (Icc (p + 1) (q - 2)) := by
      ext x
      simp only [mem_Icc, mem_insert]
      omega
    rw [this, prod_insert (by simp only [mem_Icc, not_and]; omega)]
    rw [mul_comm]
    rfl
  have h1 : ((q - 1).factorial : ZMod q) = -1 := wilsons_mod q hq
  rw [factorial_split_q_minus_1 p q (by omega), hW] at h1
  push_cast at h1
  have h2 : ((q - 1 : ℕ) : ZMod q) = -1 := by
    rw [Nat.cast_sub (by omega)]
    simp
  rw [h2] at h1
  have h3 : (p.factorial : ZMod q) * (W : ZMod q) = 1 := by
    calc (p.factorial : ZMod q) * (W : ZMod q)
      _ = - (- ((p.factorial : ZMod q) * (W : ZMod q))) := by ring
      _ = - ((p.factorial : ZMod q) * (W : ZMod q) * -1) := by ring
      _ = - ((p.factorial : ZMod q) * ((W : ZMod q) * -1)) := by ring
      _ = - (-1) := by rw [h1]
      _ = 1 := by ring
  constructor
  · intro hp1
    have hp1' : (p.factorial : ZMod q) = (1 : ℕ) := (ZMod.natCast_eq_natCast_iff p.factorial 1 q).mpr hp1
    push_cast at hp1'
    rw [hp1', one_mul] at h3
    apply (ZMod.natCast_eq_natCast_iff W 1 q).mp
    push_cast
    exact h3
  · intro hW1
    have hW1' : (W : ZMod q) = (1 : ℕ) := (ZMod.natCast_eq_natCast_iff W 1 q).mpr hW1
    push_cast at hW1'
    rw [hW1', mul_one] at h3
    apply (ZMod.natCast_eq_natCast_iff p.factorial 1 q).mp
    push_cast
    exact h3

lemma W_eq_one (p q : ℕ) (h_gap : q - p = 2) :
  Finset.prod (Finset.Icc (p + 1) (q - 2)) id = 1 := by
  have : q - 2 = p := by omega
  rw [this]
  have empty_Icc : Finset.Icc (p + 1) p = ∅ := Finset.Icc_eq_empty (by omega)
  rw [empty_Icc]
  rfl

lemma B_implies_D (p q : ℕ) (h_gap : q - p = 2) :
  let W := Finset.prod (Finset.Icc (p + 1) (q - 2)) id;
  W ≡ 1 [MOD q] := by
  intro W
  have hW : W = 1 := W_eq_one p q h_gap
  rw [hW]

lemma B_implies_A (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) (h_gap : q - p = 2) :
  p.factorial ≡ 1 [MOD q] := by
  have h_q_ge_3 : q ≥ 3 := by
    have : p ≥ 2 := Nat.Prime.two_le hp
    omega
  have h1 : ((q - 1).factorial : ZMod q) = -1 := wilsons_mod q hq
  have h_p : p = q - 2 := by omega
  have h_split : (q - 1).factorial = p.factorial * (q - 1) := by
    rw [h_p]
    have : q - 1 = (q - 2) + 1 := by omega
    rw [this, factorial_succ]
    ring
  rw [h_split] at h1
  push_cast at h1
  have h2 : ((q - 1 : ℕ) : ZMod q) = -1 := by
    rw [Nat.cast_sub (by omega)]
    simp
  rw [h2] at h1
  have h3 : (p.factorial : ZMod q) = 1 := by
    calc (p.factorial : ZMod q)
      _ = - (- (p.factorial : ZMod q)) := by ring
      _ = - ((p.factorial : ZMod q) * -1) := by ring
      _ = - (-1) := by rw [h1]
      _ = 1 := by ring
  apply (ZMod.natCast_eq_natCast_iff p.factorial 1 q).mp
  push_cast
  exact h3
