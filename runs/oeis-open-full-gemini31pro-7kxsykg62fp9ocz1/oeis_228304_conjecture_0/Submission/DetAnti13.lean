import Mathlib
import Submission.Defs
import Submission.DetAnti3
import Submission.DetAnti5
import Submission.DetAnti6
import Submission.DetAnti8
import Submission.DetAnti10
import Submission.DetAnti12

open Nat Finset Matrix

lemma a_matrix_mod_p (p : ℕ) [hp : Fact p.Prime] (hp_odd : p ≠ 2) :
    let N := Fin p
    let A : Matrix N N ℤ := fun i j => a_val (i.val + j.val)
    (((Matrix.det A : ℤ) : ZMod p) = (-1 : ZMod p) ^ ((p - 1) / 2)) := by
  intro N A
  have h_p_pos : 0 < p := hp.out.pos
  haveI ne_z : NeZero p := ⟨hp.out.ne_zero⟩
  let f := Int.castRingHom (ZMod p)
  let A_mod := f.mapMatrix A
  have h_det_mod : ((Matrix.det A : ℤ) : ZMod p) = Matrix.det A_mod := by
    dsimp [A_mod]
    exact RingHom.map_det f A
  rw [h_det_mod]
  have h_anti : ∀ i j : Fin p, p - 1 < (i : ℕ) + (j : ℕ) → A_mod i j = 0 := by
    intro i j hij
    dsimp [A_mod, f, RingHom.mapMatrix, A]
    have hn1 : p ≤ (i : ℕ) + (j : ℕ) := by omega
    have hn2 : (i : ℕ) + (j : ℕ) ≤ 2 * p - 2 := by
      have : (i : ℕ) < p := i.isLt
      have : (j : ℕ) < p := j.isLt
      omega
    have eq_a : (a_val ((i : ℕ) + (j : ℕ)) : ZMod p) = ∑ k ∈ range ((i : ℕ) + (j : ℕ) + 1), (-1 : ZMod p)^k * (choose ((i : ℕ) + (j : ℕ)) k : ZMod p)^4 := by
      dsimp [a_val]
      push_cast
      rfl
    rw [eq_a]
    exact a_zmod_eq_zero_of_range p ((i : ℕ) + (j : ℕ)) hp_odd hn1 hn2
  have h_det_anti := det_anti_triangular A_mod h_anti
  rw [h_det_anti]
  have h_prod : ∏ i : Fin p, A_mod i (revPerm p i) = 1 := by
    have H : ∀ i : Fin p, A_mod i (revPerm p i) = 1 := by
      intro i
      have H_idx : (i : ℕ) + (revPerm p i : ℕ) = p - 1 := by
        dsimp [revPerm]
        omega
      dsimp [A_mod, f, RingHom.mapMatrix, A]
      rw [H_idx]
      exact a_p_minus_1_mod_p p hp_odd
    have H2 : ∏ i : Fin p, A_mod i (revPerm p i) = ∏ i : Fin p, (1 : ZMod p) := by
      apply prod_congr rfl
      intro i _
      exact H i
    rw [H2, prod_const_one]
  rw [h_prod, mul_one]
  have h_odd : p % 2 = 1 := by
    cases hp.out.eq_two_or_odd with
    | inl h2 => exfalso; exact hp_odd h2
    | inr hodd => exact hodd
  have h_pow : p * (p - 1) / 2 = (p - 1) / 2 + 2 * ((p / 2) * ((p - 1) / 2)) := by
    set k := p / 2
    have H1 : p = 2 * k + 1 := by
      dsimp [k]
      omega
    have H2 : p - 1 = 2 * k := by omega
    have H3 : (p - 1) / 2 = k := by omega
    have H4 : p * (p - 1) = 2 * (2 * k * k + k) := by
      calc p * (p - 1) = p * (2 * k) := by rw [H2]
        _ = (2 * k + 1) * (2 * k) := by nth_rw 1 [H1]
        _ = 2 * (2 * k * k + k) := by ring
    calc p * (p - 1) / 2 = 2 * (2 * k * k + k) / 2 := by rw [H4]
      _ = 2 * k * k + k := by rw [Nat.mul_div_cancel_left _ zero_lt_two]
      _ = k + 2 * (k * k) := by ring
      _ = (p - 1) / 2 + 2 * ((p / 2) * ((p - 1) / 2)) := by
          nth_rw 1 [←H3]
          nth_rw 2 [←H3]
  have h_pow2 : (-1 : ZMod p) ^ (p * (p - 1) / 2) = (-1 : ZMod p) ^ ((p - 1) / 2) := by
    rw [h_pow, pow_add, pow_mul]
    have : (-1 : ZMod p)^2 = 1 := by simp
    rw [this, one_pow, mul_one]
  rw [h_pow2]
