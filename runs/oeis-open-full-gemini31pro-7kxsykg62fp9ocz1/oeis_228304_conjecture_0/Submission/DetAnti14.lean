import Mathlib
import Submission.Defs
import Submission.DetAnti3
import Submission.DetAnti5
import Submission.DetAnti6
import Submission.DetAnti8
import Submission.DetAnti10
import Submission.DetAnti12

open Nat Finset Matrix

lemma c_matrix_mod_p (p : ℕ) [hp : Fact p.Prime] (hp_odd : p ≠ 2) :
    let N := Fin p
    let C : Matrix N N ℤ := fun i j => c_val (i.val + j.val)
    (((Matrix.det C : ℤ) : ZMod p) = 1) := by
  intro N C
  have h_p_pos : 0 < p := hp.out.pos
  haveI ne_z : NeZero p := ⟨hp.out.ne_zero⟩
  let f := Int.castRingHom (ZMod p)
  let C_mod := f.mapMatrix C
  have h_det_mod : ((Matrix.det C : ℤ) : ZMod p) = Matrix.det C_mod := by
    dsimp [C_mod]
    exact RingHom.map_det f C
  rw [h_det_mod]
  have h_anti : ∀ i j : Fin p, p - 1 < (i : ℕ) + (j : ℕ) → C_mod i j = 0 := by
    intro i j hij
    dsimp [C_mod, f, RingHom.mapMatrix, C]
    have hn1 : p ≤ (i : ℕ) + (j : ℕ) := by omega
    have hn2 : (i : ℕ) + (j : ℕ) ≤ 2 * p - 2 := by
      have : (i : ℕ) < p := i.isLt
      have : (j : ℕ) < p := j.isLt
      omega
    have eq_c : (c_val ((i : ℕ) + (j : ℕ)) : ZMod p) = ∑ k ∈ range ((i : ℕ) + (j : ℕ) + 1), (-1 : ZMod p)^k * (choose ((i : ℕ) + (j : ℕ)) k : ZMod p)^2 * (choose (2 * k) k : ZMod p) * (choose (2 * ((i : ℕ) + (j : ℕ) - k)) ((i : ℕ) + (j : ℕ) - k) : ZMod p) := by
      dsimp [c_val]
      push_cast
      rfl
    rw [eq_c]
    exact c_zmod_eq_zero_of_range p ((i : ℕ) + (j : ℕ)) hp_odd hn1 hn2
  have h_det_anti := det_anti_triangular C_mod h_anti
  rw [h_det_anti]
  have h_prod : ∏ i : Fin p, C_mod i (revPerm p i) = (-1 : ZMod p) ^ (p * ((p - 1) / 2)) := by
    have H : ∀ i : Fin p, C_mod i (revPerm p i) = (-1 : ZMod p) ^ ((p - 1) / 2) := by
      intro i
      have H_idx : (i : ℕ) + (revPerm p i : ℕ) = p - 1 := by
        dsimp [revPerm]
        omega
      dsimp [C_mod, f, RingHom.mapMatrix, C]
      rw [H_idx]
      exact c_p_minus_1_mod_p p hp_odd
    have H2 : ∏ i : Fin p, C_mod i (revPerm p i) = ∏ i : Fin p, (-1 : ZMod p) ^ ((p - 1) / 2) := by
      apply prod_congr rfl
      intro i _
      exact H i
    rw [H2, prod_const]
    have h_card : (univ : Finset (Fin p)).card = p := Fintype.card_fin p
    rw [h_card, ←pow_mul]
    have : (p - 1) / 2 * p = p * ((p - 1) / 2) := by ring
    rw [this]
  rw [h_prod]
  have h_odd : p % 2 = 1 := by
    cases hp.out.eq_two_or_odd with
    | inl h2 => exfalso; exact hp_odd h2
    | inr hodd => exact hodd
  have h_pow_sum : p * (p - 1) / 2 + p * ((p - 1) / 2) = 2 * (p * ((p - 1) / 2)) := by
    set k := (p - 1) / 2
    have H2 : p - 1 = 2 * k := by omega
    have H4 : p * (p - 1) = 2 * (p * k) := by
      calc p * (p - 1) = p * (2 * k) := by rw [H2]
        _ = 2 * (p * k) := by ring
    calc p * (p - 1) / 2 + p * ((p - 1) / 2) = 2 * (p * k) / 2 + p * k := by rw [H4]
      _ = p * k + p * k := by rw [Nat.mul_div_cancel_left _ zero_lt_two]
      _ = 2 * (p * k) := by ring
  rw [←pow_add]
  rw [h_pow_sum]
  rw [pow_mul]
  have : (-1 : ZMod p)^2 = 1 := by simp
  rw [this, one_pow]
