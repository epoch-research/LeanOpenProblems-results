import FormalConjectures.Util.ProblemImports

open Nat
open Padic

def A275027 (n : ℕ) : ℕ :=
  Finset.sum (Finset.range (n + 1)) (fun k => (Nat.choose n k) ^ 2 * (Nat.choose (n - k) k))

theorem oeis_275027_conjecture_0
    {p : ℕ} (hp : Nat.Prime p) (hp_gt_5 : p > 5)
    {n : ℕ} (hn_pos : n > 0) :
    haveI : Fact (Nat.Prime p) := ⟨hp⟩
    let num : ℚ := (A275027 (p * n) : ℚ) - (A275027 n : ℚ)
    let den : ℚ := (p * n : ℚ) ^ 3
    let val_Q : ℚ := num / den
    (val_Q : Padic p) ∈ PadicInt.subring p := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  intro num den val_Q
  rw [PadicInt.mem_subring_iff]
  rw [eq_padicNorm]
  norm_cast
  rw [padicNorm.div]
  have h_den : 0 < den := by positivity
  have h_den_ne : den ≠ 0 := ne_of_gt h_den
  have h_norm_den_pos : 0 < padicNorm p den := lt_of_le_of_ne (padicNorm.nonneg _) (Ne.symm (padicNorm.nonzero h_den_ne))
  rw [div_le_one h_norm_den_pos]
  have h_den_eq : den = (((p * n) ^ 3 : ℕ) : ℚ) := by
    dsimp [den]
    push_cast
    rfl
  have h_norm_den : padicNorm p den = (p : ℚ) ^ (- (3 * (1 + padicValNat p n)) : ℤ) := by
    rw [h_den_eq]
    have hp_pos : p > 0 := by linarith
    have h_pn_pos : p * n > 0 := mul_pos hp_pos hn_pos
    have hq_ne : (((p * n) ^ 3 : ℕ) : ℚ) ≠ 0 := by
      norm_cast
      exact (_root_.ne_of_gt (pow_pos h_pn_pos 3))
    rw [padicNorm.eq_zpow_of_nonzero hq_ne]
    congr 1
    rw [neg_inj]
    rw [padicValRat.of_nat]
    have h_pow : padicValNat p ((p * n) ^ 3) = 3 * padicValNat p (p * n) := by
      exact padicValNat.pow 3 (_root_.ne_of_gt h_pn_pos)
    rw [h_pow]
    push_cast
    have h_mul : padicValRat p (p * n) = padicValRat p p + padicValRat p n := by
      have hp_ne : (p : ℚ) ≠ 0 := by exact_mod_cast hp_pos.ne'
      have hn_ne : (n : ℚ) ≠ 0 := by exact_mod_cast hn_pos.ne'
      exact padicValRat.mul hp_ne hn_ne
    rw [h_mul]
    have h_self : padicValRat p p = 1 := by
      rw [padicValRat.of_nat]
      exact_mod_cast padicValNat_self
    rw [h_self]
  rw [h_norm_den]
  let z : ℤ := (A275027 (p * n) : ℤ) - (A275027 n : ℤ)
  let m : ℕ := 3 * (1 + padicValNat p n)
  have h_num : num = (z : ℚ) := by
    dsimp [num, z]
    push_cast
    rfl
  rw [h_num]
  have h_norm_le : padicNorm p (z : ℚ) ≤ (p : ℚ) ^ (- (m : ℤ)) := by
    rw [← padicNorm.dvd_iff_norm_le]
    sorry
  exact h_norm_le
