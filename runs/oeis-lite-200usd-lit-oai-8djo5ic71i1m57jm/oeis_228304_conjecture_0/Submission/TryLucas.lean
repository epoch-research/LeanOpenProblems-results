import FormalConjectures.Util.ProblemImports

open Nat Finset Matrix

lemma choose_p_add_cast_zmod (p r k : ℕ) (hp : Nat.Prime p) (hr : r < p) (hk : k ≤ p + r) :
    ((Nat.choose (p + r) k : ℕ) : ZMod p) =
      if k < p then ((Nat.choose r k : ℕ) : ZMod p) else ((Nat.choose r (k - p) : ℕ) : ZMod p) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hmod := (Choose.choose_modEq_choose_mod_mul_choose_div (n := p + r) (k := k) (p := p))
  have hz : (((Nat.choose (p + r) k : ℕ) : ℤ) : ZMod p) =
      (((Nat.choose ((p + r) % p) (k % p) * Nat.choose ((p + r) / p) (k / p) : ℕ) : ℤ) : ZMod p) := by
    exact (ZMod.intCast_eq_intCast_iff _ _ p).2 hmod
  have hp_pos : 0 < p := hp.pos
  have hpr_mod : (p + r) % p = r := by rw [Nat.add_mod_left, Nat.mod_eq_of_lt hr]
  have hpr_div : (p + r) / p = 1 := by
    rw [Nat.add_comm, Nat.add_div_right _ hp_pos]
    simp [Nat.div_eq_of_lt hr]
  by_cases hkp : k < p
  · have hk_mod : k % p = k := Nat.mod_eq_of_lt hkp
    have hk_div : k / p = 0 := Nat.div_eq_of_lt hkp
    simpa [hkp, hpr_mod, hpr_div, hk_mod, hk_div, Nat.cast_mul] using hz
  · have hkp_le : p ≤ k := Nat.le_of_not_gt hkp
    have hk_lt_2p : k < 2 * p := by omega
    have hk_div : k / p = 1 := by
      apply Nat.div_eq_of_lt_le
      · omega
      · exact hk_lt_2p
    have hk_mod : k % p = k - p := by
      rw [Nat.mod_eq_sub_mod hkp_le]
      rw [Nat.mod_eq_of_lt]
      omega
    simpa [hkp, hpr_mod, hpr_div, hk_mod, hk_div, Nat.cast_mul] using hz
