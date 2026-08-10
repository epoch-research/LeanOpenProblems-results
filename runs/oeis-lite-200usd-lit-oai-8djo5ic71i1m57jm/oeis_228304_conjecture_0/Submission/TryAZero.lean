import FormalConjectures.Util.ProblemImports

open Nat Finset Matrix

def aZ (p n : ℕ) : ZMod p :=
  Finset.sum (range (n + 1)) fun k => ((-1 : ZMod p) ^ k) * ((choose n k : ZMod p) ^ 4)

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

lemma aZ_p_add_eq_zero (p r : ℕ) (hp : Nat.Prime p) (hpodd : p ≠ 2) (hr : r < p) :
    aZ p (p + r) = 0 := by
  classical
  have hp_pos : 0 < p := hp.pos
  have hp_odd_nat : Odd p := hp.odd_of_ne_two hpodd
  have hnegp : (-1 : ZMod p) ^ p = -1 := by
    rcases hp_odd_nat with ⟨m, hm⟩
    rw [hm]
    simp [pow_succ, pow_mul]
  have hsplit := Finset.sum_range_add (fun k => ((-1 : ZMod p) ^ k) * ((choose (p + r) k : ZMod p) ^ 4)) p (r+1)
  unfold aZ
  rw [show p + r + 1 = p + (r + 1) by omega]
  rw [hsplit]
  -- lower sum equals S, upper sum equals -S
  let f : ℕ → ZMod p := fun k => ((-1 : ZMod p) ^ k) * ((choose r k : ZMod p) ^ 4)
  have hlower : (∑ x ∈ range p, ((-1 : ZMod p) ^ x) * ((choose (p + r) x : ZMod p) ^ 4)) = ∑ x ∈ range p, f x := by
    apply Finset.sum_congr rfl
    intro x hx
    have hxlt : x < p := by simpa using hx
    have hch := choose_p_add_cast_zmod p r x hp hr (by omega)
    simp [f, hxlt, hch]
  have hupper : (∑ x ∈ range (r + 1), ((-1 : ZMod p) ^ (p + x)) * ((choose (p + r) (p + x) : ZMod p) ^ 4)) = - (∑ x ∈ range (r + 1), f x) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro x hx
    have hxle : x ≤ r := by simpa [Finset.mem_range] using hx
    have hch := choose_p_add_cast_zmod p r (p+x) hp hr (by omega)
    have hnlt : ¬ p + x < p := by omega
    have hsub : p + x - p = x := by omega
    simp [f, hch, hnlt, hsub, pow_add, hnegp]
  rw [hlower, hupper]
  have htail : (∑ x ∈ range p, f x) = ∑ x ∈ range (r+1), f x := by
    symm
    rw [← Finset.sum_range_add_sum_Ico (f := f) (m := r+1) (n := p) (by omega)]
    suffices (∑ k ∈ Ico (r + 1) p, f k) = 0 by simp [this]
    apply Finset.sum_eq_zero
    intro x hx
    have hxr : r < x := by
      have hx' : r + 1 ≤ x ∧ x < p := by simpa [Finset.mem_Ico] using hx
      omega
    simp [f, Nat.choose_eq_zero_of_lt hxr]
  rw [htail]
  abel
