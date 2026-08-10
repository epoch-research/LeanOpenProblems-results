import FormalConjectures.Util.ProblemImports

open Nat Finset BigOperators

namespace Blk

variable {p : ℕ}

/-- If all pairwise products `w i * w j` vanish, then `∏ (1 + w i) = 1 + ∑ w i`. -/
theorem prod_one_add_of_sq_zero {R : Type*} [CommRing R] {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (w : ι → R) (h : ∀ i ∈ s, ∀ j ∈ s, w i * w j = 0) :
    ∏ i ∈ s, (1 + w i) = 1 + ∑ i ∈ s, w i := by
  induction s using Finset.induction with
  | empty => simp
  | @insert a s ha IH =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    have hIH : ∏ i ∈ s, (1 + w i) = 1 + ∑ i ∈ s, w i :=
      IH (fun i hi j hj => h i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj))
    rw [hIH]
    have hcross : w a * ∑ i ∈ s, w i = 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_eq_zero
      intro i hi
      exact h a (Finset.mem_insert_self a s) i (Finset.mem_insert_of_mem hi)
    ring_nf
    ring_nf at hcross
    linear_combination hcross

/-- If `red31 T = 0` then `p^2 * T = 0` in `ZMod (p^3)`. -/
theorem p2_mul_eq_zero (hp : 0 < p) (T : ZMod (p^3))
    (h : (ZMod.castHom (dvd_pow_self p three_ne_zero) (ZMod p)) T = 0) :
    (p : ZMod (p^3))^2 * T = 0 := by
  have hne : NeZero p := ⟨hp.ne'⟩
  have hpd : p ∣ T.val := by
    rw [ZMod.castHom_apply, ← ZMod.natCast_val, ZMod.natCast_eq_zero_iff] at h
    exact h
  obtain ⟨c, hc⟩ := hpd
  have e1 : (p : ZMod (p^3))^2 * T = ((p^2 * T.val : ℕ) : ZMod (p^3)) := by
    rw [Nat.cast_mul, Nat.cast_pow, ZMod.natCast_zmod_val]
  rw [e1, hc]
  have e2 : p^2 * (p * c) = p^3 * c := by ring
  rw [e2, Nat.cast_mul, ZMod.natCast_self, zero_mul]

/- Harmonic order-2 facts mod p. -/

theorem sum_sq_zmod [Fact p.Prime] (hp5 : 5 ≤ p) : ∑ x : ZMod p, x ^ 2 = 0 := by
  apply FiniteField.sum_pow_lt_card_sub_one
  rw [ZMod.card]; omega

theorem harm2_zmod [Fact p.Prime] (hp5 : 5 ≤ p) : ∑ x : ZMod p, (x⁻¹) ^ 2 = 0 := by
  have h := Equiv.sum_comp (Function.Involutive.toPerm (Inv.inv : ZMod p → ZMod p) inv_inv)
    (fun y => y ^ 2)
  simp only [Function.Involutive.coe_toPerm] at h
  rw [h]; exact sum_sq_zmod hp5

theorem harm2_icc [Fact p.Prime] (hp5 : 5 ≤ p) :
    ∑ i ∈ Icc 1 (p-1), ((i : ZMod p)⁻¹) ^ 2 = 0 := by
  have hp0 : 0 < p := (Fact.out (p := p.Prime)).pos
  have hne : NeZero p := ⟨hp0.ne'⟩
  have h := harm2_zmod (p := p) hp5
  rw [show (∑ x : ZMod p, (x⁻¹)^2) = ∑ r ∈ Finset.range p, (((r : ZMod p))⁻¹)^2 by
    apply Finset.sum_nbij' (i := fun x : ZMod p => x.val) (j := fun r : ℕ => (r : ZMod p))
    · intro a _; simp [Finset.mem_range, ZMod.val_lt]
    · intro b _; exact Finset.mem_univ _
    · intro a _; exact ZMod.natCast_rightInverse a
    · intro b hb; exact ZMod.val_cast_of_lt (Finset.mem_range.mp hb)
    · intro a _; rw [ZMod.natCast_rightInverse a]] at h
  rw [show Finset.range p = insert 0 (Finset.Icc 1 (p-1)) by
    ext x; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega,
    Finset.sum_insert (by simp)] at h
  simp only [Nat.cast_zero, inv_zero] at h
  rw [zero_pow (by norm_num), zero_add] at h
  exact h

/-- Reflection: the half harmonic-sq sum vanishes. -/
theorem harm2_half [Fact p.Prime] (hp5 : 5 ≤ p) :
    ∑ i ∈ Icc 1 ((p-1)/2), ((i : ZMod p)⁻¹) ^ 2 = 0 := by
  have hp0 : 0 < p := (Fact.out (p := p.Prime)).pos
  have hodd : p % 2 = 1 := by
    rcases (Fact.out (p := p.Prime)).eq_two_or_odd with h2 | hodd
    · omega
    · exact hodd
  set h := (p-1)/2 with hh
  -- full sum = 2 * half
  have hsplit : ∑ i ∈ Icc 1 (p-1), ((i : ZMod p)⁻¹) ^ 2
      = 2 * ∑ i ∈ Icc 1 h, ((i : ZMod p)⁻¹) ^ 2 := by
    have hunion : Finset.Icc 1 (p-1) = Finset.Icc 1 h ∪ Finset.Icc (h+1) (p-1) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_union]; omega
    have hdisj : Disjoint (Finset.Icc 1 h) (Finset.Icc (h+1) (p-1)) := by
      rw [Finset.disjoint_left]; intro x hx hx2
      simp only [Finset.mem_Icc] at hx hx2; omega
    rw [hunion, Finset.sum_union hdisj, two_mul]
    congr 1
    -- second half = reflected first half
    apply Finset.sum_nbij' (i := fun x => p - x) (j := fun x => p - x)
    · intro a ha; simp only [Finset.mem_Icc] at *; omega
    · intro a ha; simp only [Finset.mem_Icc] at *; omega
    · intro a ha; simp only [Finset.mem_Icc] at ha; omega
    · intro a ha; simp only [Finset.mem_Icc] at ha; omega
    · intro a ha; simp only [Finset.mem_Icc] at ha
      have hc : ((p - a : ℕ) : ZMod p) = -(a : ZMod p) := by
        rw [Nat.cast_sub (by omega), ZMod.natCast_self, zero_sub]
      rw [hc, inv_neg, neg_pow, neg_pow]; ring
  rw [harm2_icc hp5] at hsplit
  -- 0 = 2 * half
  have h2 : (2 : ZMod p) * (∑ i ∈ Icc 1 h, ((i : ZMod p)⁻¹) ^ 2) = 0 := hsplit.symm
  have hne2 : (2 : ZMod p) ≠ 0 := by
    rw [show (2 : ZMod p) = ((2 : ℕ) : ZMod p) by norm_num, Ne, ZMod.natCast_eq_zero_iff]
    intro hd; have := Nat.le_of_dvd (by norm_num) hd; omega
  exact (mul_eq_zero.mp h2).resolve_left hne2

/-- Pairing a product over `Icc 1 (p-1)` into pairs `{i, p-i}`. -/
theorem pair_prod [Fact p.Prime] (hp5 : 5 ≤ p) (F : ℕ → ZMod (p^3)) :
    ∏ i ∈ Icc 1 (p-1), F i = ∏ i ∈ Icc 1 ((p-1)/2), (F i * F (p - i)) := by
  have hp0 : 0 < p := (Fact.out (p := p.Prime)).pos
  have hodd : p % 2 = 1 := by
    rcases (Fact.out (p := p.Prime)).eq_two_or_odd with h2 | hodd
    · omega
    · exact hodd
  set h := (p-1)/2 with hh
  have hunion : Finset.Icc 1 (p-1) = Finset.Icc 1 h ∪ Finset.Icc (h+1) (p-1) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_union]; omega
  have hdisj : Disjoint (Finset.Icc 1 h) (Finset.Icc (h+1) (p-1)) := by
    rw [Finset.disjoint_left]; intro x hx hx2
    simp only [Finset.mem_Icc] at hx hx2; omega
  rw [hunion, Finset.prod_union hdisj, Finset.prod_mul_distrib]
  congr 1
  apply Finset.prod_nbij' (i := fun x => p - x) (j := fun x => p - x)
  · intro a ha; simp only [Finset.mem_Icc] at *; omega
  · intro a ha; simp only [Finset.mem_Icc] at *; omega
  · intro a ha; simp only [Finset.mem_Icc] at ha; omega
  · intro a ha; simp only [Finset.mem_Icc] at ha; omega
  · intro a ha; simp only [Finset.mem_Icc] at ha; rw [show p - (p - a) = a by omega]

/-- `i` is a unit in `ZMod (p^3)` for `1 ≤ i ≤ p-1`. -/
theorem isUnit_cast3 [Fact p.Prime] (i : ℕ) (h1 : 1 ≤ i) (h2 : i ≤ p - 1) :
    IsUnit ((i : ℕ) : ZMod (p^3)) := by
  have hpp : p.Prime := Fact.out
  rw [ZMod.isUnit_iff_coprime]
  have : ¬ p ∣ i := by
    intro hd; have := Nat.le_of_dvd (by omega) hd; omega
  exact (hpp.coprime_iff_not_dvd.mpr this).symm.pow_right 3

/-- The block congruence: `∏_{i=1}^{p-1}(lp+i) ≡ (p-1)! (mod p^3)`. -/
theorem block_cong [Fact p.Prime] (hp5 : 5 ≤ p) (l : ℕ) :
    ∏ i ∈ Icc 1 (p-1), ((l * p + i : ℕ) : ZMod (p^3))
      = ∏ i ∈ Icc 1 (p-1), ((i : ℕ) : ZMod (p^3)) := by
  have hp0 : 0 < p := (Fact.out (p := p.Prime)).pos
  set h := (p-1)/2 with hh
  rw [pair_prod hp5 (fun i => ((l * p + i : ℕ) : ZMod (p^3))),
      pair_prod hp5 (fun i => ((i : ℕ) : ZMod (p^3)))]
  -- pb i, w i
  set pb : ℕ → ZMod (p^3) := fun i => ((i : ℕ) : ZMod (p^3)) * ((p - i : ℕ) : ZMod (p^3)) with hpb
  set w : ℕ → ZMod (p^3) := fun i => (l : ZMod (p^3)) * ((l : ZMod (p^3)) + 1) * (p : ZMod (p^3))^2 * (pb i)⁻¹ with hw
  -- p^3 = 0 facts
  have hp3 : (p : ZMod (p^3))^3 = 0 := by
    rw [show ((p : ZMod (p^3)))^3 = ((p^3 : ℕ) : ZMod (p^3)) by push_cast; ring, ZMod.natCast_self]
  have hp4 : (p : ZMod (p^3))^4 = 0 := by
    rw [show (p : ZMod (p^3))^4 = (p : ZMod (p^3))^3 * p by ring, hp3, zero_mul]
  -- per-pair identity
  have key : ∀ i ∈ Icc 1 h, ((l * p + i : ℕ) : ZMod (p^3)) * ((l * p + (p - i) : ℕ) : ZMod (p^3))
      = pb i * (1 + w i) := by
    intro i hi
    simp only [Finset.mem_Icc] at hi
    have hiu : IsUnit (pb i) := by
      rw [hpb]; apply IsUnit.mul
      · exact isUnit_cast3 i hi.1 (by omega)
      · exact isUnit_cast3 (p - i) (by omega) (by omega)
    have hcs : ((p - i : ℕ) : ZMod (p^3)) = (p : ZMod (p^3)) - (i : ZMod (p^3)) := by
      rw [Nat.cast_sub (by omega)]
    have hbij : pb i * (pb i)⁻¹ = 1 := ZMod.mul_inv_of_unit _ hiu
    have hident : ((l * p + i : ℕ) : ZMod (p^3)) * ((l * p + (p - i) : ℕ) : ZMod (p^3))
        = pb i + (l : ZMod (p^3)) * ((l : ZMod (p^3)) + 1) * (p : ZMod (p^3))^2 := by
      rw [hpb]; push_cast; rw [hcs]; ring
    rw [hident, hw]
    have : pb i * (1 + (l : ZMod (p^3)) * ((l : ZMod (p^3)) + 1) * (p : ZMod (p^3))^2 * (pb i)⁻¹)
        = pb i + (l : ZMod (p^3)) * ((l : ZMod (p^3)) + 1) * (p : ZMod (p^3))^2 * (pb i * (pb i)⁻¹) := by
      ring
    rw [this, hbij, mul_one]
  rw [Finset.prod_congr rfl key, Finset.prod_mul_distrib]
  -- ∏ (1 + w i) = 1 + ∑ w i
  have hwij : ∀ i ∈ Icc 1 h, ∀ j ∈ Icc 1 h, w i * w j = 0 := by
    intro i _ j _
    have : w i * w j = (l : ZMod (p^3))^2 * ((l : ZMod (p^3)) + 1)^2 * (pb i)⁻¹ * (pb j)⁻¹
        * (p : ZMod (p^3))^4 := by rw [hw]; ring
    rw [this, hp4, mul_zero]
  rw [prod_one_add_of_sq_zero _ w hwij]
  -- ∑ w i = 0
  have hsumw : (1 : ZMod (p^3)) + ∑ i ∈ Icc 1 h, w i = 1 := by
    have hsw : ∑ i ∈ Icc 1 h, w i
        = (l : ZMod (p^3)) * ((l : ZMod (p^3)) + 1) * ((p : ZMod (p^3))^2 * ∑ i ∈ Icc 1 h, (pb i)⁻¹) := by
      conv_rhs => rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro i _; simp only [hw]; ring
    rw [hsw]
    have hred : (ZMod.castHom (dvd_pow_self p three_ne_zero) (ZMod p)) (∑ i ∈ Icc 1 h, (pb i)⁻¹) = 0 := by
      rw [map_sum]
      rw [show (0 : ZMod p) = -(∑ i ∈ Icc 1 h, ((i : ZMod p)⁻¹)^2) by rw [harm2_half hp5]; ring]
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      simp only [Finset.mem_Icc] at hi
      have hiu : IsUnit (pb i) := by
        rw [hpb]; apply IsUnit.mul
        · exact isUnit_cast3 i hi.1 (by omega)
        · exact isUnit_cast3 (p - i) (by omega) (by omega)
      rw [show (ZMod.castHom (dvd_pow_self p three_ne_zero) (ZMod p)) (pb i)⁻¹
            = ((ZMod.castHom (dvd_pow_self p three_ne_zero) (ZMod p)) (pb i))⁻¹ from
          (ZMod.inv_eq_of_mul_eq_one p _ _ (by rw [← map_mul, ZMod.mul_inv_of_unit _ hiu, map_one])).symm]
      rw [hpb, map_mul, map_natCast, map_natCast]
      have hcs : ((p - i : ℕ) : ZMod p) = -(i : ZMod p) := by
        rw [Nat.cast_sub (by omega), ZMod.natCast_self, zero_sub]
      rw [hcs]
      rw [show (i : ZMod p) * -(i : ZMod p) = -((i : ZMod p)^2) by ring, inv_neg, inv_pow]
    rw [p2_mul_eq_zero hp0 _ hred, mul_zero, add_zero]
  rw [hsumw, mul_one]

end Blk
