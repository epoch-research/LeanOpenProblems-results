import FormalConjectures.Util.ProblemImports

open Matrix Nat Int

/--
A226163: Determinant of the $(p_n-1)/2$-by-$(p_n-1)/2$ matrix with $(i,j)$-entry being the Legendre symbol
$$\left(\frac{i^2 - \left(\frac{p_n-1}{2}\right)! \cdot j}{p_n}\right)$$
where $p_n$ is the $n$-th prime.
The sequence is naturally indexed starting from $n=2$.
-/
noncomputable def A226163 (n : ℕ) : ℤ :=
  if _h : n < 2 then 0 else

  -- p is the n-th prime, p_n. Mathlib's nth Nat.Prime is 0-indexed, so we use (n-1).
  -- Since n >= 2, p >= 3 is an an odd prime.
  let p : ℕ := Nat.nth Nat.Prime (n - 1)

  -- Matrix dimension m = (p-1)/2.
  let m : ℕ := (p - 1) / 2

  -- The constant C = ((p-1)/2)! as an integer.
  let C : ℤ := m.factorial.cast

  -- The matrix M has entries in ℤ.
  let M : Matrix (Fin m) (Fin m) ℤ := fun i j =>
    -- 1-based indices i' and j' for the formula: 1 <= i', j' <= m.
    let i' : ℤ := (i.val + 1).cast
    let j' : ℤ := (j.val + 1).cast

    -- Argument for the Legendre symbol: i'^2 - C * j'
    let arg : ℤ := i' * i' - C * j'

    -- jacobiSym is the Legendre symbol since p is prime.
    jacobiSym arg p

  M.det

open Matrix Finset
open scoped BigOperators

namespace Scratch

noncomputable def tailRevPerm (m : ℕ) : Equiv.Perm (Fin (m+1)) :=
  Equiv.ofBijective
    (fun r : Fin (m+1) => if h : r = 0 then (0 : Fin (m+1)) else ⟨m + 1 - r.val, by have hp : 0 < r.val := Nat.pos_of_ne_zero (by intro hv; exact h (Fin.ext hv)); omega⟩)
    (by
      constructor
      · intro a b hab
        by_cases ha : a = 0
        · subst a
          by_cases hb : b = 0
          · exact hb.symm
          · have hbval : m+1-b.val = 0 := by
              have := congrArg Fin.val hab
              simpa [hb] using this.symm
            exact False.elim (by have := b.2; omega)
        · by_cases hb : b = 0
          · subst b
            have haval : m+1-a.val = 0 := by
              have := congrArg Fin.val hab
              simpa [ha] using this
            exact False.elim (by have := a.2; omega)
          · have hvals : m+1-a.val = m+1-b.val := by
              have := congrArg Fin.val hab
              simpa [ha, hb] using this
            exact Fin.ext (by omega)
      · intro y
        by_cases hy : y = 0
        · refine ⟨0, ?_⟩
          simp [hy]
        · refine ⟨⟨m+1-y.val, by have hp : 0 < y.val := Nat.pos_of_ne_zero (by intro hv; exact hy (Fin.ext hv)); omega⟩, ?_⟩
          have hnon : (⟨m+1-y.val, by have hp : 0 < y.val := Nat.pos_of_ne_zero (by intro hv; exact hy (Fin.ext hv)); omega⟩ : Fin (m+1)) ≠ 0 := by
            intro h
            have := congrArg Fin.val h
            simp at this
            omega
          simp [hnon]
          apply Fin.ext
          simp
          omega)

lemma tailRevPerm_val_ne_zero {m : ℕ} {r : Fin (m+1)} (hr : r ≠ 0) :
    (tailRevPerm m r).val = m+1-r.val := by
  simp [tailRevPerm, hr]

def auxDpos (R : Type*) [CommRing R] (m : ℕ) (c : R) (y : Fin (m+1) → R) : Matrix (Fin (m+1)) (Fin (m+1)) R :=
  fun r j => if r.val = 0 then 1 + c * y j ^ (m+1) else y j ^ ((m+1) - r.val)

def auxD1pos (R : Type*) [CommRing R] (m : ℕ) (y : Fin (m+1) → R) : Matrix (Fin (m+1)) (Fin (m+1)) R :=
  fun r j => if r.val = 0 then 1 else y j ^ ((m+1) - r.val)

def auxD2pos (R : Type*) [CommRing R] (m : ℕ) (y : Fin (m+1) → R) : Matrix (Fin (m+1)) (Fin (m+1)) R :=
  fun r j => if r.val = 0 then y j ^ (m+1) else y j ^ ((m+1) - r.val)

lemma det_auxDpos_split {R : Type*} [CommRing R] (m : ℕ) (c : R) (y : Fin (m+1) → R) :
    (auxDpos R m c y).det = (auxD1pos R m y).det + c * (auxD2pos R m y).det := by
  have hmat : auxDpos R m c y = (auxD1pos R m y).updateRow 0 ((auxD1pos R m y 0) + c • (auxD2pos R m y 0)) := by
    ext r j
    by_cases hr : r = 0
    · subst r
      simp [auxDpos, auxD1pos, auxD2pos]
    · have hv : r.val ≠ 0 := by intro h; exact hr (Fin.ext h)
      simp [auxDpos, auxD1pos, auxD2pos, hv, hr]
  rw [hmat]
  rw [Matrix.det_updateRow_add]
  rw [Matrix.updateRow_eq_self]
  rw [Matrix.det_updateRow_smul]
  have hrow : (auxD1pos R m y).updateRow 0 (auxD2pos R m y 0) = auxD2pos R m y := by
    ext r j
    by_cases hr : r = 0
    · subst r
      simp [auxD2pos]
    · have hv : r.val ≠ 0 := by intro h; exact hr (Fin.ext h)
      simp [Matrix.updateRow, auxD1pos, auxD2pos, hr, hv]
  rw [hrow]

lemma auxD1pos_eq_tail_rev_vander {R : Type*} [CommRing R] (m : ℕ) (y : Fin (m+1) → R) :
    auxD1pos R m y = ((Matrix.vandermonde y)ᵀ.submatrix (⇑(tailRevPerm m)) id) := by
  ext r j
  by_cases hr : r = 0
  · subst r
    simp [auxD1pos, tailRevPerm, Matrix.vandermonde, Matrix.transpose_apply]
  · have hrv : r.val ≠ 0 := by intro hv; exact hr (Fin.ext hv)
    simp [auxD1pos, hrv, Matrix.vandermonde, Matrix.transpose_apply, tailRevPerm_val_ne_zero hr]

lemma det_auxD1pos {R : Type*} [CommRing R] (m : ℕ) (y : Fin (m+1) → R) :
    (auxD1pos R m y).det =
      (((Equiv.Perm.sign (tailRevPerm m) : ℤˣ) : ℤ) : R) * (Matrix.vandermonde y).det := by
  rw [auxD1pos_eq_tail_rev_vander]
  rw [Matrix.det_permute]
  rw [Matrix.det_transpose]

lemma auxD2pos_eq_scaled_rev_vander {R : Type*} [CommRing R] (m : ℕ) (y : Fin (m+1) → R) :
    auxD2pos R m y = Matrix.of (fun r j : Fin (m+1) => y j * ((Matrix.vandermonde y)ᵀ.submatrix Fin.rev id) r j) := by
  ext r j
  simp [auxD2pos, Matrix.vandermonde, Matrix.transpose_apply]
  by_cases hr : r.val = 0
  · simp [hr]
    rw [_root_.pow_succ']
  · have hrf : r ≠ 0 := by intro h; exact hr (congrArg Fin.val h)
    rw [if_neg hrf]
    have hcalc : m + 1 - r.val = (m - r.val) + 1 := by omega
    rw [hcalc, _root_.pow_succ']

lemma det_auxD2pos {R : Type*} [CommRing R] (m : ℕ) (y : Fin (m+1) → R) :
    (auxD2pos R m y).det =
      (∏ j : Fin (m+1), y j) * (((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin (m+1))) : ℤˣ) : ℤ) : R) * (Matrix.vandermonde y).det := by
  rw [auxD2pos_eq_scaled_rev_vander]
  rw [Matrix.det_mul_row]
  have hperm : ((Matrix.vandermonde y)ᵀ.submatrix Fin.rev id) =
      ((Matrix.vandermonde y)ᵀ.submatrix (⇑(Fin.revPerm : Equiv.Perm (Fin (m+1)))) id) := by
    ext i j
    simp [Fin.revPerm]
  rw [hperm]
  rw [Matrix.det_permute]
  rw [Matrix.det_transpose]
  ring

lemma det_auxDpos_formula {R : Type*} [CommRing R] (m : ℕ) (c : R) (y : Fin (m+1) → R) :
    (auxDpos R m c y).det =
      ((((Equiv.Perm.sign (tailRevPerm m) : ℤˣ) : ℤ) : R) +
        c * (∏ j : Fin (m+1), y j) * (((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin (m+1))) : ℤˣ) : ℤ) : R))
        * (Matrix.vandermonde y).det := by
  rw [det_auxDpos_split, det_auxD1pos, det_auxD2pos]
  ring

end Scratch

open Matrix Finset
open scoped BigOperators

namespace Scratch

def coeffRed (R : Type*) [CommRing R] (m : ℕ) (y : Fin (m+1) → R) : Matrix (Fin (m+1)) (Fin (m+1)) R :=
  fun r j => if _hr : r.val = 0 then 1 + (-1 : R)^(m+1) * y j ^ (m+1)
    else ((-1 : R)^((m+1)-r.val)) * ((Nat.choose (m+1) r.val : ℕ) : R) * y j ^ ((m+1)-r.val)

lemma vandermonde_mul_coeffRed_apply {R : Type*} [CommRing R] (m : ℕ)
    (x y : Fin (m+1) → R) (hx : ∀ i, x i ^ (m+1) = 1) (i j : Fin (m+1)) :
    (Matrix.vandermonde x * coeffRed R m y) i j = (x i - y j) ^ (m+1) := by
  rw [Matrix.mul_apply]
  simp only [Matrix.vandermonde_apply, coeffRed]
  rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => x i ^ k * if hr : k = 0 then 1 + (-1 : R) ^ (m + 1) * y j ^ (m + 1) else (-1 : R) ^ (m + 1 - k) * ((Nat.choose (m + 1) k : ℕ) : R) * y j ^ (m + 1 - k)) (m+1)]
  rw [sub_pow]
  nth_rw 2 [Finset.sum_range_succ]
  rw [Finset.sum_range_succ']
  rw [Finset.sum_range_succ']
  have hsum :
      (∑ k ∈ Finset.range m,
        x i ^ (k + 1) *
          if hr : k + 1 = 0 then 1 + (-1 : R) ^ (m + 1) * y j ^ (m + 1)
          else (-1 : R) ^ (m + 1 - (k + 1)) * ↑((m + 1).choose (k + 1)) * y j ^ (m + 1 - (k + 1))) =
      (∑ k ∈ Finset.range m,
        (-1 : R) ^ (k + 1 + (m + 1)) * x i ^ (k + 1) * y j ^ (m + 1 - (k + 1)) * ↑((m + 1).choose (k + 1))) := by
    apply Finset.sum_congr rfl
    intro k hk
    have hklt : k < m := Finset.mem_range.mp hk
    have hkpos : k + 1 ≠ 0 := by omega
    simp only [hkpos, dif_neg]
    have hexp : k + 1 + (m + 1) = (m + 1 - (k + 1)) + 2 * (k + 1) := by omega
    rw [hexp]
    have heven : (-1 : R) ^ (2 * (k + 1)) = 1 := by
      rw [pow_mul]
      simp
    conv_rhs =>
      rw [pow_add]
      rw [heven]
    simp
    ring
  rw [hsum]
  simp [hx i]
  ring

lemma matrix_pow_sub_eq_vander_mul_coeffRed {R : Type*} [CommRing R] (m : ℕ)
    (x y : Fin (m+1) → R) (hx : ∀ i, x i ^ (m+1) = 1) :
    (Matrix.of fun i j : Fin (m+1) => (x i - y j) ^ (m+1)) = Matrix.vandermonde x * coeffRed R m y := by
  ext i j
  exact (vandermonde_mul_coeffRed_apply m x y hx i j).symm

end Scratch

namespace Scratch

def coeffScale (R : Type*) [CommRing R] (m : ℕ) : Fin (m+1) → R :=
  fun r => if r.val = 0 then 1 else (-1 : R)^((m+1)-r.val) * ((Nat.choose (m+1) r.val : ℕ) : R)

lemma coeffRed_eq_scaled_auxDpos {R : Type*} [CommRing R] (m : ℕ) (y : Fin (m+1) → R) :
    coeffRed R m y = Matrix.of (fun r j => coeffScale R m r * auxDpos R m ((-1 : R)^(m+1)) y r j) := by
  ext r j
  by_cases h : r.val = 0
  · have hr : r = 0 := Fin.ext h
    simp [coeffRed, coeffScale, auxDpos, h, hr]
  · have hr : r ≠ 0 := by intro h0; exact h (congrArg Fin.val h0)
    simp [coeffRed, coeffScale, auxDpos, h, hr]

lemma det_coeffRed_formula {R : Type*} [CommRing R] (m : ℕ) (y : Fin (m+1) → R) :
    (coeffRed R m y).det =
      (∏ r : Fin (m+1), coeffScale R m r) *
      (((((Equiv.Perm.sign (tailRevPerm m) : ℤˣ) : ℤ) : R) +
        ((-1 : R)^(m+1)) * (∏ j : Fin (m+1), y j) * (((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin (m+1))) : ℤˣ) : ℤ) : R))
        * (Matrix.vandermonde y).det) := by
  rw [coeffRed_eq_scaled_auxDpos]
  rw [Matrix.det_mul_column]
  rw [det_auxDpos_formula]

lemma det_pow_sub_formula {R : Type*} [CommRing R] (m : ℕ)
    (x y : Fin (m+1) → R) (hx : ∀ i, x i ^ (m+1) = 1) :
    (Matrix.of fun i j : Fin (m+1) => (x i - y j) ^ (m+1)).det =
      (Matrix.vandermonde x).det *
      ((∏ r : Fin (m+1), coeffScale R m r) *
      (((((Equiv.Perm.sign (tailRevPerm m) : ℤˣ) : ℤ) : R) +
        ((-1 : R)^(m+1)) * (∏ j : Fin (m+1), y j) * (((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin (m+1))) : ℤˣ) : ℤ) : R))
        * (Matrix.vandermonde y).det)) := by
  rw [matrix_pow_sub_eq_vander_mul_coeffRed]
  rw [Matrix.det_mul]
  rw [det_coeffRed_formula]
  exact hx

end Scratch

namespace Scratch

noncomputable def finalFactor (R : Type*) [CommRing R] (m : ℕ) (y : Fin (m+1) → R) : R :=
  ((((Equiv.Perm.sign (tailRevPerm m) : ℤˣ) : ℤ) : R) +
    ((-1 : R)^(m+1)) * (∏ j : Fin (m+1), y j) *
      (((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin (m+1))) : ℤˣ) : ℤ) : R))

lemma det_pow_sub_ne_zero_of {R : Type*} [CommRing R] [IsDomain R] (m : ℕ)
    (x y : Fin (m+1) → R) (hxpow : ∀ i, x i ^ (m+1) = 1)
    (hxinj : Function.Injective x) (hyinj : Function.Injective y)
    (hscale : ∀ r : Fin (m+1), coeffScale R m r ≠ 0)
    (hfinal : finalFactor R m y ≠ 0) :
    (Matrix.of fun i j : Fin (m+1) => (x i - y j) ^ (m+1)).det ≠ 0 := by
  rw [det_pow_sub_formula]
  apply mul_ne_zero
  · exact (Matrix.det_vandermonde_ne_zero_iff).2 hxinj
  · apply mul_ne_zero
    · exact Finset.prod_ne_zero_iff.mpr (by intro a ha; exact hscale a)
    · apply mul_ne_zero
      · exact hfinal
      · exact (Matrix.det_vandermonde_ne_zero_iff).2 hyinj
  exact hxpow

end Scratch

namespace Scratch

lemma coeffScale_ne_zero_zmod {p m : ℕ} [Fact p.Prime] (hp : p = 2*(m+1) + 1)
    (r : Fin (m+1)) : coeffScale (ZMod p) m r ≠ 0 := by
  by_cases hr : r.val = 0
  · simp [coeffScale, hr]
  · have hchoose_nz : (((Nat.choose (m+1) r.val : ℕ) : ZMod p) ≠ 0) := by
      rw [Ne, CharP.cast_eq_zero_iff (ZMod p) p (Nat.choose (m+1) r.val)]
      have hdlt : m+1 < p := by subst p; omega
      have hle : r.val ≤ m+1 := le_of_lt r.isLt
      have hcop := Nat.Prime.coprime_choose_of_lt (Fact.out : p.Prime) hdlt hle
      exact fun hdvd => (Fact.out : Nat.Prime p).ne_one (Nat.Coprime.eq_one_of_dvd hcop hdvd)
    simp [coeffScale, hr, hchoose_nz]

end Scratch
namespace Scratch

lemma ring_tail {R} [CommRing R] (m : ℕ) (C : R) (h : C * ((-1 : R)^m * C) = -1) :
    C^2 = (-1 : R)^(m+1) := by
  have h' : (-1 : R)^m * C^2 = -1 := by
    calc
      (-1 : R)^m * C^2 = C * ((-1 : R)^m * C) := by ring
      _ = -1 := h
  have hsquare : ((-1 : R)^m) * ((-1 : R)^m) = 1 := by
    rw [← pow_add]
    have : m + m = 2 * m := by omega
    rw [this]
    simp
  calc
    C^2 = 1 * C^2 := by rw [one_mul]
    _ = ((-1 : R)^m * (-1 : R)^m) * C^2 := by rw [hsquare]
    _ = (-1 : R)^m * ((-1 : R)^m * C^2) := by ring
    _ = (-1 : R)^m * (-1) := by rw [h']
    _ = (-1 : R)^(m+1) := by rw [pow_succ]

lemma prod_upper_half {p m : ℕ} (hp : p = 2*m + 1) :
    (∏ x ∈ Ico (m+1) p, (x : ZMod p)) = ((-1 : ZMod p)^m) * (m.factorial : ZMod p) := by
  subst p
  -- map x ↦ 2*m+1-x
  calc
    (∏ x ∈ Ico (m + 1) (2 * m + 1), (x : ZMod (2 * m + 1))) =
        (∏ y ∈ Ico 1 (m+1), (-(y : ZMod (2*m+1)))) := by
      refine prod_bij (fun x hx => 2*m+1 - x) ?_ ?_ ?_ ?_
      · intro x hx
        rw [mem_Ico] at hx ⊢
        constructor
        · exact Nat.sub_pos_of_lt hx.2
        · change 2*m+1 - x < m+1
          omega
      · intro x hx y hy hxy
        rw [mem_Ico] at hx hy
        change 2*m+1 - x = 2*m+1 - y at hxy
        omega
      · intro y hy
        rw [mem_Ico] at hy
        refine ⟨2*m+1-y, ?_, ?_⟩
        · rw [mem_Ico]
          constructor <;> omega
        · change 2*m+1 - (2*m+1-y) = y
          omega
      · intro x hx
        have hxlt : x < 2*m+1 := (mem_Ico.mp hx).2
        rw [Nat.cast_sub (le_of_lt hxlt)]
        simp
    _ = ((-1 : ZMod (2*m+1))^m) * (m.factorial : ZMod (2*m+1)) := by
      have hneg : (∏ y ∈ Ico 1 (m+1), (-(y : ZMod (2*m+1)))) =
          (∏ y ∈ Ico 1 (m+1), ((-1 : ZMod (2*m+1)) * (y : ZMod (2*m+1)))) := by
        refine prod_congr rfl ?_
        intro y hy
        ring
      rw [hneg]
      rw [Finset.prod_mul_distrib]
      have hcard : (Ico 1 (m+1)).card = m := by simp
      rw [Finset.prod_const, hcard]
      rw [← prod_natCast, prod_Ico_id_eq_factorial]

lemma half_factorial_sq {p m : ℕ} [Fact p.Prime] (hp : p = 2*m + 1) :
    ((m.factorial : ℕ) : ZMod p)^2 = (-1 : ZMod p) ^ (m + 1) := by
  have hprod1 : (∏ x ∈ Ico 1 (m+1), (x : ZMod p)) = (m.factorial : ZMod p) := by
    rw [← prod_natCast, Finset.prod_Ico_id_eq_factorial]
  have hprod2 : (∏ x ∈ Ico (m+1) p, (x : ZMod p)) = ((-1 : ZMod p)^m) * (m.factorial : ZMod p) :=
    prod_upper_half hp
  have hle1 : 1 ≤ m+1 := by omega
  have hle2 : m+1 ≤ p := by omega
  have hw : (∏ x ∈ Ico 1 p, (x : ZMod p)) = (-1 : ZMod p) := ZMod.prod_Ico_one_prime p
  rw [← Finset.prod_Ico_consecutive _ hle1 hle2] at hw
  rw [hprod1, hprod2] at hw
  exact ring_tail m (m.factorial : ZMod p) hw

end Scratch

namespace Scratch

lemma add_mul_ne_zero_of_sq_eq_one_sq_eq_neg_one {R : Type*} [CommRing R]
    {a b Y : R} (ha : a^2 = 1) (hb : b^2 = 1) (hY : Y^2 = -1) (hone : (1 : R) ≠ -1) :
    a + Y * b ≠ 0 := by
  intro h
  have hyb : Y * b = -a := by
    calc
      Y * b = (a + Y * b) - a := by ring
      _ = 0 - a := by rw [h]
      _ = -a := by ring
  have hsq : (Y * b)^2 = (-a)^2 := by rw [hyb]
  have : (1 : R) = -1 := by
    calc
      (1 : R) = a^2 := ha.symm
      _ = (-a)^2 := by ring
      _ = (Y * b)^2 := hsq.symm
      _ = Y^2 * b^2 := by ring
      _ = (-1) * 1 := by rw [hY, hb]
      _ = -1 := by ring
  exact hone this

lemma intUnit_cast_sq_eq_one {R : Type*} [CommRing R] (u : ℤˣ) : (((u : ℤ) : R)^2) = 1 := by
  rcases Int.units_eq_one_or u with h | h <;> simp [h]

lemma one_ne_neg_one_zmod_of_two_lt {p : ℕ} (hp2 : 2 < p) : (1 : ZMod p) ≠ -1 := by
  intro h
  have htwo : (2 : ZMod p) = 0 := by
    have hc := congrArg (fun x : ZMod p => x + 1) h
    norm_num at hc ⊢
    exact hc
  have hdvd : p ∣ 2 := by
    simpa using (CharP.cast_eq_zero_iff (ZMod p) p 2).mp htwo
  exact (Nat.not_dvd_of_pos_of_lt (by norm_num) hp2) hdvd

lemma prod_fin_succ_natCast_eq_factorial {R : Type*} [CommSemiring R] (d : ℕ) :
    (∏ j : Fin d, ((j.val + 1 : ℕ) : R)) = (d.factorial : ℕ) := by
  rw [Fin.prod_univ_eq_prod_range (fun k => ((k + 1 : ℕ) : R)) d]
  rw [← Nat.cast_prod]
  rw [Finset.prod_range_add_one_eq_factorial]

lemma prod_y_sq_factorial {R : Type*} [CommRing R] {d : ℕ}
    (hC2 : ((d.factorial : ℕ) : R)^2 = -1) (hd_even : Even d) :
    (∏ j : Fin d, ((d.factorial : ℕ) : R) * ((j.val + 1 : ℕ) : R))^2 = -1 := by
  let C : R := (d.factorial : ℕ)
  have hprod : (∏ j : Fin d, C * ((j.val + 1 : ℕ) : R)) = C^(d+1) := by
    calc
      (∏ j : Fin d, C * ((j.val + 1 : ℕ) : R)) = C^d * (∏ j : Fin d, ((j.val + 1 : ℕ) : R)) := by
        rw [Finset.prod_mul_distrib]
        rw [Finset.prod_const]
        simp
      _ = C^d * C := by rw [prod_fin_succ_natCast_eq_factorial]
      _ = C^(d+1) := by rw [pow_succ]
  change (∏ j : Fin d, C * ((j.val + 1 : ℕ) : R)) ^ 2 = -1
  rw [hprod]
  have hC2' : C^2 = -1 := hC2
  rw [← pow_mul]
  have hdmul : (d + 1) * 2 = 2 * (d + 1) := by omega
  rw [hdmul, pow_mul]
  rw [hC2']
  rcases hd_even with ⟨k, rfl⟩
  simp [pow_succ]

lemma finalFactor_ne_zero_zmod_even {p m : ℕ} [Fact p.Prime]
    (hp : p = 2*(m+1) + 1) (heven : Even (m+1)) :
    finalFactor (ZMod p) m (fun j : Fin (m+1) => ((m+1).factorial : ZMod p) * ((j.val+1 : ℕ) : ZMod p)) ≠ 0 := by
  unfold finalFactor
  have hp2 : 2 < p := by subst p; omega
  have hone : (1 : ZMod p) ≠ -1 := one_ne_neg_one_zmod_of_two_lt hp2
  have hC2raw : (((m+1).factorial : ℕ) : ZMod p)^2 = (-1 : ZMod p) ^ ((m+1)+1) := by
    exact half_factorial_sq (p := p) (m := m+1) hp
  have hC2 : (((m+1).factorial : ℕ) : ZMod p)^2 = -1 := by
    rw [hC2raw]
    rcases heven with ⟨k, hk⟩
    rw [hk]
    simp [pow_succ]
  have hY : (∏ j : Fin (m+1), ((m+1).factorial : ZMod p) * ((j.val+1 : ℕ) : ZMod p))^2 = -1 :=
    prod_y_sq_factorial (R := ZMod p) hC2 heven
  have ha : (((((Equiv.Perm.sign (tailRevPerm m) : ℤˣ) : ℤ) : ZMod p))^2) = 1 := intUnit_cast_sq_eq_one _
  have hb : (((((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin (m+1))) : ℤˣ) : ℤ) : ZMod p))^2) = 1 := intUnit_cast_sq_eq_one _
  -- since m+1 is even, the extra sign (-1)^(m+1) is 1
  rw [Even.neg_one_pow heven]
  simpa [one_mul] using add_mul_ne_zero_of_sq_eq_one_sq_eq_neg_one ha hb hY hone

end Scratch

namespace Scratch

lemma zmod_natCast_ne_zero_of_pos_lt {p a : ℕ} (ha0 : 0 < a) (hap : a < p) :
    (a : ZMod p) ≠ 0 := by
  rw [Ne, CharP.cast_eq_zero_iff (ZMod p) p a]
  exact Nat.not_dvd_of_pos_of_lt ha0 hap

lemma zmod_factorial_ne_zero_of_lt {p d : ℕ} (hp : p.Prime) (hd : d < p) :
    ((d.factorial : ℕ) : ZMod p) ≠ 0 := by
  rw [Ne, CharP.cast_eq_zero_iff (ZMod p) p d.factorial]
  rw [hp.dvd_factorial]
  exact not_le_of_gt hd

lemma sq_injective_first_half_m {p m : ℕ} [Fact p.Prime] (hp : p = 2*(m+1) + 1) :
    Function.Injective (fun i : Fin (m+1) => (((i.val + 1 : ℕ) : ZMod p)^2)) := by
  intro i j hij
  have hi_pos : 0 < i.val + 1 := by omega
  have hj_pos : 0 < j.val + 1 := by omega
  have hi_lt : i.val + 1 < p := by subst p; have := i.isLt; omega
  have hj_lt : j.val + 1 < p := by subst p; have := j.isLt; omega
  have hsum_lt : (i.val + 1) + (j.val + 1) < p := by subst p; have := i.isLt; have := j.isLt; omega
  have hprod : (((i.val+1 : ℕ) : ZMod p) - ((j.val+1 : ℕ) : ZMod p)) *
      (((i.val+1 : ℕ) : ZMod p) + ((j.val+1 : ℕ) : ZMod p)) = 0 := by
    calc
      (((i.val+1 : ℕ) : ZMod p) - ((j.val+1 : ℕ) : ZMod p)) *
      (((i.val+1 : ℕ) : ZMod p) + ((j.val+1 : ℕ) : ZMod p))
          = (((i.val+1 : ℕ) : ZMod p)^2 - ((j.val+1 : ℕ) : ZMod p)^2) := by ring
      _ = 0 := by exact sub_eq_zero.mpr hij
  have hsum_ne : (((i.val+1 : ℕ) : ZMod p) + ((j.val+1 : ℕ) : ZMod p)) ≠ 0 := by
    have hcast : (((i.val+1 : ℕ) + (j.val+1 : ℕ) : ℕ) : ZMod p) ≠ 0 :=
      zmod_natCast_ne_zero_of_pos_lt (by omega) hsum_lt
    simpa [Nat.cast_add] using hcast
  have hdiff : (((i.val+1 : ℕ) : ZMod p) - ((j.val+1 : ℕ) : ZMod p)) = 0 := by
    exact (mul_eq_zero.mp hprod).resolve_right hsum_ne
  have hcast_eq : ((i.val+1 : ℕ) : ZMod p) = ((j.val+1 : ℕ) : ZMod p) := sub_eq_zero.mp hdiff
  have hmodeq : (i.val+1 : ℕ) ≡ (j.val+1 : ℕ) [MOD p] := by
    exact (ZMod.natCast_eq_natCast_iff (i.val+1) (j.val+1) p).mp hcast_eq
  have hnat : i.val + 1 = j.val + 1 := by
    apply Nat.ModEq.eq_of_lt_of_lt hmodeq hi_lt hj_lt
  exact Fin.ext (by omega)

lemma linear_injective_first_half_m {p m : ℕ} [Fact p.Prime] (hp : p = 2*(m+1) + 1) :
    Function.Injective (fun j : Fin (m+1) => (((m+1).factorial : ℕ) : ZMod p) * ((j.val + 1 : ℕ) : ZMod p)) := by
  intro i j hij
  have hd_lt : m+1 < p := by subst p; omega
  have hC : (((m+1).factorial : ℕ) : ZMod p) ≠ 0 := zmod_factorial_ne_zero_of_lt (Fact.out : p.Prime) hd_lt
  have h_eq : (((i.val+1 : ℕ) : ZMod p) = ((j.val+1 : ℕ) : ZMod p)) := by
    apply mul_left_cancel₀ hC
    simpa [mul_assoc] using hij
  have hi_lt : i.val + 1 < p := by subst p; have := i.isLt; omega
  have hj_lt : j.val + 1 < p := by subst p; have := j.isLt; omega
  have hmodeq : (i.val+1 : ℕ) ≡ (j.val+1 : ℕ) [MOD p] := by
    exact (ZMod.natCast_eq_natCast_iff (i.val+1) (j.val+1) p).mp h_eq
  have hnat : i.val + 1 = j.val + 1 := Nat.ModEq.eq_of_lt_of_lt hmodeq hi_lt hj_lt
  exact Fin.ext (by omega)

lemma square_first_half_pow_eq_one_m {p m : ℕ} [Fact p.Prime] (hp : p = 2*(m+1) + 1) (i : Fin (m+1)) :
    (((i.val + 1 : ℕ) : ZMod p)^2) ^ (m+1) = 1 := by
  have hi_pos : 0 < i.val + 1 := by omega
  have hi_lt : i.val + 1 < p := by subst p; have := i.isLt; omega
  have hne : ((i.val+1 : ℕ) : ZMod p) ≠ 0 := zmod_natCast_ne_zero_of_pos_lt hi_pos hi_lt
  have hfermat : ((i.val+1 : ℕ) : ZMod p) ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one hne
  have hpd : p - 1 = 2*(m+1) := by subst p; omega
  calc
    (((i.val + 1 : ℕ) : ZMod p)^2) ^ (m+1) = ((i.val+1 : ℕ) : ZMod p) ^ (2*(m+1)) := by rw [pow_mul]
    _ = ((i.val+1 : ℕ) : ZMod p) ^ (p-1) := by rw [hpd]
    _ = 1 := hfermat

lemma power_matrix_det_ne_zero_even {p m : ℕ} [Fact p.Prime]
    (hp : p = 2*(m+1) + 1) (heven : Even (m+1)) :
    (Matrix.of fun i j : Fin (m+1) =>
      ((((i.val + 1 : ℕ) : ZMod p)^2) - (((m+1).factorial : ℕ) : ZMod p) * ((j.val+1 : ℕ) : ZMod p)) ^ (m+1)).det ≠ 0 := by
  apply det_pow_sub_ne_zero_of (m := m)
  · intro i
    exact square_first_half_pow_eq_one_m hp i
  · exact sq_injective_first_half_m hp
  · exact linear_injective_first_half_m hp
  · intro r
    exact coeffScale_ne_zero_zmod hp r
  · exact finalFactor_ne_zero_zmod_even hp heven

end Scratch

namespace Scratch

lemma cast_jacobiSym_prime_eq_pow (p : ℕ) [Fact p.Prime] (a : ℤ) :
    ((jacobiSym a p : ℤ) : ZMod p) = (a : ZMod p) ^ (p / 2) := by
  rw [← jacobiSym.legendreSym.to_jacobiSym p a]
  exact legendreSym.eq_pow (p := p) a

noncomputable def intJacobiMatrix (p d : ℕ) : Matrix (Fin d) (Fin d) ℤ := fun i j =>
  let C : ℤ := d.factorial.cast
  let ii : ℤ := (i.val + 1).cast
  let jj : ℤ := (j.val + 1).cast
  jacobiSym (ii * ii - C * jj) p

lemma intJacobiMatrix_det_ne_zero_even {p d : ℕ} [Fact p.Prime]
    (hp : p = 2*d + 1) (heven : Even d) :
    (intJacobiMatrix p d).det ≠ 0 := by
  by_cases hd0 : d = 0
  · subst d
    simp [intJacobiMatrix]
  · have hdpos : 0 < d := Nat.pos_of_ne_zero hd0
    obtain ⟨m, rfl⟩ : ∃ m, d = m+1 := ⟨d-1, by omega⟩
    have hp' : p = 2*(m+1) + 1 := hp
    have hpow_ne := power_matrix_det_ne_zero_even (p := p) (m := m) hp' heven
    intro hdet0
    have hcastdet : (((intJacobiMatrix p (m+1)).det : ℤ) : ZMod p) = 0 := by rw [hdet0]; simp
    rw [Int.cast_det] at hcastdet
    apply hpow_ne
    convert hcastdet using 2
    ext i j
    simp [intJacobiMatrix, Matrix.map_apply]
    rw [cast_jacobiSym_prime_eq_pow]
    have hpdiv : p / 2 = m+1 := by subst p; omega
    rw [hpdiv]
    congr 1
    norm_num
    ring

end Scratch

open Matrix
open scoped BigOperators

namespace Scratch

lemma det_zero_of_transpose_eq_neg_rat {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℚ) (hA : Aᵀ = -A) (hodd : Odd (Fintype.card ι)) : A.det = 0 := by
  have hdet : A.det = (-A).det := by rw [← det_transpose, hA]
  have hneg : (-A).det = - A.det := by
    rw [Matrix.det_neg, Odd.neg_one_pow (α := ℚ) hodd]
    ring
  have h : A.det = - A.det := hdet.trans hneg
  linarith

lemma det_zero_cols_from_skew_or_id_rat {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℚ) (s : Finset ι)
    (hA : Aᵀ = -A) (hodd : Odd s.card) :
    (Matrix.of fun i j => if j ∈ s then A i j else if i = j then (1 : ℚ) else 0).det = 0 := by
  classical
  letI : Fintype {x // (fun i => i ∈ s) x} := Subtype.fintype (fun i => i ∈ s)
  letI : Fintype {x // ¬ (fun i => i ∈ s) x} := Subtype.fintype (fun i => ¬ i ∈ s)
  let M : Matrix ι ι ℚ := Matrix.of fun i j => if j ∈ s then A i j else if i = j then (1 : ℚ) else 0
  change M.det = 0
  have htop : ∀ i, i ∈ s → ∀ j, ¬ j ∈ s → M i j = 0 := by
    intro i hi j hj
    simp [M, hj, ne_of_mem_of_not_mem hi hj]
  have hdet := Matrix.twoBlockTriangular_det' M (fun i => i ∈ s) htop
  have hprincipal_skew : ((M.toSquareBlockProp fun i => i ∈ s)ᵀ = -(M.toSquareBlockProp fun i => i ∈ s)) := by
    ext i j
    have hentry := congr_fun (congr_fun hA (i : ι)) (j : ι)
    simpa [Matrix.toSquareBlockProp, Matrix.toBlock, Matrix.transpose_apply, M] using hentry
  have hcard : Odd (Fintype.card {x // (fun i => i ∈ s) x}) := by
    simpa [Fintype.card_subtype] using hodd
  rw [hdet]
  apply _root_.mul_eq_zero.mpr
  left
  exact det_zero_of_transpose_eq_neg_rat _ hprincipal_skew hcard

lemma inv_comm_of_comm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K S : Matrix ι ι ℚ) (hcomm : K * S = S * K) (hdet : IsUnit S.det) :
    K * S⁻¹ = S⁻¹ * K := by
  calc
    K * S⁻¹ = S⁻¹ * S * (K * S⁻¹) := by
      rw [Matrix.nonsing_inv_mul S hdet, Matrix.one_mul]
    _ = S⁻¹ * (S * K) * S⁻¹ := by simp [Matrix.mul_assoc]
    _ = S⁻¹ * (K * S) * S⁻¹ := by rw [hcomm]
    _ = S⁻¹ * K * (S * S⁻¹) := by simp [Matrix.mul_assoc]
    _ = S⁻¹ * K := by rw [Matrix.mul_nonsing_inv S hdet, Matrix.mul_one]

lemma skew_inv_mul_of_comm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K S : Matrix ι ι ℚ) (hK : Kᵀ = -K) (hS : Sᵀ = S) (hcomm : K * S = S * K)
    (hdet : IsUnit S.det) : (S⁻¹ * K)ᵀ = -(S⁻¹ * K) := by
  have hSinvT : (S⁻¹)ᵀ = S⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, hS]
  have hcomm_inv : K * S⁻¹ = S⁻¹ * K := inv_comm_of_comm K S hcomm hdet
  calc
    (S⁻¹ * K)ᵀ = Kᵀ * (S⁻¹)ᵀ := by rw [Matrix.transpose_mul]
    _ = (-K) * S⁻¹ := by rw [hK, hSinvT]
    _ = -(K * S⁻¹) := by ext; simp [Matrix.mul_apply, Finset.sum_neg_distrib]
    _ = -(S⁻¹ * K) := by rw [hcomm_inv]

lemma det_mixed_cols_zero_of_skew_symm_comm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K S : Matrix ι ι ℚ) (s : Finset ι)
    (hK : Kᵀ = -K) (hS : Sᵀ = S) (hcomm : K * S = S * K)
    (hdet : IsUnit S.det) (hodd : Odd s.card) :
    (Matrix.of fun i j => if j ∈ s then K i j else S i j).det = 0 := by
  classical
  let T : Matrix ι ι ℚ := S⁻¹ * K
  let N : Matrix ι ι ℚ := Matrix.of fun i j => if j ∈ s then T i j else if i = j then (1 : ℚ) else 0
  have hSN : S * N = Matrix.of fun i j => if j ∈ s then K i j else S i j := by
    ext i j
    by_cases hj : j ∈ s
    · calc
        (S * N) i j = (S * T) i j := by simp [N, hj, Matrix.mul_apply]
        _ = (S * (S⁻¹ * K)) i j := by rfl
        _ = K i j := by rw [Matrix.mul_nonsing_inv_cancel_left S K hdet]
        _ = (Matrix.of fun i j => if j ∈ s then K i j else S i j) i j := by simp [hj]
    · simp [N, hj, Matrix.mul_apply]
  have hTskew : Tᵀ = -T := skew_inv_mul_of_comm K S hK hS hcomm hdet
  have hNdet : N.det = 0 := det_zero_cols_from_skew_or_id_rat T s hTskew hodd
  have : (Matrix.of fun i j => if j ∈ s then K i j else S i j).det = (S * N).det := by rw [hSN]
  rw [this, Matrix.det_mul, hNdet, mul_zero]

end Scratch

open Polynomial

namespace Scratch

lemma det_mixed_cols_zero_of_skew_symm_comm_noinv {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K S : Matrix ι ι ℚ) (s : Finset ι)
    (hK : Kᵀ = -K) (hS : Sᵀ = S) (hcomm : K * S = S * K)
    (hodd : Odd s.card) :
    (Matrix.of fun i j => if j ∈ s then K i j else S i j).det = 0 := by
  classical
  let P : Polynomial ℚ := (Matrix.of fun i j : ι =>
    if j ∈ s then Polynomial.C (K i j) else Polynomial.C (S i j) + Polynomial.X * Polynomial.C (if i = j then (1 : ℚ) else 0)).det
  let target : ℚ := (Matrix.of fun i j => if j ∈ s then K i j else S i j).det
  have hPeval0 : Polynomial.eval 0 P = target := by
    unfold P target
    change (Polynomial.evalRingHom (R:=ℚ) 0) ((Matrix.of fun i j : ι =>
      if j ∈ s then Polynomial.C (K i j) else Polynomial.C (S i j) + Polynomial.X * Polynomial.C (if i = j then (1 : ℚ) else 0)).det) = target
    rw [RingHom.map_det]
    congr 1
    ext i j
    by_cases hj : j ∈ s
    · simp [hj]
    · by_cases hij : i = j <;> simp [hj, hij]
  by_contra htarget
  have hPne : P ≠ 0 := by
    intro hP0
    have : target = 0 := by simpa [hP0] using hPeval0.symm
    exact htarget this
  let Q : Polynomial ℚ := Matrix.charpoly (-S)
  have hQne : Q ≠ 0 := (Matrix.charpoly_monic (-S)).ne_zero
  let bad : Finset ℚ := P.roots.toFinset ∪ Q.roots.toFinset
  obtain ⟨t, htbad⟩ := Finset.exists_notMem bad
  have htP_notroot : t ∉ P.roots := by
    intro ht
    exact htbad (Finset.mem_union.mpr (Or.inl (Multiset.mem_toFinset.mpr ht)))
  have htQ_notroot : t ∉ Q.roots := by
    intro ht
    exact htbad (Finset.mem_union.mpr (Or.inr (Multiset.mem_toFinset.mpr ht)))
  have hPevalt_ne : Polynomial.eval t P ≠ 0 := by
    intro hzero
    exact htP_notroot ((Polynomial.mem_roots hPne).mpr hzero)
  have hQeval_ne : Polynomial.eval t Q ≠ 0 := by
    intro hzero
    exact htQ_notroot ((Polynomial.mem_roots hQne).mpr hzero)
  have hdet_shift_ne : (S + (Matrix.scalar ι) t).det ≠ 0 := by
    have hchar := Matrix.eval_charpoly (-S) t
    -- eval charpoly(-S) t = (t I - (-S)).det = (S + t I).det
    rw [show Polynomial.eval t Q = ((Matrix.scalar ι) t - (-S)).det from hchar] at hQeval_ne
    convert hQeval_ne using 2
    ext i j
    by_cases hij : i = j <;> simp [Matrix.scalar_apply, hij]
    ring
  have hunit : IsUnit (S + (Matrix.scalar ι) t).det := isUnit_iff_ne_zero.mpr hdet_shift_ne
  have hSshiftT : (S + (Matrix.scalar ι) t)ᵀ = S + (Matrix.scalar ι) t := by
    ext i j
    have hsij : S j i = S i j := by
      have := congr_fun (congr_fun hS i) j
      simpa [Matrix.transpose_apply] using this
    by_cases hij : i = j
    · subst j
      simp [Matrix.transpose_apply, Matrix.scalar_apply, hsij]
    · have hji : j ≠ i := fun h => hij h.symm
      simp [Matrix.transpose_apply, Matrix.scalar_apply, hij, hji, hsij]
  have hcomm_shift : K * (S + (Matrix.scalar ι) t) = (S + (Matrix.scalar ι) t) * K := by
    rw [Matrix.mul_add, Matrix.add_mul, hcomm]
    ext i j
    simp [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.scalar_apply]
    ring
  have hzero_shift := det_mixed_cols_zero_of_skew_symm_comm K (S + (Matrix.scalar ι) t) s hK hSshiftT hcomm_shift hunit hodd
  have hPevalt : Polynomial.eval t P = (Matrix.of fun i j => if j ∈ s then K i j else (S + (Matrix.scalar ι) t) i j).det := by
    unfold P
    change (Polynomial.evalRingHom (R:=ℚ) t) ((Matrix.of fun i j : ι =>
      if j ∈ s then Polynomial.C (K i j) else Polynomial.C (S i j) + Polynomial.X * Polynomial.C (if i = j then (1 : ℚ) else 0)).det) = _
    rw [RingHom.map_det]
    congr 1
    ext i j
    by_cases hj : j ∈ s
    · simp [hj]
    · by_cases hij : i = j <;> simp [hj, Matrix.scalar_apply, hij]
  rw [hPevalt, hzero_shift] at hPevalt_ne
  exact hPevalt_ne rfl

end Scratch
open Matrix
open scoped BigOperators

namespace Scratch

def groupCirc (G R : Type*) [Group G] [CommSemiring R] (f : G → R) : Matrix G G R :=
  fun a b => f (a * b⁻¹)

lemma groupCirc_mul_apply {G R : Type*} [Group G] [Fintype G] [DecidableEq G] [CommSemiring R]
    (f g : G → R) (a c : G) :
    (groupCirc G R f * groupCirc G R g) a c = ∑ t : G, f ((a * c⁻¹) * t⁻¹) * g t := by
  rw [Matrix.mul_apply]
  let F : G → R := fun b => f (a * b⁻¹) * g (b * c⁻¹)
  let H : G → R := fun t => f ((a * c⁻¹) * t⁻¹) * g t
  change (∑ b : G, F b) = ∑ t : G, H t
  have hsum : (∑ t : G, H t) = ∑ b : G, F b := by
    refine Fintype.sum_equiv (Equiv.mulRight c) H F ?_
    intro t
    simp [F, H, mul_assoc]
  exact hsum.symm

lemma groupCirc_mul_comm {G R : Type*} [CommGroup G] [Fintype G] [DecidableEq G] [CommSemiring R]
    (f g : G → R) : groupCirc G R f * groupCirc G R g = groupCirc G R g * groupCirc G R f := by
  ext a c
  rw [groupCirc_mul_apply, groupCirc_mul_apply]
  let A : G := a * c⁻¹
  let e : G ≃ G := (Equiv.mulLeft A).trans (Equiv.inv G)
  -- e t = (A*t)⁻¹? not what we want, inspect by simp; use inverse composition then mulLeft
  let e' : G ≃ G := (Equiv.inv G).trans (Equiv.mulLeft A)
  have hsum : (∑ t : G, f (A * t⁻¹) * g t) = ∑ u : G, f u * g (A * u⁻¹) := by
    refine Fintype.sum_equiv e' (fun t => f (A * t⁻¹) * g t) (fun u => f u * g (A * u⁻¹)) ?_
    intro t
    dsimp [e', A]
    have hid : a * c⁻¹ * (a * c⁻¹ * t⁻¹)⁻¹ = t := by
      calc
        a * c⁻¹ * (a * c⁻¹ * t⁻¹)⁻¹ = (a * a⁻¹) * ((c⁻¹ * c) * t) := by
          simp only [_root_.mul_inv_rev, inv_inv]
          ac_rfl
        _ = t := by simp
    rw [hid]
  have hsum2 : (∑ u : G, f u * g (A * u⁻¹)) = ∑ u : G, g (A * u⁻¹) * f u := by
    apply Finset.sum_congr rfl
    intro u hu
    ring
  simpa [A] using hsum.trans hsum2

lemma groupCirc_transpose {G R : Type*} [CommGroup G] [CommSemiring R]
    (f : G → R) : (groupCirc G R f)ᵀ = groupCirc G R (fun x => f x⁻¹) := by
  ext a b
  simp [groupCirc, Matrix.transpose_apply, _root_.mul_inv_rev, mul_comm]

end Scratch

namespace Scratch

lemma groupCirc_skew_of_inv_neg {G R : Type*} [CommGroup G] [CommRing R]
    (f : G → R) (hf : ∀ x, f x⁻¹ = - f x) :
    (groupCirc G R f)ᵀ = - groupCirc G R f := by
  rw [groupCirc_transpose]
  ext a b
  simpa [groupCirc] using hf (a * b⁻¹)

lemma groupCirc_symm_of_inv_eq {G R : Type*} [CommGroup G] [CommRing R]
    (f : G → R) (hf : ∀ x, f x⁻¹ = f x) :
    (groupCirc G R f)ᵀ = groupCirc G R f := by
  rw [groupCirc_transpose]
  ext a b
  simpa [groupCirc] using hf (a * b⁻¹)

lemma det_mixed_groupCirc_zero {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G]
    (f g : G → ℚ) (s : Finset G)
    (hf : ∀ x, f x⁻¹ = - f x) (hg : ∀ x, g x⁻¹ = g x) (hodd : Odd s.card) :
    (Matrix.of fun a b : G => if b ∈ s then groupCirc G ℚ f a b else groupCirc G ℚ g a b).det = 0 := by
  apply det_mixed_cols_zero_of_skew_symm_comm_noinv
  · exact groupCirc_skew_of_inv_neg f hf
  · exact groupCirc_symm_of_inv_eq g hg
  · exact groupCirc_mul_comm f g
  · exact hodd

end Scratch
open scoped BigOperators

namespace Scratch

lemma sq_injective_first_half {p d : ℕ} [Fact p.Prime] (hp : p = 2*d + 1) :
    Function.Injective (fun i : Fin d => (((i.val + 1 : ℕ) : ZMod p)^2)) := by
  intro i j hij
  have hi_pos : 0 < i.val + 1 := by omega
  have hj_pos : 0 < j.val + 1 := by omega
  have hi_lt : i.val + 1 < p := by subst p; have := i.isLt; omega
  have hj_lt : j.val + 1 < p := by subst p; have := j.isLt; omega
  have hsum_lt : (i.val + 1) + (j.val + 1) < p := by subst p; have := i.isLt; have := j.isLt; omega
  have hprod : (((i.val+1 : ℕ) : ZMod p) - ((j.val+1 : ℕ) : ZMod p)) *
      (((i.val+1 : ℕ) : ZMod p) + ((j.val+1 : ℕ) : ZMod p)) = 0 := by
    calc
      (((i.val+1 : ℕ) : ZMod p) - ((j.val+1 : ℕ) : ZMod p)) *
      (((i.val+1 : ℕ) : ZMod p) + ((j.val+1 : ℕ) : ZMod p))
          = (((i.val+1 : ℕ) : ZMod p)^2 - ((j.val+1 : ℕ) : ZMod p)^2) := by ring
      _ = 0 := by exact sub_eq_zero.mpr hij
  have hsum_ne : (((i.val+1 : ℕ) : ZMod p) + ((j.val+1 : ℕ) : ZMod p)) ≠ 0 := by
    have hcast : (((i.val+1 : ℕ) + (j.val+1 : ℕ) : ℕ) : ZMod p) ≠ 0 :=
      zmod_natCast_ne_zero_of_pos_lt (by omega) hsum_lt
    simpa [Nat.cast_add] using hcast
  have hdiff : (((i.val+1 : ℕ) : ZMod p) - ((j.val+1 : ℕ) : ZMod p)) = 0 := by
    exact (mul_eq_zero.mp hprod).resolve_right hsum_ne
  have hcast_eq : ((i.val+1 : ℕ) : ZMod p) = ((j.val+1 : ℕ) : ZMod p) := sub_eq_zero.mp hdiff
  have hmodeq : (i.val+1 : ℕ) ≡ (j.val+1 : ℕ) [MOD p] := by
    exact (ZMod.natCast_eq_natCast_iff (i.val+1) (j.val+1) p).mp hcast_eq
  have hnat : i.val + 1 = j.val + 1 := by
    apply Nat.ModEq.eq_of_lt_of_lt hmodeq hi_lt hj_lt
  exact Fin.ext (by omega)

noncomputable def squareUnits (p : ℕ) [Fact p.Prime] : Subgroup (ZMod p)ˣ where
  carrier := {u | IsSquare ((u : (ZMod p)ˣ) : ZMod p)}
  one_mem' := by refine ⟨1, by simp⟩
  mul_mem' := by
    intro a b ha hb
    rcases ha with ⟨x, hx⟩
    rcases hb with ⟨y, hy⟩
    refine ⟨x*y, ?_⟩
    calc
      (((a*b : (ZMod p)ˣ) : ZMod p)) = (a : ZMod p) * (b : ZMod p) := rfl
      _ = (x * x) * (y * y) := by rw [hx, hy]
      _ = (x*y) * (x*y) := by ring
  inv_mem' := by
    intro a ha
    have hs : IsSquare (((a : (ZMod p)ˣ) : ZMod p)) := ha
    have hinv : IsSquare ((((a : (ZMod p)ˣ) : ZMod p)⁻¹)) := IsSquare.inv hs
    change IsSquare (((a⁻¹ : (ZMod p)ˣ) : ZMod p))
    rwa [Units.val_inv_eq_inv_val]

noncomputable def firstHalfSquareMap {p d : ℕ} [Fact p.Prime] (hp : p = 2*d+1) (i : Fin d) : squareUnits p := by
  let x : ZMod p := ((i.val+1 : ℕ) : ZMod p)
  have hxne : x^2 ≠ 0 := by
    apply pow_ne_zero
    have hi0 : 0 < i.val+1 := by omega
    have hilt : i.val+1 < p := by subst p; have := i.isLt; omega
    exact zmod_natCast_ne_zero_of_pos_lt hi0 hilt
  exact ⟨Units.mk0 (x^2) hxne, by change IsSquare (x^2); exact IsSquare.sq x⟩

lemma firstHalfSquareMap_injective {p d : ℕ} [Fact p.Prime] (hp : p = 2*d+1) :
    Function.Injective (firstHalfSquareMap (p:=p) (d:=d) hp) := by
  intro i j h
  apply sq_injective_first_half hp
  have hv := congrArg (fun u : squareUnits p => (((u : squareUnits p) : (ZMod p)ˣ) : ZMod p)) h
  simpa [firstHalfSquareMap] using hv

lemma zmod_val_pos_of_ne_zero {p : ℕ} [NeZero p] {x : ZMod p} (hx : x ≠ 0) : 0 < x.val := by
  have h := (ZMod.val_ne_zero x).mpr hx
  omega

lemma square_surj_firstHalf {p d : ℕ} [Fact p.Prime] (hp : p = 2*d+1) :
    Function.Surjective (firstHalfSquareMap (p:=p) (d:=d) hp) := by
  intro u
  rcases u.property with ⟨r, hr⟩
  have hunit_ne : (((u : squareUnits p) : (ZMod p)ˣ) : ZMod p) ≠ 0 := Units.ne_zero _
  have hrne : r ≠ 0 := by
    intro h0
    rw [h0] at hr
    simp at hr
  haveI : NeZero p := ⟨by have hp2 := (Fact.out : Nat.Prime p).two_le; omega⟩
  let k := r.val
  have hkpos : 0 < k := zmod_val_pos_of_ne_zero hrne
  have hklt : k < p := ZMod.val_lt r
  by_cases hk : k ≤ d
  · let i : Fin d := ⟨k-1, by omega⟩
    refine ⟨i, ?_⟩
    apply Subtype.ext
    apply Units.ext
    change (((((i.val+1 : ℕ) : ZMod p)^2) : ZMod p)) = (((u : squareUnits p) : (ZMod p)ˣ) : ZMod p)
    have hik : i.val + 1 = k := by simp [i]; omega
    rw [hik]
    rw [ZMod.natCast_zmod_val]
    simpa [pow_two] using hr.symm
  · let i : Fin d := ⟨p-k-1, by subst p; omega⟩
    refine ⟨i, ?_⟩
    apply Subtype.ext
    apply Units.ext
    change (((((i.val+1 : ℕ) : ZMod p)^2) : ZMod p)) = (((u : squareUnits p) : (ZMod p)ˣ) : ZMod p)
    have hik : i.val + 1 = p-k := by simp [i]; omega
    rw [hik]
    have hcast : ((p-k : ℕ) : ZMod p) = - (k : ZMod p) := by
      rw [Nat.cast_sub (le_of_lt hklt)]
      simp
    rw [hcast]
    rw [sq]
    rw [neg_mul_neg]
    rw [← sq]
    rw [ZMod.natCast_zmod_val]
    simpa [pow_two] using hr.symm

noncomputable def firstHalfSquareEquiv {p d : ℕ} [Fact p.Prime] (hp : p = 2*d+1) : Fin d ≃ squareUnits p :=
  Equiv.ofBijective (firstHalfSquareMap (p:=p) (d:=d) hp) ⟨firstHalfSquareMap_injective hp, square_surj_firstHalf hp⟩

end Scratch

namespace Scratch

lemma qc_neg_one_of_mod_four_three {p : ℕ} [Fact p.Prime] (hp3 : p % 4 = 3) :
    quadraticChar (ZMod p) (-1) = (-1 : ℤ) := by
  have hp2 : p ≠ 2 := by intro h; subst p; norm_num at hp3
  have hleg : legendreSym p (-1) = -1 := by
    rw [legendreSym.at_neg_one (p := p) hp2]
    exact ZMod.χ₄_nat_three_mod_four hp3
  simpa [legendreSym] using hleg

noncomputable def colY (p d : ℕ) : Fin d → ZMod p := fun j =>
  ((d.factorial : ℕ) : ZMod p) * ((j.val+1 : ℕ) : ZMod p)

noncomputable def colChosen (p d : ℕ) (j : Fin d) : ZMod p := by
  classical
  exact if IsSquare (colY p d j) then colY p d j else - colY p d j

lemma factorial_cast_ne_zero {p d : ℕ} [Fact p.Prime] (hp : p = 2*d+1) :
    (((d.factorial : ℕ) : ZMod p) ≠ 0) := by
  have hd_lt : d < p := by subst p; omega
  rw [Ne, CharP.cast_eq_zero_iff (ZMod p) p d.factorial]
  rw [(Fact.out : Nat.Prime p).dvd_factorial]
  exact not_le_of_gt hd_lt

lemma colY_ne_zero {p d : ℕ} [Fact p.Prime] (hp : p = 2*d+1) (j : Fin d) : colY p d j ≠ 0 := by
  unfold colY
  have hC := factorial_cast_ne_zero (p:=p) (d:=d) hp
  have hj0 : ((j.val+1 : ℕ) : ZMod p) ≠ 0 := by
    apply zmod_natCast_ne_zero_of_pos_lt
    · omega
    · subst p; have := j.isLt; omega
  exact mul_ne_zero hC hj0

lemma linear_injective_first_half {p d : ℕ} [Fact p.Prime] (hp : p = 2*d + 1) :
    Function.Injective (colY p d) := by
  intro i j hij
  unfold colY at hij
  have hC := factorial_cast_ne_zero (p:=p) (d:=d) hp
  have h_eq : (((i.val+1 : ℕ) : ZMod p) = ((j.val+1 : ℕ) : ZMod p)) := by
    apply mul_left_cancel₀ hC
    simpa [mul_assoc] using hij
  have hi_lt : i.val + 1 < p := by subst p; have := i.isLt; omega
  have hj_lt : j.val + 1 < p := by subst p; have := j.isLt; omega
  have hmodeq : (i.val+1 : ℕ) ≡ (j.val+1 : ℕ) [MOD p] := by
    exact (ZMod.natCast_eq_natCast_iff (i.val+1) (j.val+1) p).mp h_eq
  have hnat : i.val + 1 = j.val + 1 := Nat.ModEq.eq_of_lt_of_lt hmodeq hi_lt hj_lt
  exact Fin.ext (by omega)

lemma colY_neg_ne {p d : ℕ} [Fact p.Prime] (hp : p = 2*d+1) (i j : Fin d) :
    colY p d i ≠ - colY p d j := by
  intro h
  unfold colY at h
  have hC := factorial_cast_ne_zero (p:=p) (d:=d) hp
  have hsum0 : (((i.val+1 : ℕ) : ZMod p) + ((j.val+1 : ℕ) : ZMod p)) = 0 := by
    apply mul_left_cancel₀ hC
    calc
      ((d.factorial : ℕ) : ZMod p) * (((i.val+1 : ℕ) : ZMod p) + ((j.val+1 : ℕ) : ZMod p))
          = ((d.factorial : ℕ) : ZMod p) * ((i.val+1 : ℕ) : ZMod p) + ((d.factorial : ℕ) : ZMod p) * ((j.val+1 : ℕ) : ZMod p) := by ring
      _ = 0 := by rw [h]; ring
      _ = ((d.factorial : ℕ) : ZMod p) * 0 := by ring
  have hsum_lt : (i.val + 1) + (j.val + 1) < p := by subst p; have := i.isLt; have := j.isLt; omega
  have hcast_ne : (((i.val+1)+(j.val+1) : ℕ) : ZMod p) ≠ 0 :=
    zmod_natCast_ne_zero_of_pos_lt (by omega) hsum_lt
  exact hcast_ne (by simpa [Nat.cast_add] using hsum0)

lemma neg_square_of_not_square_mod3 {p : ℕ} [Fact p.Prime] (hp3 : p % 4 = 3) {y : ZMod p}
    (hy0 : y ≠ 0) (hysq : ¬ IsSquare y) : IsSquare (-y) := by
  have hchi_y : quadraticChar (ZMod p) y = (-1 : ℤ) := quadraticChar_neg_one_iff_not_isSquare.mpr hysq
  have hchi_neg1 : quadraticChar (ZMod p) (-1) = (-1 : ℤ) := qc_neg_one_of_mod_four_three (p:=p) hp3
  have hchi : quadraticChar (ZMod p) (-y) = (1 : ℤ) := by
    have hnegmul : (-y : ZMod p) = (-1) * y := by ring
    rw [hnegmul, map_mul, hchi_neg1, hchi_y]
    norm_num
  exact (quadraticChar_one_iff_isSquare (neg_ne_zero.mpr hy0)).mp hchi

lemma colChosen_ne_zero {p d : ℕ} [Fact p.Prime] (hp : p = 2*d+1) (j : Fin d) : colChosen p d j ≠ 0 := by
  unfold colChosen
  by_cases hs : IsSquare (colY p d j)
  · simpa [hs] using colY_ne_zero (p:=p) (d:=d) hp j
  · simpa [hs] using neg_ne_zero.mpr (colY_ne_zero (p:=p) (d:=d) hp j)

lemma colChosen_square {p d : ℕ} [Fact p.Prime] (hp : p = 2*d+1) (hp3 : p % 4 = 3) (j : Fin d) :
    IsSquare (colChosen p d j) := by
  unfold colChosen
  by_cases hs : IsSquare (colY p d j)
  · simpa [hs] using hs
  · simpa [hs] using neg_square_of_not_square_mod3 (p:=p) hp3 (colY_ne_zero (p:=p) (d:=d) hp j) hs

noncomputable def colSquareMap {p d : ℕ} [Fact p.Prime] (hp : p = 2*d+1) (hp3 : p % 4 = 3) (j : Fin d) : squareUnits p :=
  ⟨Units.mk0 (colChosen p d j) (colChosen_ne_zero (p:=p) (d:=d) hp j), colChosen_square (p:=p) (d:=d) hp hp3 j⟩

lemma colSquareMap_val {p d : ℕ} [Fact p.Prime] (hp : p = 2*d+1) (hp3 : p % 4 = 3) (j : Fin d) :
    (((colSquareMap (p:=p) (d:=d) hp hp3 j : squareUnits p) : (ZMod p)ˣ) : ZMod p) = colChosen p d j := rfl

lemma colSquareMap_injective {p d : ℕ} [Fact p.Prime] (hp : p = 2*d+1) (hp3 : p % 4 = 3) :
    Function.Injective (colSquareMap (p:=p) (d:=d) hp hp3) := by
  intro i j h
  have hv0 := congrArg (fun u : squareUnits p => (((u : squareUnits p) : (ZMod p)ˣ) : ZMod p)) h
  have hv : colChosen p d i = colChosen p d j := by simpa [colSquareMap_val] using hv0
  unfold colChosen at hv
  by_cases hi : IsSquare (colY p d i) <;> by_cases hj : IsSquare (colY p d j)
  · have hy : colY p d i = colY p d j := by simpa [hi, hj] using hv
    exact linear_injective_first_half hp hy
  · have hy : colY p d i = - colY p d j := by simpa [hi, hj] using hv
    exact False.elim ((colY_neg_ne hp i j) hy)
  · have hy : - colY p d i = colY p d j := by simpa [hi, hj] using hv
    have hy' : colY p d j = - colY p d i := by rw [← hy]
    exact False.elim ((colY_neg_ne hp j i) hy')
  · have hy : - colY p d i = - colY p d j := by simpa [hi, hj] using hv
    have hy2 : colY p d i = colY p d j := neg_inj.mp hy
    exact linear_injective_first_half hp hy2

noncomputable def colSquareEquiv {p d : ℕ} [Fact p.Prime] (hp : p = 2*d+1) (hp3 : p % 4 = 3) : Fin d ≃ squareUnits p := by
  classical
  letI : Fintype (squareUnits p) := Subtype.fintype _
  refine Equiv.ofBijective (colSquareMap (p:=p) (d:=d) hp hp3) ?_
  rw [Fintype.bijective_iff_injective_and_card]
  constructor
  · exact colSquareMap_injective hp hp3
  · rw [Fintype.card_fin]
    simpa using (Fintype.card_congr (firstHalfSquareEquiv (p:=p) (d:=d) hp))

end Scratch

open Finset

lemma ring_tail {R} [CommRing R] (m : ℕ) (C : R) (h : C * ((-1 : R)^m * C) = -1) :
    C^2 = (-1 : R)^(m+1) := by
  have h' : (-1 : R)^m * C^2 = -1 := by
    calc
      (-1 : R)^m * C^2 = C * ((-1 : R)^m * C) := by ring
      _ = -1 := h
  have hsquare : ((-1 : R)^m) * ((-1 : R)^m) = 1 := by
    rw [← pow_add]
    have : m + m = 2 * m := by omega
    rw [this]
    simp
  calc
    C^2 = 1 * C^2 := by rw [one_mul]
    _ = ((-1 : R)^m * (-1 : R)^m) * C^2 := by rw [hsquare]
    _ = (-1 : R)^m * ((-1 : R)^m * C^2) := by ring
    _ = (-1 : R)^m * (-1) := by rw [h']
    _ = (-1 : R)^(m+1) := by rw [pow_succ]

lemma prod_upper_half {p m : ℕ} (hp : p = 2*m + 1) :
    (∏ x ∈ Ico (m+1) p, (x : ZMod p)) = ((-1 : ZMod p)^m) * (m.factorial : ZMod p) := by
  subst p
  -- map x ↦ 2*m+1-x
  calc
    (∏ x ∈ Ico (m + 1) (2 * m + 1), (x : ZMod (2 * m + 1))) =
        (∏ y ∈ Ico 1 (m+1), (-(y : ZMod (2*m+1)))) := by
      refine prod_bij (fun x hx => 2*m+1 - x) ?_ ?_ ?_ ?_
      · intro x hx
        rw [mem_Ico] at hx ⊢
        constructor
        · exact Nat.sub_pos_of_lt hx.2
        · change 2*m+1 - x < m+1
          omega
      · intro x hx y hy hxy
        rw [mem_Ico] at hx hy
        change 2*m+1 - x = 2*m+1 - y at hxy
        omega
      · intro y hy
        rw [mem_Ico] at hy
        refine ⟨2*m+1-y, ?_, ?_⟩
        · rw [mem_Ico]
          constructor <;> omega
        · change 2*m+1 - (2*m+1-y) = y
          omega
      · intro x hx
        have hxlt : x < 2*m+1 := (mem_Ico.mp hx).2
        rw [Nat.cast_sub (le_of_lt hxlt)]
        simp
    _ = ((-1 : ZMod (2*m+1))^m) * (m.factorial : ZMod (2*m+1)) := by
      have hneg : (∏ y ∈ Ico 1 (m+1), (-(y : ZMod (2*m+1)))) =
          (∏ y ∈ Ico 1 (m+1), ((-1 : ZMod (2*m+1)) * (y : ZMod (2*m+1)))) := by
        refine prod_congr rfl ?_
        intro y hy
        ring
      rw [hneg]
      rw [Finset.prod_mul_distrib]
      have hcard : (Ico 1 (m+1)).card = m := by simp
      rw [Finset.prod_const, hcard]
      rw [← prod_natCast, prod_Ico_id_eq_factorial]

lemma half_factorial_sq {p m : ℕ} [Fact p.Prime] (hp : p = 2*m + 1) :
    ((m.factorial : ℕ) : ZMod p)^2 = (-1 : ZMod p) ^ (m + 1) := by
  have hprod1 : (∏ x ∈ Ico 1 (m+1), (x : ZMod p)) = (m.factorial : ZMod p) := by
    rw [← prod_natCast, Finset.prod_Ico_id_eq_factorial]
  have hprod2 : (∏ x ∈ Ico (m+1) p, (x : ZMod p)) = ((-1 : ZMod p)^m) * (m.factorial : ZMod p) :=
    prod_upper_half hp
  have hle1 : 1 ≤ m+1 := by omega
  have hle2 : m+1 ≤ p := by omega
  have hw : (∏ x ∈ Ico 1 p, (x : ZMod p)) = (-1 : ZMod p) := ZMod.prod_Ico_one_prime p
  rw [← Finset.prod_Ico_consecutive _ hle1 hle2] at hw
  rw [hprod1, hprod2] at hw
  exact ring_tail m (m.factorial : ZMod p) hw
lemma prod_fin_succ_natCast_eq_factorial {R : Type*} [CommSemiring R] (d : ℕ) :
    (∏ j : Fin d, ((j.val + 1 : ℕ) : R)) = (d.factorial : ℕ) := by
  rw [Fin.prod_univ_eq_prod_range (fun k => ((k + 1 : ℕ) : R)) d]
  rw [← Nat.cast_prod]
  rw [Finset.prod_range_add_one_eq_factorial]


namespace Scratch
open Finset

lemma prod_colY_eq_one_of_odd {p d : ℕ} [Fact p.Prime] (hp : p = 2*d+1) (hdodd : Odd d) :
    (∏ j : Fin d, colY p d j) = (1 : ZMod p) := by
  unfold colY
  calc
    (∏ j : Fin d, ((d.factorial : ℕ) : ZMod p) * ((j.val+1 : ℕ) : ZMod p))
        = ((d.factorial : ℕ) : ZMod p)^d * (∏ j : Fin d, ((j.val+1 : ℕ) : ZMod p)) := by
          rw [Finset.prod_mul_distrib, Finset.prod_const]
          simp
    _ = ((d.factorial : ℕ) : ZMod p)^d * ((d.factorial : ℕ) : ZMod p) := by
          rw [prod_fin_succ_natCast_eq_factorial]
    _ = ((d.factorial : ℕ) : ZMod p)^(d+1) := by rw [pow_succ]
    _ = 1 := by
      have hC2raw : ((d.factorial : ℕ) : ZMod p)^2 = (-1 : ZMod p)^(d+1) := half_factorial_sq (p:=p) (m:=d) hp
      have hC2 : ((d.factorial : ℕ) : ZMod p)^2 = 1 := by
        rw [hC2raw]
        rcases hdodd with ⟨k, hk⟩
        rw [hk]
        norm_num [pow_succ]
      rcases hdodd with ⟨k, hk⟩
      rw [hk]
      rw [hk] at hC2
      have hexp : 2 * k + 1 + 1 = 2 * (k + 1) := by omega
      rw [hexp, pow_mul, hC2]
      simp

lemma quadraticChar_prod_colY {p d : ℕ} [Fact p.Prime] (hp : p = 2*d+1) (hdodd : Odd d) :
    (∏ j : Fin d, quadraticChar (ZMod p) (colY p d j)) = (1 : ℤ) := by
  rw [← map_prod]
  rw [prod_colY_eq_one_of_odd (p:=p) (d:=d) hp hdodd]
  simp

lemma chi_colY_eq_if {p d : ℕ} [Fact p.Prime] (hp : p = 2*d+1) (j : Fin d) :
    quadraticChar (ZMod p) (colY p d j) = if IsSquare (colY p d j) then (1 : ℤ) else -1 := by
  classical
  by_cases hs : IsSquare (colY p d j)
  · have h := (quadraticChar_one_iff_isSquare (colY_ne_zero (p:=p) (d:=d) hp j)).mpr hs
    simp [hs, h]
  · have h := quadraticChar_neg_one_iff_not_isSquare.mpr hs
    simp [hs, h]

lemma even_of_neg_one_pow_eq_one {m : ℕ} (h : (-1 : ℤ)^m = 1) : Even m := by
  by_cases hm : Even m
  · exact hm
  · have ho : Odd m := Nat.not_even_iff_odd.mp hm
    rw [Odd.neg_one_pow (α:=ℤ) ho] at h
    norm_num at h

lemma odd_square_count_colY {p d : ℕ} [Fact p.Prime] (hp : p = 2*d+1) (hdodd : Odd d) :
    Odd ((Finset.univ.filter (fun j : Fin d => IsSquare (colY p d j))).card) := by
  classical
  let P : Fin d → Prop := fun j => IsSquare (colY p d j)
  let s : Finset (Fin d) := Finset.univ.filter P
  let t : Finset (Fin d) := Finset.univ.filter (fun j => ¬ P j)
  have hprod1 := quadraticChar_prod_colY (p:=p) (d:=d) hp hdodd
  have hprod2 : (∏ j : Fin d, quadraticChar (ZMod p) (colY p d j)) = (-1 : ℤ) ^ t.card := by
    calc
      (∏ j : Fin d, quadraticChar (ZMod p) (colY p d j)) = ∏ j : Fin d, (if P j then (1 : ℤ) else -1) := by
        apply Finset.prod_congr rfl; intro j hj; exact chi_colY_eq_if (p:=p) (d:=d) hp j
      _ = (-1 : ℤ) ^ t.card := by
        rw [Finset.prod_ite]
        simp [P, t, Finset.prod_const]
  have ht_even : Even t.card := even_of_neg_one_pow_eq_one (by rw [← hprod2]; exact hprod1)
  have hcard : s.card + t.card = d := by
    calc
      s.card + t.card = (Finset.univ : Finset (Fin d)).card := by
        rw [Finset.card_filter_add_card_filter_not (s:= (Finset.univ : Finset (Fin d))) (p:=P)]
      _ = d := by simp
  have ht_le : t.card ≤ d := by omega
  have hs_eq : s.card = d - t.card := by omega
  rw [hs_eq]
  exact Nat.Odd.sub_even ht_le hdodd ht_even

lemma odd_colSquare_signSet {p d : ℕ} [Fact p.Prime] (hp : p = 2*d+1) (hp3 : p % 4 = 3) (hdodd : Odd d) :
    Odd ((Finset.univ.filter (fun j : Fin d => IsSquare (colY p d j))).image (colSquareMap (p:=p) (d:=d) hp hp3)).card := by
  classical
  rw [Finset.card_image_of_injective]
  · exact odd_square_count_colY (p:=p) (d:=d) hp hdodd
  · exact colSquareMap_injective hp hp3

end Scratch

namespace Scratch

lemma quadraticChar_unit_square_eq_one {p : ℕ} [Fact p.Prime] (u : squareUnits p) :
    quadraticChar (ZMod p) (((u : squareUnits p) : (ZMod p)ˣ) : ZMod p) = 1 := by
  have hs : IsSquare ((((u : squareUnits p) : (ZMod p)ˣ) : ZMod p)) := u.property
  have hne : (((u : squareUnits p) : (ZMod p)ˣ) : ZMod p) ≠ 0 := Units.ne_zero _
  exact (quadraticChar_one_iff_isSquare hne).mpr hs

lemma quadraticChar_unit_square_inv_eq_one {p : ℕ} [Fact p.Prime] (u : squareUnits p) :
    quadraticChar (ZMod p) (((((u : squareUnits p) : (ZMod p)ˣ)⁻¹ : (ZMod p)ˣ) : ZMod p)) = 1 := by
  exact quadraticChar_unit_square_eq_one (p := p) ((u : squareUnits p)⁻¹)

lemma zmod_unit_inv_sub_one {p : ℕ} (u : (ZMod p)ˣ) :
    (((u⁻¹ : (ZMod p)ˣ) : ZMod p) - 1) = -(((u : (ZMod p)ˣ) : ZMod p) - 1) * (((u⁻¹ : (ZMod p)ˣ) : ZMod p)) := by
  have hu : ((u : ZMod p) * ((u⁻¹ : (ZMod p)ˣ) : ZMod p)) = 1 := by simp
  calc
    (((u⁻¹ : (ZMod p)ˣ) : ZMod p) - 1) = (((u⁻¹ : (ZMod p)ˣ) : ZMod p) - ((u : ZMod p) * ((u⁻¹ : (ZMod p)ˣ) : ZMod p))) := by rw [hu]
    _ = -(((u : (ZMod p)ˣ) : ZMod p) - 1) * (((u⁻¹ : (ZMod p)ˣ) : ZMod p)) := by ring

lemma zmod_unit_inv_add_one {p : ℕ} (u : (ZMod p)ˣ) :
    (((u⁻¹ : (ZMod p)ˣ) : ZMod p) + 1) = ((((u : (ZMod p)ˣ) : ZMod p) + 1) * (((u⁻¹ : (ZMod p)ˣ) : ZMod p))) := by
  have hu : ((u : ZMod p) * ((u⁻¹ : (ZMod p)ˣ) : ZMod p)) = 1 := by simp
  calc
    (((u⁻¹ : (ZMod p)ˣ) : ZMod p) + 1) = (((u⁻¹ : (ZMod p)ˣ) : ZMod p) + ((u : ZMod p) * ((u⁻¹ : (ZMod p)ˣ) : ZMod p))) := by rw [hu]
    _ = ((((u : (ZMod p)ˣ) : ZMod p) + 1) * (((u⁻¹ : (ZMod p)ˣ) : ZMod p))) := by ring

lemma qc_inv_sub_one_neg {p : ℕ} [Fact p.Prime] (hp3 : p % 4 = 3) (u : squareUnits p) :
    quadraticChar (ZMod p) (((((u : squareUnits p) : (ZMod p)ˣ)⁻¹ : (ZMod p)ˣ) : ZMod p) - 1)
      = - quadraticChar (ZMod p) ((((u : squareUnits p) : (ZMod p)ˣ) : ZMod p) - 1) := by
  let uu : (ZMod p)ˣ := (u : squareUnits p)
  have hunit : quadraticChar (ZMod p) (((uu⁻¹ : (ZMod p)ˣ) : ZMod p)) = 1 := by
    change quadraticChar (ZMod p) ((((((u : squareUnits p) : (ZMod p)ˣ))⁻¹ : (ZMod p)ˣ) : ZMod p)) = 1
    exact quadraticChar_unit_square_inv_eq_one (p := p) u
  have hneg : quadraticChar (ZMod p) (-1) = (-1 : ℤ) := qc_neg_one_of_mod_four_three (p := p) hp3
  rw [zmod_unit_inv_sub_one uu]
  have hnegmul : (-(↑uu - 1) : ZMod p) = (-1) * (↑uu - 1) := by ring
  rw [hnegmul, map_mul, map_mul, hneg, hunit]
  ring

lemma qc_inv_add_one_eq {p : ℕ} [Fact p.Prime] (u : squareUnits p) :
    quadraticChar (ZMod p) (((((u : squareUnits p) : (ZMod p)ˣ)⁻¹ : (ZMod p)ˣ) : ZMod p) + 1)
      = quadraticChar (ZMod p) ((((u : squareUnits p) : (ZMod p)ˣ) : ZMod p) + 1) := by
  let uu : (ZMod p)ˣ := (u : squareUnits p)
  have hunit : quadraticChar (ZMod p) (((uu⁻¹ : (ZMod p)ˣ) : ZMod p)) = 1 := by
    change quadraticChar (ZMod p) ((((((u : squareUnits p) : (ZMod p)ˣ))⁻¹ : (ZMod p)ˣ) : ZMod p)) = 1
    exact quadraticChar_unit_square_inv_eq_one (p := p) u
  rw [zmod_unit_inv_add_one uu, map_mul, hunit]
  ring

end Scratch

namespace Scratch


noncomputable instance squareUnits.fintype (p : ℕ) [Fact p.Prime] : Fintype (squareUnits p) := by classical exact Subtype.fintype _

noncomputable def qcharRat {p : ℕ} [Fact p.Prime] (z : ZMod p) : ℚ :=
  ((quadraticChar (ZMod p) z : ℤ) : ℚ)

noncomputable def diffFun (p : ℕ) [Fact p.Prime] (u : squareUnits p) : ℚ :=
  qcharRat ((((u : squareUnits p) : (ZMod p)ˣ) : ZMod p) - 1)

noncomputable def sumFun (p : ℕ) [Fact p.Prime] (u : squareUnits p) : ℚ :=
  qcharRat ((((u : squareUnits p) : (ZMod p)ˣ) : ZMod p) + 1)

lemma diffFun_inv_neg {p : ℕ} [Fact p.Prime] (hp3 : p % 4 = 3) (u : squareUnits p) :
    diffFun p (u⁻¹) = - diffFun p u := by
  unfold diffFun qcharRat
  change ((quadraticChar (ZMod p) (((((u : squareUnits p) : (ZMod p)ˣ)⁻¹ : (ZMod p)ˣ) : ZMod p) - 1) : ℤ) : ℚ)
    = - ((quadraticChar (ZMod p) ((((u : squareUnits p) : (ZMod p)ˣ) : ZMod p) - 1) : ℤ) : ℚ)
  rw [qc_inv_sub_one_neg (p:=p) hp3 u]
  norm_num

lemma sumFun_inv_eq {p : ℕ} [Fact p.Prime] (u : squareUnits p) :
    sumFun p (u⁻¹) = sumFun p u := by
  unfold sumFun qcharRat
  change ((quadraticChar (ZMod p) (((((u : squareUnits p) : (ZMod p)ˣ)⁻¹ : (ZMod p)ˣ) : ZMod p) + 1) : ℤ) : ℚ)
    = ((quadraticChar (ZMod p) ((((u : squareUnits p) : (ZMod p)ˣ) : ZMod p) + 1) : ℤ) : ℚ)
  rw [qc_inv_add_one_eq (p:=p) u]

noncomputable def signSet {p d : ℕ} [Fact p.Prime] (hp : p = 2*d+1) (hp3 : p % 4 = 3) : Finset (squareUnits p) :=
  (Finset.univ.filter (fun j : Fin d => IsSquare (colY p d j))).image (colSquareMap (p:=p) (d:=d) hp hp3)

lemma signSet_odd {p d : ℕ} [Fact p.Prime] (hp : p = 2*d+1) (hp3 : p % 4 = 3) (hdodd : Odd d) :
    Odd (signSet (p:=p) (d:=d) hp hp3).card := by
  unfold signSet
  exact odd_colSquare_signSet (p:=p) (d:=d) hp hp3 hdodd

lemma mixed_squareUnits_det_zero {p d : ℕ} [Fact p.Prime] (hp : p = 2*d+1) (hp3 : p % 4 = 3) (hdodd : Odd d) :
    (Matrix.of fun a b : squareUnits p =>
      if b ∈ signSet (p:=p) (d:=d) hp hp3 then groupCirc (squareUnits p) ℚ (diffFun p) a b
      else groupCirc (squareUnits p) ℚ (sumFun p) a b).det = 0 := by
  classical
  letI : Fintype (squareUnits p) := Subtype.fintype _
  apply det_mixed_groupCirc_zero
  · intro x
    exact diffFun_inv_neg (p:=p) hp3 x
  · intro x
    exact sumFun_inv_eq (p:=p) x
  · exact signSet_odd (p:=p) (d:=d) hp hp3 hdodd

end Scratch

namespace Scratch

lemma colSquareMap_mem_signSet_iff {p d : ℕ} [Fact p.Prime] (hp : p = 2*d+1) (hp3 : p % 4 = 3) (j : Fin d) :
    colSquareMap (p:=p) (d:=d) hp hp3 j ∈ signSet (p:=p) (d:=d) hp hp3 ↔ IsSquare (colY p d j) := by
  classical
  unfold signSet
  constructor
  · intro h
    rcases Finset.mem_image.mp h with ⟨k, hk, heq⟩
    have hkj : k = j := colSquareMap_injective hp hp3 heq
    simpa [hkj] using (Finset.mem_filter.mp hk).2
  · intro hj
    apply Finset.mem_image.mpr
    refine ⟨j, ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩

lemma qcharRat_mul_square_unit_eq {p : ℕ} [Fact p.Prime] (u : squareUnits p) (z : ZMod p) :
    qcharRat (z * ((((u : squareUnits p) : (ZMod p)ˣ)⁻¹ : (ZMod p)ˣ) : ZMod p)) = qcharRat z := by
  unfold qcharRat
  have hunit : quadraticChar (ZMod p) (((((u : squareUnits p) : (ZMod p)ˣ)⁻¹ : (ZMod p)ˣ) : ZMod p)) = 1 := quadraticChar_unit_square_inv_eq_one (p:=p) u
  rw [map_mul, hunit]
  ring

lemma firstHalfSquareEquiv_val {p d : ℕ} [Fact p.Prime] (hp : p = 2*d+1) (i : Fin d) :
    ((((firstHalfSquareEquiv (p:=p) (d:=d) hp i : squareUnits p) : (ZMod p)ˣ) : ZMod p)) = (((i.val+1 : ℕ) : ZMod p)^2) := by
  change (((firstHalfSquareMap (p:=p) (d:=d) hp i : squareUnits p) : (ZMod p)ˣ) : ZMod p) = _
  rfl

lemma colSquareEquiv_val {p d : ℕ} [Fact p.Prime] (hp : p = 2*d+1) (hp3 : p % 4 = 3) (j : Fin d) :
    ((((colSquareEquiv (p:=p) (d:=d) hp hp3 j : squareUnits p) : (ZMod p)ˣ) : ZMod p)) = colChosen p d j := by
  change (((colSquareMap (p:=p) (d:=d) hp hp3 j : squareUnits p) : (ZMod p)ˣ) : ZMod p) = _
  rfl

lemma mixed_entry_eq_qchar {p d : ℕ} [Fact p.Prime] (hp : p = 2*d+1) (hp3 : p % 4 = 3) (i j : Fin d) :
    (if colSquareEquiv (p:=p) (d:=d) hp hp3 j ∈ signSet (p:=p) (d:=d) hp hp3
      then groupCirc (squareUnits p) ℚ (diffFun p) (firstHalfSquareEquiv (p:=p) (d:=d) hp i) (colSquareEquiv (p:=p) (d:=d) hp hp3 j)
      else groupCirc (squareUnits p) ℚ (sumFun p) (firstHalfSquareEquiv (p:=p) (d:=d) hp i) (colSquareEquiv (p:=p) (d:=d) hp hp3 j))
    = qcharRat ((((i.val+1 : ℕ) : ZMod p)^2) - colY p d j) := by
  classical
  have hmem := colSquareMap_mem_signSet_iff (p:=p) (d:=d) hp hp3 j
  -- rewrite equivalences to maps
  change (if colSquareMap (p:=p) (d:=d) hp hp3 j ∈ signSet (p:=p) (d:=d) hp hp3
      then groupCirc (squareUnits p) ℚ (diffFun p) (firstHalfSquareMap (p:=p) (d:=d) hp i) (colSquareMap (p:=p) (d:=d) hp hp3 j)
      else groupCirc (squareUnits p) ℚ (sumFun p) (firstHalfSquareMap (p:=p) (d:=d) hp i) (colSquareMap (p:=p) (d:=d) hp hp3 j))
    = qcharRat ((((i.val+1 : ℕ) : ZMod p)^2) - colY p d j)
  let r : squareUnits p := firstHalfSquareMap (p:=p) (d:=d) hp i
  let c : squareUnits p := colSquareMap (p:=p) (d:=d) hp hp3 j
  have hr : (((r : squareUnits p) : (ZMod p)ˣ) : ZMod p) = (((i.val+1 : ℕ) : ZMod p)^2) := by rfl
  have hc_chosen : (((c : squareUnits p) : (ZMod p)ˣ) : ZMod p) = colChosen p d j := by rfl
  by_cases hs : IsSquare (colY p d j)
  · have hm : c ∈ signSet (p:=p) (d:=d) hp hp3 := by
      change colSquareMap (p:=p) (d:=d) hp hp3 j ∈ signSet (p:=p) (d:=d) hp hp3
      exact (hmem).2 hs
    rw [if_pos hm]
    change diffFun p (r * c⁻¹) = qcharRat ((((i.val+1 : ℕ) : ZMod p)^2) - colY p d j)
    unfold diffFun
    calc
      qcharRat (((((r * c⁻¹ : squareUnits p) : (ZMod p)ˣ) : ZMod p)) - 1)
          = qcharRat (((((i.val+1 : ℕ) : ZMod p)^2) - colY p d j) * (((((c : squareUnits p) : (ZMod p)ˣ)⁻¹ : (ZMod p)ˣ) : ZMod p))) := by
            congr 1
            have hc : (((c : squareUnits p) : (ZMod p)ˣ) : ZMod p) = colY p d j := by
              rw [hc_chosen]
              unfold colChosen
              simp [hs]
            change ((((((r : squareUnits p) : (ZMod p)ˣ) * (((c : squareUnits p) : (ZMod p)ˣ)⁻¹)) : (ZMod p)ˣ) : ZMod p) - 1) = _
            rw [Units.val_mul, Units.val_inv_eq_inv_val, hr, hc]
            field_simp [colY_ne_zero (p:=p) (d:=d) hp j]
      _ = qcharRat ((((i.val+1 : ℕ) : ZMod p)^2) - colY p d j) := by
            exact qcharRat_mul_square_unit_eq (p:=p) c ((((i.val+1 : ℕ) : ZMod p)^2) - colY p d j)
  · have hm : c ∉ signSet (p:=p) (d:=d) hp hp3 := by
      change colSquareMap (p:=p) (d:=d) hp hp3 j ∉ signSet (p:=p) (d:=d) hp hp3
      simpa [hmem] using hs
    rw [if_neg hm]
    change sumFun p (r * c⁻¹) = qcharRat ((((i.val+1 : ℕ) : ZMod p)^2) - colY p d j)
    unfold sumFun
    calc
      qcharRat (((((r * c⁻¹ : squareUnits p) : (ZMod p)ˣ) : ZMod p)) + 1)
          = qcharRat (((((i.val+1 : ℕ) : ZMod p)^2) - colY p d j) * (((((c : squareUnits p) : (ZMod p)ˣ)⁻¹ : (ZMod p)ˣ) : ZMod p))) := by
            congr 1
            have hc : (((c : squareUnits p) : (ZMod p)ˣ) : ZMod p) = - colY p d j := by
              rw [hc_chosen]
              unfold colChosen
              simp [hs]
            change ((((((r : squareUnits p) : (ZMod p)ˣ) * (((c : squareUnits p) : (ZMod p)ˣ)⁻¹)) : (ZMod p)ˣ) : ZMod p) + 1) = _
            rw [Units.val_mul, Units.val_inv_eq_inv_val, hr, hc]
            field_simp [colY_ne_zero (p:=p) (d:=d) hp j]
            ring

      _ = qcharRat ((((i.val+1 : ℕ) : ZMod p)^2) - colY p d j) := by
            exact qcharRat_mul_square_unit_eq (p:=p) c ((((i.val+1 : ℕ) : ZMod p)^2) - colY p d j)

end Scratch

namespace Scratch

lemma jacobi_qcharRat {p : ℕ} [Fact p.Prime] (a : ℤ) :
    ((jacobiSym a p : ℤ) : ℚ) = qcharRat ((a : ZMod p)) := by
  unfold qcharRat
  rw [← jacobiSym.legendreSym.to_jacobiSym (p:=p) a]
  rfl

lemma intJacobi_entry_rat_eq {p d : ℕ} [Fact p.Prime] (i j : Fin d) :
    ((intJacobiMatrix p d i j : ℤ) : ℚ) = qcharRat ((((i.val+1 : ℕ) : ZMod p)^2) - colY p d j) := by
  unfold intJacobiMatrix colY
  rw [jacobi_qcharRat (p:=p)]
  congr 1
  norm_num
  ring

lemma intJacobiMatrix_det_zero_odd {p d : ℕ} [Fact p.Prime]
    (hp : p = 2*d+1) (hp3 : p % 4 = 3) (hdodd : Odd d) :
    (intJacobiMatrix p d).det = 0 := by
  classical
  let A : Matrix (squareUnits p) (squareUnits p) ℚ := Matrix.of fun a b : squareUnits p =>
      if b ∈ signSet (p:=p) (d:=d) hp hp3 then groupCirc (squareUnits p) ℚ (diffFun p) a b
      else groupCirc (squareUnits p) ℚ (sumFun p) a b
  let B : Matrix (Fin d) (Fin d) ℚ := (intJacobiMatrix p d).map (fun z => (z : ℚ))
  let eR : Fin d ≃ squareUnits p := firstHalfSquareEquiv (p:=p) (d:=d) hp
  let eC : Fin d ≃ squareUnits p := colSquareEquiv (p:=p) (d:=d) hp hp3
  have hA : A.det = 0 := by
    dsimp [A]
    exact mixed_squareUnits_det_zero (p:=p) (d:=d) hp hp3 hdodd
  have hB : B = (Matrix.reindex eR.symm eC.symm) A := by
    ext i j
    dsimp [B, A, eR, eC]
    rw [intJacobi_entry_rat_eq (p:=p) (d:=d) i j]
    exact (mixed_entry_eq_qchar (p:=p) (d:=d) hp hp3 i j).symm
  have hBdet : B.det = 0 := by
    rw [hB]
    rw [Matrix.det_reindex]
    rw [hA]
    ring
  have hcastdet : (((intJacobiMatrix p d).det : ℤ) : ℚ) = 0 := by
    rw [Int.cast_det]
    exact hBdet
  exact_mod_cast hcastdet

end Scratch


namespace Scratch

lemma two_mul_add_one_mod_four_eq_three_iff_odd (d : ℕ) : (2*d+1)%4=3 ↔ Odd d := by
  constructor
  · intro h
    by_cases he : Even d
    · rcases he with ⟨k,rfl⟩
      have : (2*(2*k)+1)%4=1 := by omega
      omega
    · exact Nat.not_even_iff_odd.mp he
  · intro h
    rcases h with ⟨k,rfl⟩
    omega

lemma two_mul_add_one_mod_four_ne_three_iff_even (d : ℕ) : (2*d+1)%4≠3 ↔ Even d := by
  constructor
  · intro h
    by_contra he
    have ho := Nat.not_even_iff_odd.mp he
    exact h ((two_mul_add_one_mod_four_eq_three_iff_odd d).2 ho)
  · intro he h3
    have ho := (two_mul_add_one_mod_four_eq_three_iff_odd d).1 h3
    exact (Nat.not_even_iff_odd.mpr ho) he

end Scratch

/--
Conjecture: a(n) = 0 if and only if p_n ≡ 3 (mod 4).
-/
theorem oeis_226163_conjecture_0 (n : ℕ) (h_n : 2 ≤ n) :
    A226163 n = 0 ↔ Nat.nth Nat.Prime (n - 1) % 4 = 3 := by
  classical
  let p : ℕ := Nat.nth Nat.Prime (n - 1)
  have hpprime : p.Prime := by simpa [p] using Nat.prime_nth_prime (n - 1)
  haveI : Fact p.Prime := ⟨hpprime⟩
  have hpge3 : 3 ≤ p := by
    have hle := Nat.add_two_le_nth_prime (n - 1)
    omega
  have hpne2 : p ≠ 2 := by omega
  have hpodd : Odd p := hpprime.odd_of_ne_two hpne2
  let d : ℕ := (p - 1) / 2
  obtain ⟨k, hk⟩ := hpodd
  have hdk : d = k := by
    dsimp [d]
    omega
  have hp_eq : p = 2*d + 1 := by
    rw [hdk]
    exact hk
  have hnot : ¬ n < 2 := by omega
  have hA : A226163 n = (Scratch.intJacobiMatrix p d).det := by
    simp [A226163, hnot, p, d]
    rfl
  constructor
  · intro hzero
    by_cases h3 : p % 4 = 3
    · simpa [p] using h3
    · exfalso
      have hd_even : Even d := by
        exact (Scratch.two_mul_add_one_mod_four_ne_three_iff_even d).1 (by simpa [hp_eq] using h3)
      have hnz := Scratch.intJacobiMatrix_det_ne_zero_even (p:=p) (d:=d) hp_eq hd_even
      apply hnz
      rw [← hA]
      exact hzero
  · intro h3orig
    have h3 : p % 4 = 3 := by simpa [p] using h3orig
    have hd_odd : Odd d := by
      exact (Scratch.two_mul_add_one_mod_four_eq_three_iff_odd d).1 (by simpa [hp_eq] using h3)
    have hz := Scratch.intJacobiMatrix_det_zero_odd (p:=p) (d:=d) hp_eq h3 hd_odd
    rw [hA]
    exact hz
