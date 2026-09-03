import FormalConjecturesUtil

/-! A character-weighted necessary density inequality for arithmetic covers. -/

namespace Erdos7Reduction
open Finset

private theorem twisted_sum_eq_zero {G : Type*} [AddCommGroup G] [Fintype G]
    (χ : AddChar G ℂ) (P : G → Prop) [DecidablePred P] (a h : G)
    (hP : ∀ x, P (x + h) ↔ P x) (hχ : χ h ≠ 1) :
    (∑ x, if P x then χ (x - a) else 0) = 0 := by
  let S : ℂ := ∑ x, if P x then χ (x - a) else 0
  have hsum : (∑ x, if P (x + h) then χ (x + h - a) else 0) = S :=
    Fintype.sum_bijective _ (AddGroup.addRight_bijective h) _ _ (fun _ => rfl)
  have hterm (x : G) :
      (if P (x + h) then χ (x + h - a) else 0) =
        χ h * (if P x then χ (x - a) else 0) := by
    simp only [hP x]
    have heq : x + h - a = h + (x - a) := by abel
    rw [heq, χ.map_add_eq_mul]
    split_ifs <;> simp
  simp_rw [hterm] at hsum
  rw [← Finset.mul_sum] at hsum
  exact eq_zero_of_mul_eq_self_left hχ hsum

private theorem fiber_sum_one {G H : Type*} [AddGroup G] [AddGroup H]
    [Fintype G] [Fintype H] [DecidableEq H] (f : G →+ H)
    (hf : Function.Surjective f) (b : H) :
    (∑ x : G, if f x = b then (1 : ℝ) else 0) =
      (Fintype.card G : ℝ) / Fintype.card H := by
  classical
  have heq (y : H) : (Finset.univ.filter (fun x => f x = y)).card =
      (Finset.univ.filter (fun x => f x = b)).card :=
    AddMonoidHom.card_fiber_eq_of_mem_range f (hf y) (hf b)
  have hcard : Fintype.card G =
      Fintype.card H * (Finset.univ.filter (fun x => f x = b)).card := by
    have h := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset G))
      (t := (Finset.univ : Finset H)) (f := f) (fun _ _ => Finset.mem_univ _)
    simpa only [heq, Finset.card_univ, Finset.sum_const, nsmul_eq_mul] using h
  have hc : (Fintype.card H : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Fintype.card_pos : 0 < Fintype.card H))
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  apply (eq_div_iff hc).mpr
  exact_mod_cast (Nat.mul_comm _ _).trans hcard.symm

/-- A nonnegative character weight lets us omit one class from the density bound,
provided its character vanishes in average on every other class. -/
private theorem weighted_cover_bound {G ι : Type*} [AddCommGroup G]
    [Fintype G] [Fintype ι] [DecidableEq ι]
    (P : ι → G → Prop) [∀ i, DecidablePred (P i)]
    (hcover : ∀ x, ∃ i, P i x) (i₀ : ι) (w : G → ℝ)
    (hw : ∀ x, 0 ≤ w x) (hzero : ∀ x, P i₀ x → w x = 0) :
    ∑ x, w x ≤ ∑ i ∈ Finset.univ.erase i₀, ∑ x, if P i x then w x else 0 := by
  have hpoint (x : G) : w x ≤ ∑ i ∈ Finset.univ.erase i₀,
      if P i x then w x else 0 := by
    obtain ⟨i, hi⟩ := hcover x
    by_cases heq : i = i₀
    · subst i
      rw [hzero x hi]
      exact Finset.sum_nonneg (by intro i _; split_ifs <;> positivity)
    · calc
        w x = if P i x then w x else 0 := by simp [hi]
        _ ≤ ∑ j ∈ Finset.univ.erase i₀, if P j x then w x else 0 :=
          Finset.single_le_sum (f := fun j => if P j x then w x else 0)
            (by intro j _; dsimp only; split_ifs; exact hw x; exact le_rfl) (by simp [heq])
  calc
    _ ≤ ∑ x, ∑ i ∈ Finset.univ.erase i₀, if P i x then w x else 0 :=
      Finset.sum_le_sum (fun x _ => hpoint x)
    _ = _ := Finset.sum_comm


/-- In a finite arithmetic cover, a modulus dividing no other modulus can be
omitted from the usual reciprocal-density lower bound. -/
theorem density_omit_divisibility_maximal {ι : Type} [Fintype ι] [DecidableEq ι]
    (m : ι → ℕ) (a : ι → ℤ) (hm : ∀ i, 0 < m i)
    (hcover : ∀ x : ℤ, ∃ i, (m i : ℤ) ∣ x - a i)
    (i₀ : ι) (hi₀ : 1 < m i₀) (hmax : ∀ i, i ≠ i₀ → ¬ m i₀ ∣ m i)
    (N : ℕ) (hN : 0 < N) (hdiv : ∀ i, m i ∣ N) :
    1 ≤ ∑ i ∈ Finset.univ.erase i₀, ((m i : ℝ)⁻¹) := by
  classical
  letI : NeZero N := ⟨by omega⟩
  letI (i : ι) : NeZero (m i) := ⟨by have := hm i; omega⟩
  let f (i : ι) := ZMod.castHom (hdiv i) (ZMod (m i))
  let χ : AddChar (ZMod N) ℂ :=
    ZMod.stdAddChar.compAddMonoidHom (f i₀).toAddMonoidHom
  have hχnat (n : ℕ) : χ (n : ZMod N) = 1 ↔ m i₀ ∣ n := by
    change ZMod.stdAddChar ((f i₀) (n : ZMod N)) = 1 ↔ _
    rw [map_natCast, ← (ZMod.stdAddChar (N := m i₀)).map_zero_eq_one,
      ZMod.injective_stdAddChar.eq_iff]
    exact CharP.cast_eq_zero_iff (ZMod (m i₀)) (m i₀) n
  have hχone : χ 1 ≠ 1 := by
    simpa only [Nat.cast_one] using
      (hχnat 1).not.mpr (Nat.not_dvd_of_pos_of_lt (by omega) hi₀)
  let P (i : ι) (x : ZMod N) : Prop := f i x = (a i : ZMod (m i))
  have hPcover (x : ZMod N) : ∃ i, P i x := by
    obtain ⟨i, hi⟩ := hcover (x.val : ℤ)
    refine ⟨i, ?_⟩
    dsimp [P]
    rw [← ZMod.natCast_zmod_val x, map_natCast]
    symm
    simpa only [Int.cast_natCast] using
      (ZMod.intCast_eq_intCast_iff_dvd_sub (a i) (x.val : ℤ) (m i)).mpr hi
  let a₀ : ZMod N := (a i₀ : ZMod N)
  let w (x : ZMod N) : ℝ := 1 - (χ (x - a₀)).re
  have hw (x : ZMod N) : 0 ≤ w x := by
    dsimp [w]
    have h := Complex.re_le_norm (χ (x - a₀))
    rw [χ.norm_apply] at h
    linarith
  have hzero (x : ZMod N) (hx : P i₀ x) : w x = 0 := by
    have hval : χ (x - a₀) = 1 := by
      change ZMod.stdAddChar (f i₀ (x - a₀)) = 1
      rw [map_sub]
      change ZMod.stdAddChar (f i₀ x - f i₀ (a i₀ : ZMod N)) = 1
      rw [map_intCast, hx, sub_self, AddChar.map_zero_eq_one]
    simp [w, hval]
  have hsumχ : ∑ x : ZMod N, χ (x - a₀) = 0 := by
    simpa using twisted_sum_eq_zero χ (fun _ => True) a₀ 1 (by simp) hχone
  have hsumw : ∑ x : ZMod N, w x = (N : ℝ) := by
    simp only [w, Finset.sum_sub_distrib, ← Complex.re_sum, hsumχ,
      Complex.zero_re, sub_zero, Finset.sum_const, Finset.card_univ,
      ZMod.card, nsmul_eq_mul, mul_one]
  have hsum_other (i : ι) (hi : i ≠ i₀) :
      (∑ x : ZMod N, if P i x then w x else 0) = (N : ℝ) / m i := by
    have hPstep (x : ZMod N) : P i (x + (m i : ZMod N)) ↔ P i x := by
      dsimp [P]
      rw [map_add, map_natCast, ZMod.natCast_self, add_zero]
    have hχstep : χ (m i : ZMod N) ≠ 1 := by
      exact (hχnat (m i)).not.mpr (hmax i hi)
    have hz := twisted_sum_eq_zero χ (P i) a₀ (m i : ZMod N) hPstep hχstep
    have ht (x : ZMod N) : (if P i x then w x else 0) =
        (if P i x then (1 : ℝ) else 0) -
          (if P i x then χ (x - a₀) else 0).re := by
      dsimp [w]
      split_ifs <;> simp
    simp_rw [ht]
    rw [Finset.sum_sub_distrib, ← Complex.re_sum, hz, Complex.zero_re, sub_zero]
    simpa only [ZMod.card] using
      fiber_sum_one (f i).toAddMonoidHom (ZMod.castHom_surjective (hdiv i)) (a i)
  have hbound := weighted_cover_bound P hPcover i₀ w hw hzero
  rw [hsumw] at hbound
  have heq : (∑ i ∈ Finset.univ.erase i₀,
        ∑ x : ZMod N, if P i x then w x else 0) =
      (N : ℝ) * ∑ i ∈ Finset.univ.erase i₀, ((m i : ℝ)⁻¹) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hsum_other i (Finset.mem_erase.mp hi).1, div_eq_mul_inv]
  rw [heq] at hbound
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  nlinarith

#print axioms density_omit_divisibility_maximal

end Erdos7Reduction
