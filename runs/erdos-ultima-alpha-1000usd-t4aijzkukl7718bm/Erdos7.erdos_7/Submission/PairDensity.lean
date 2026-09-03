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


/-! Pairwise nonresonance for the two largest odd moduli. -/

namespace Erdos7Reduction

private theorem stdAddChar_mul_int (m k : ℕ) [NeZero m] [NeZero k] (u v : ℤ) :
    ZMod.stdAddChar (u : ZMod m) * ZMod.stdAddChar (v : ZMod k) =
      ZMod.stdAddChar ((u * k + v * m : ℤ) : ZMod (m * k)) := by
  rw [ZMod.stdAddChar_coe, ZMod.stdAddChar_coe, ZMod.stdAddChar_coe,
    ← Complex.exp_add]
  congr 1
  push_cast
  have hm : (m : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne m)
  have hk : (k : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne k)
  field_simp

private theorem stdAddChar_int_eq_one_iff (m : ℕ) [NeZero m] (u : ℤ) :
    ZMod.stdAddChar (u : ZMod m) = 1 ↔ (m : ℤ) ∣ u := by
  rw [← (ZMod.stdAddChar (N := m)).map_zero_eq_one,
    ZMod.injective_stdAddChar.eq_iff, ZMod.intCast_zmod_eq_zero_iff_dvd]

/-- An odd pair cannot resonate positively with a smaller modulus. -/
theorem odd_pair_add_nonresonance (m k n : ℕ) (hm : Odd m) (hk : Odd k)
    (hn : 0 < n) (hnm : n < m) (hnk : n < k) :
    ¬ m * k ∣ n * k + n * m := by
  intro hd
  have hk0 : 0 < k := by omega
  have hp : 0 < n * k + n * m := by positivity
  have hlt : n * k + n * m < 2 * (m * k) := by
    have h₁ := Nat.mul_lt_mul_of_pos_right hnm (by omega : 0 < k)
    have h₂ := Nat.mul_lt_mul_of_pos_right hnk (by omega : 0 < m)
    nlinarith
  have heq := Nat.eq_of_dvd_of_lt_two_mul (ne_of_gt hp) hd hlt
  have he : Even (m * k) := by
    rw [← heq, ← Nat.mul_add]
    exact (hk.add_odd hm).mul_left n
  exact (Nat.not_even_iff_odd.mpr (hm.mul hk)) he

/-- The difference of reciprocal characters of distinct moduli cannot resonate
with a smaller modulus. This part does not require oddness. -/
theorem pair_sub_nonresonance (m k n : ℕ) (hn : 0 < n)
    (hnk : n < k) (hkm : k < m) :
    ¬ (m * k : ℤ) ∣ (n : ℤ) * k - (n : ℤ) * m := by
  intro hd
  have hd' : m * k ∣ n * (m - k) := by
    apply Int.natCast_dvd_natCast.mp
    convert dvd_neg.mpr hd using 1
    push_cast [Nat.cast_sub hkm.le]
    ring
  have hpos : 0 < n * (m - k) := Nat.mul_pos hn (Nat.sub_pos_of_lt hkm)
  have hlt : n * (m - k) < m * k := by
    have h₁ := Nat.mul_lt_mul_of_pos_right hnk (Nat.sub_pos_of_lt hkm)
    have hsub : m - k + k = m := Nat.sub_add_cancel hkm.le
    nlinarith
  exact (not_lt_of_ge (Nat.le_of_dvd hpos hd')) hlt

/-- Both mixed character frequencies are nontrivial below the two largest odd moduli. -/
theorem odd_pair_character_nonresonance (m k n : ℕ) (hm : Odd m) (hk : Odd k)
    (hn : 0 < n) (hnk : n < k) (hkm : k < m) :
    letI : NeZero m := ⟨by omega⟩
    letI : NeZero k := ⟨by omega⟩
    ZMod.stdAddChar (n : ZMod m) * ZMod.stdAddChar (n : ZMod k) ≠ 1 ∧
      ZMod.stdAddChar (n : ZMod m) * ZMod.stdAddChar (-(n : ℤ) : ZMod k) ≠ 1 := by
  letI : NeZero m := ⟨by omega⟩
  letI : NeZero k := ⟨by omega⟩
  constructor
  · intro h
    have hz : (m * k : ℤ) ∣ (n : ℤ) * k + (n : ℤ) * m := by
      apply (stdAddChar_int_eq_one_iff (m * k) _).mp
      rw [← stdAddChar_mul_int]
      simpa only [Int.cast_natCast, Int.cast_neg] using h
    have hnat : m * k ∣ n * k + n * m := by exact_mod_cast hz
    exact odd_pair_add_nonresonance m k n hm hk hn (lt_trans hnk hkm) hnk hnat
  · intro h
    have hz : (m * k : ℤ) ∣ (n : ℤ) * k - (n : ℤ) * m := by
      apply (stdAddChar_int_eq_one_iff (m * k) _).mp
      rw [sub_eq_add_neg, ← neg_mul, ← stdAddChar_mul_int]
      simpa only [Int.cast_natCast, Int.cast_neg] using h
    exact pair_sub_nonresonance m k n hn hnk hkm hz

#print axioms odd_pair_character_nonresonance
end Erdos7Reduction

namespace Erdos7Reduction
open Finset

private theorem eigen_sum_eq_zero {G : Type*} [AddCommGroup G] [Fintype G]
    (P : G → Prop) [DecidablePred P] (h : G) (g : G → ℂ) (c : ℂ)
    (hP : ∀ x, P (x + h) ↔ P x) (hg : ∀ x, g (x + h) = c * g x)
    (hc : c ≠ 1) : (∑ x, if P x then g x else 0) = 0 := by
  have hsum : (∑ x, if P (x + h) then g (x + h) else 0) =
      ∑ x, if P x then g x else 0 :=
    Fintype.sum_bijective _ (AddGroup.addRight_bijective h) _ _ (fun _ => rfl)
  have ht (x : G) : (if P (x + h) then g (x + h) else 0) =
      c * (if P x then g x else 0) := by
    simp only [hP, hg]
    split_ifs <;> simp
  simp_rw [ht] at hsum
  rw [← Finset.mul_sum] at hsum
  exact eq_zero_of_mul_eq_self_left hc hsum

private theorem pair_weight_sum {G : Type*} [AddCommGroup G] [Fintype G]
    (χ ψ : AddChar G ℂ) (a b h : G) (P : G → Prop) [DecidablePred P]
    (hP : ∀ x, P (x + h) ↔ P x)
    (hχ : χ h ≠ 1) (hψ : ψ h ≠ 1)
    (hplus : χ h * ψ h ≠ 1) (hminus : χ h * ψ (-h) ≠ 1) :
    (∑ x, if P x then (1 - (χ (x - a)).re) * (1 - (ψ (x - b)).re) else 0) =
      ∑ x, if P x then (1 : ℝ) else 0 := by
  have hzχ := twisted_sum_eq_zero χ P a h hP hχ
  have hzψ := twisted_sum_eq_zero ψ P b h hP hψ
  have hshift (x c : G) : x + h - c = h + (x - c) := by abel
  have hzplus : (∑ x, if P x then χ (x - a) * ψ (x - b) else 0) = 0 := by
    apply eigen_sum_eq_zero P h _ (χ h * ψ h) hP _ hplus
    intro x
    dsimp only
    simp only [hshift, AddChar.map_add_eq_mul]
    ring
  have hm' : χ h * (starRingEnd ℂ) (ψ h) ≠ 1 := by
    simpa only [ψ.map_neg_eq_inv, Complex.inv_eq_conj (ψ.norm_apply h)] using hminus
  have hzminus : (∑ x, if P x then
      χ (x - a) * (starRingEnd ℂ) (ψ (x - b)) else 0) = 0 := by
    apply eigen_sum_eq_zero P h _ (χ h * (starRingEnd ℂ) (ψ h)) hP _ hm'
    intro x
    dsimp only
    simp only [hshift, AddChar.map_add_eq_mul, map_mul]
    ring
  have ht (x : G) :
      (if P x then (1 - (χ (x - a)).re) * (1 - (ψ (x - b)).re) else 0) =
        (if P x then (1 : ℝ) else 0) - (if P x then χ (x - a) else 0).re -
        (if P x then ψ (x - b) else 0).re +
        ((if P x then χ (x - a) * ψ (x - b) else 0).re +
          (if P x then χ (x - a) * (starRingEnd ℂ) (ψ (x - b)) else 0).re) / 2 := by
    split_ifs
    · simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
      ring
    · simp
  simp_rw [ht]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_div,
    ← Complex.re_sum, hzχ, hzψ, hzplus, hzminus, Complex.zero_re,
    sub_zero, add_zero, zero_div]

private theorem weighted_cover_omit {G ι : Type*} [Fintype G] [Fintype ι]
    [DecidableEq ι] (P : ι → G → Prop) [∀ i, DecidablePred (P i)]
    (hcover : ∀ x, ∃ i, P i x) (s : Finset ι) (w : G → ℝ)
    (hw : ∀ x, 0 ≤ w x) (hzero : ∀ i ∈ s, ∀ x, P i x → w x = 0) :
    ∑ x, w x ≤ ∑ i ∈ Finset.univ \ s, ∑ x, if P i x then w x else 0 := by
  have hpoint (x : G) : w x ≤ ∑ i ∈ Finset.univ \ s, if P i x then w x else 0 := by
    obtain ⟨i, hi⟩ := hcover x
    by_cases his : i ∈ s
    · rw [hzero i his x hi]
      simp
    · calc
        w x = if P i x then w x else 0 := by simp [hi]
        _ ≤ ∑ j ∈ Finset.univ \ s, if P j x then w x else 0 :=
          Finset.single_le_sum (f := fun j => if P j x then w x else 0)
            (by intro j _; dsimp only; split_ifs; exact hw x; exact le_rfl) (by simp [his])
  calc
    _ ≤ ∑ x, ∑ i ∈ Finset.univ \ s, if P i x then w x else 0 :=
      Finset.sum_le_sum (fun x _ => hpoint x)
    _ = _ := Finset.sum_comm

end Erdos7Reduction

namespace Erdos7Reduction
open Finset

/-- For a covering with distinct largest two moduli, both odd, the reciprocal
sum after omitting those two moduli is still at least one. -/
theorem density_omit_two_largest_odd {ι : Type} [Fintype ι] [DecidableEq ι]
    (m : ι → ℕ) (a : ι → ℤ) (hm : ∀ i, 0 < m i)
    (hcover : ∀ x : ℤ, ∃ i, (m i : ℤ) ∣ x - a i)
    (i₀ i₁ : ι) (hodd₀ : Odd (m i₀)) (hodd₁ : Odd (m i₁))
    (hi₁ : 1 < m i₁) (h10 : m i₁ < m i₀)
    (hmax : ∀ i, i ≠ i₀ → i ≠ i₁ → m i < m i₁)
    (N : ℕ) (hN : 0 < N) (hdiv : ∀ i, m i ∣ N) :
    1 ≤ ∑ i ∈ Finset.univ \ {i₀, i₁}, (m i : ℝ)⁻¹ := by
  classical
  letI : NeZero N := ⟨by omega⟩
  letI (i : ι) : NeZero (m i) := ⟨by have := hm i; omega⟩
  let f (i : ι) := ZMod.castHom (hdiv i) (ZMod (m i))
  let χ (i : ι) : AddChar (ZMod N) ℂ :=
    ZMod.stdAddChar.compAddMonoidHom (f i).toAddMonoidHom
  have hχnat (i : ι) (n : ℕ) : χ i (n : ZMod N) = 1 ↔ m i ∣ n := by
    change ZMod.stdAddChar ((f i) (n : ZMod N)) = 1 ↔ _
    rw [map_natCast, ← (ZMod.stdAddChar (N := m i)).map_zero_eq_one,
      ZMod.injective_stdAddChar.eq_iff]
    exact CharP.cast_eq_zero_iff (ZMod (m i)) (m i) n
  have hnr (n : ℕ) (hn : 0 < n) (hn₁ : n < m i₁) :
      χ i₀ (n : ZMod N) ≠ 1 ∧ χ i₁ (n : ZMod N) ≠ 1 ∧
      χ i₀ (n : ZMod N) * χ i₁ (n : ZMod N) ≠ 1 ∧
      χ i₀ (n : ZMod N) * χ i₁ (-(n : ZMod N)) ≠ 1 := by
    refine ⟨(hχnat i₀ n).not.mpr (Nat.not_dvd_of_pos_of_lt hn (lt_trans hn₁ h10)),
      (hχnat i₁ n).not.mpr (Nat.not_dvd_of_pos_of_lt hn hn₁), ?_⟩
    have hp := odd_pair_character_nonresonance (m i₀) (m i₁) n hodd₀ hodd₁ hn hn₁ h10
    change ZMod.stdAddChar (f i₀ (n : ZMod N)) *
        ZMod.stdAddChar (f i₁ (n : ZMod N)) ≠ 1 ∧
      ZMod.stdAddChar (f i₀ (n : ZMod N)) *
        ZMod.stdAddChar (f i₁ (-(n : ZMod N))) ≠ 1
    simpa only [map_natCast, map_neg, Int.cast_natCast] using hp
  let P (i : ι) (x : ZMod N) : Prop := f i x = (a i : ZMod (m i))
  have hPcover (x : ZMod N) : ∃ i, P i x := by
    obtain ⟨i, hi⟩ := hcover (x.val : ℤ)
    refine ⟨i, ?_⟩
    dsimp [P]
    rw [← ZMod.natCast_zmod_val x, map_natCast]
    symm
    simpa only [Int.cast_natCast] using
      (ZMod.intCast_eq_intCast_iff_dvd_sub (a i) (x.val : ℤ) (m i)).mpr hi
  let u (i : ι) (x : ZMod N) : ℝ := 1 - (χ i (x - a i)).re
  let w (x : ZMod N) : ℝ := u i₀ x * u i₁ x
  have hu (i : ι) (x : ZMod N) : 0 ≤ u i x := by
    dsimp [u]
    have h := Complex.re_le_norm (χ i (x - a i))
    rw [(χ i).norm_apply] at h
    linarith
  have hw (x : ZMod N) : 0 ≤ w x := mul_nonneg (hu i₀ x) (hu i₁ x)
  have huzero (i : ι) (x : ZMod N) (hx : P i x) : u i x = 0 := by
    have hval : χ i (x - a i) = 1 := by
      change ZMod.stdAddChar (f i (x - a i)) = 1
      rw [map_sub, map_intCast, hx, sub_self, AddChar.map_zero_eq_one]
    simp [u, hval]
  have hzero (i : ι) (hi : i ∈ ({i₀, i₁} : Finset ι)) (x : ZMod N)
      (hx : P i x) : w x = 0 := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · simp [w, huzero i x hx]
    · simp [w, huzero i x hx]
  have hsumw : ∑ x : ZMod N, w x = (N : ℝ) := by
    obtain ⟨hc₀, hc₁, hp, hm⟩ := hnr 1 (by omega) hi₁
    have hh := pair_weight_sum (χ i₀) (χ i₁) (a i₀) (a i₁) (1 : ZMod N)
      (fun _ => True) (by simp) (by simpa using hc₀) (by simpa using hc₁)
      (by simpa using hp) (by simpa using hm)
    simpa only [w, u, if_true, Finset.sum_const, Finset.card_univ,
      ZMod.card, nsmul_eq_mul, mul_one] using hh
  have hsum_other (i : ι) (hi₀ : i ≠ i₀) (hi₁ : i ≠ i₁) :
      (∑ x : ZMod N, if P i x then w x else 0) = (N : ℝ) / m i := by
    have hPstep (x : ZMod N) : P i (x + (m i : ZMod N)) ↔ P i x := by
      dsimp [P]
      rw [map_add, map_natCast, ZMod.natCast_self, add_zero]
    obtain ⟨hc₀, hc₁, hp, hm⟩ := hnr (m i) (hm i) (hmax i hi₀ hi₁)
    have hh := pair_weight_sum (χ i₀) (χ i₁) (a i₀) (a i₁) (m i : ZMod N)
      (P i) hPstep hc₀ hc₁ hp hm
    change (∑ x : ZMod N, if P i x then w x else 0) = _ at hh
    rw [hh]
    simpa only [ZMod.card] using
      fiber_sum_one (f i).toAddMonoidHom (ZMod.castHom_surjective (hdiv i)) (a i)
  have hbound := weighted_cover_omit P hPcover {i₀, i₁} w hw hzero
  rw [hsumw] at hbound
  have heq : (∑ i ∈ Finset.univ \ {i₀, i₁},
        ∑ x : ZMod N, if P i x then w x else 0) =
      (N : ℝ) * ∑ i ∈ Finset.univ \ {i₀, i₁}, ((m i : ℝ)⁻¹) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have hn := (Finset.mem_sdiff.mp hi).2
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
    rw [hsum_other i hn.1 hn.2, div_eq_mul_inv]
  rw [heq] at hbound
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  nlinarith

#print axioms density_omit_two_largest_odd
end Erdos7Reduction
