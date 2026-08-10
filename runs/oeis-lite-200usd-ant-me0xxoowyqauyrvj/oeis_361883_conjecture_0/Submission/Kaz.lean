import FormalConjectures.Util.ProblemImports
open Nat Finset BigOperators Polynomial

namespace Kaz

variable {p : ℕ}

noncomputable def Ysub : Polynomial ℤ := X^2 + X

theorem natDegree_Ysub : (Ysub : Polynomial ℤ).natDegree = 2 := by
  unfold Ysub; compute_degree!

theorem Ysub_monic : (Ysub : Polynomial ℤ).Monic := by
  rw [Polynomial.Monic.def, Polynomial.leadingCoeff, natDegree_Ysub]
  unfold Ysub
  rw [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X]
  norm_num

theorem Ysub_comp_sym : (Ysub : Polynomial ℤ).comp (-1 - X) = Ysub := by
  unfold Ysub
  rw [Polynomial.add_comp, Polynomial.pow_comp, Polynomial.X_comp]; ring

theorem natDegree_inner : (-1 - X : Polynomial ℤ).natDegree = 1 := by
  rw [show (-1 - X : Polynomial ℤ) = C (-1) - X by simp]; compute_degree!

theorem leadingCoeff_inner : (-1 - X : Polynomial ℤ).leadingCoeff = -1 := by
  rw [show (-1 - X : Polynomial ℤ) = -(X + C 1) by rw [map_one]; ring, Polynomial.leadingCoeff_neg,
      (Polynomial.monic_X_add_C (1:ℤ)).leadingCoeff]

/-- Any integer polynomial fixed by `X ↦ -1-X` is a polynomial in `X^2+X`. -/
theorem sym_rep (f : Polynomial ℤ) (hf : f.comp (-1 - X) = f) :
    ∃ g : Polynomial ℤ, f = g.comp Ysub := by
  induction hn : f.natDegree using Nat.strong_induction_on generalizing f with
  | _ n IH =>
    subst hn
    by_cases hf0 : f = 0
    · exact ⟨0, by simp [hf0]⟩
    · have hlc0 : f.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hf0
      have hne : Even f.natDegree := by
        have hcomp := congrArg Polynomial.leadingCoeff hf
        rw [Polynomial.leadingCoeff_comp (by rw [natDegree_inner]; norm_num),
            leadingCoeff_inner] at hcomp
        have h1 : f.leadingCoeff * (-1)^f.natDegree = f.leadingCoeff * 1 := by
          rw [mul_one]; linarith [hcomp]
        have h2 : (-1 : ℤ)^f.natDegree = 1 := mul_left_cancel₀ hlc0 h1
        rwa [neg_one_pow_eq_one_iff_even (by norm_num)] at h2
      obtain ⟨d, hd⟩ := hne
      have hd2 : f.natDegree = 2 * d := by omega
      have hYdmon : (Ysub ^ d : Polynomial ℤ).Monic := Ysub_monic.pow d
      set h := C f.leadingCoeff * Ysub ^ d with hh
      have hh_deg : h.natDegree = 2 * d := by
        rw [hh, Polynomial.natDegree_C_mul hlc0, Polynomial.natDegree_pow, natDegree_Ysub,
            Nat.mul_comm]
      have hh_lc : h.leadingCoeff = f.leadingCoeff := by
        rw [hh, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C, hYdmon.leadingCoeff, mul_one]
      have hh_ne : h ≠ 0 := by
        rw [← Polynomial.leadingCoeff_ne_zero, hh_lc]; exact hlc0
      have hh_sym : h.comp (-1 - X) = h := by
        rw [hh, Polynomial.mul_comp, Polynomial.C_comp, Polynomial.pow_comp, Ysub_comp_sym]
      set f' := f - h with hf'
      have hf'sym : f'.comp (-1 - X) = f' := by rw [hf', Polynomial.sub_comp, hf, hh_sym]
      by_cases hf'0 : f' = 0
      · refine ⟨C f.leadingCoeff * X ^ d, ?_⟩
        have hfe : f = h := by rw [hf'] at hf'0; exact sub_eq_zero.mp hf'0
        rw [Polynomial.mul_comp, Polynomial.C_comp, Polynomial.pow_comp, Polynomial.X_comp, ← hh]
        exact hfe
      · have hdeg_eq : f.degree = h.degree := by
          rw [Polynomial.degree_eq_natDegree hf0, Polynomial.degree_eq_natDegree hh_ne, hd2, hh_deg]
        have hdeg_lt : f'.degree < f.degree := by
          rw [hf']; exact Polynomial.degree_sub_lt hdeg_eq hf0 hh_lc.symm
        have hnd_lt : f'.natDegree < f.natDegree :=
          Polynomial.natDegree_lt_natDegree hf'0 hdeg_lt
        obtain ⟨g', hg'⟩ := IH f'.natDegree hnd_lt f' hf'sym rfl
        refine ⟨g' + C f.leadingCoeff * X ^ d, ?_⟩
        rw [Polynomial.add_comp, ← hg', Polynomial.mul_comp, Polynomial.C_comp,
            Polynomial.pow_comp, Polynomial.X_comp, hf']; ring

/-- The block polynomial `block(l) = ∏_{i=1}^{p-1} (i + p·l)` as a polynomial in `l`. -/
noncomputable def bpoly (p : ℕ) : Polynomial ℤ := ∏ i ∈ Icc 1 (p-1), (C (i:ℤ) + C (p:ℤ) * X)

theorem bpoly_sym (p : ℕ) (hodd : Odd p) (hp : 5 ≤ p) :
    (bpoly p).comp (-1 - X) = bpoly p := by
  unfold bpoly
  rw [Polynomial.prod_comp]
  have hpar : Even (p - 1) := by
    rcases hodd with ⟨k, hk⟩; exact ⟨k, by omega⟩
  have key : ∀ i ∈ Icc 1 (p-1), (C (i:ℤ) + C (p:ℤ) * X).comp (-1 - X)
      = -(C (p:ℤ) * X + C ((p:ℤ) - (i:ℤ))) := by
    intro i _
    rw [Polynomial.add_comp, Polynomial.C_comp, Polynomial.mul_comp, Polynomial.C_comp,
        Polynomial.X_comp, Polynomial.C_sub]
    ring
  rw [Finset.prod_congr rfl key]
  rw [Finset.prod_neg, Nat.card_Icc, show p - 1 + 1 - 1 = p - 1 by omega,
      Even.neg_one_pow hpar, one_mul]
  apply Finset.prod_nbij' (fun i => p - i) (fun j => p - j)
  · intro i hi; simp only [Finset.mem_Icc] at *; omega
  · intro j hj; simp only [Finset.mem_Icc] at *; omega
  · intro i hi; simp only [Finset.mem_Icc] at hi; omega
  · intro j hj; simp only [Finset.mem_Icc] at hj; omega
  · intro i hi; simp only [Finset.mem_Icc] at hi
    rw [Nat.cast_sub (by omega)]; ring

/-- `Ysub^k` has zero constant term for `k ≥ 1`. -/
theorem Ysub_pow_coeff0 (k : ℕ) (hk : 1 ≤ k) : (Ysub ^ k : Polynomial ℤ).coeff 0 = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  rw [pow_succ, Polynomial.mul_coeff_zero]
  unfold Ysub
  simp

/-- Constant coefficient of a composition with `Ysub`. -/
theorem comp_Ysub_coeff0 (g : Polynomial ℤ) : (g.comp Ysub).coeff 0 = g.coeff 0 := by
  rw [Polynomial.comp, Polynomial.eval₂_eq_sum, Polynomial.sum_def, Polynomial.finset_sum_coeff]
  rw [Finset.sum_eq_single 0]
  · simp
  · intro b hb hb0
    rw [Polynomial.coeff_C_mul, Ysub_pow_coeff0 b (by omega), mul_zero]
  · intro h
    simp only [Polynomial.mem_support_iff, not_not] at h
    simp [h]

/-- `Ysub^k` has zero coeff at 1 for `k ≥ 2`. -/
theorem Ysub_pow_coeff1 (k : ℕ) (hk : 2 ≤ k) : (Ysub ^ k : Polynomial ℤ).coeff 1 = 0 := by
  have hfac : (Ysub ^ k : Polynomial ℤ) = X ^ k * (X + 1) ^ k := by
    rw [← mul_pow]; congr 1; unfold Ysub; ring
  rw [hfac, Polynomial.coeff_mul]
  apply Finset.sum_eq_zero
  intro x hx
  rw [Finset.mem_antidiagonal] at hx
  have : (X ^ k : Polynomial ℤ).coeff x.1 = 0 := by
    rw [Polynomial.coeff_X_pow]; rw [if_neg]; omega
  rw [this, zero_mul]

/-- Coeff at 1 of a composition with `Ysub`. -/
theorem comp_Ysub_coeff1 (g : Polynomial ℤ) : (g.comp Ysub).coeff 1 = g.coeff 1 := by
  rw [Polynomial.comp, Polynomial.eval₂_eq_sum, Polynomial.sum_def, Polynomial.finset_sum_coeff]
  rw [Finset.sum_eq_single 1]
  · rw [Polynomial.coeff_C_mul]; unfold Ysub
    rw [pow_one]
    simp
  · intro b hb hb1
    rw [Polynomial.coeff_C_mul]
    rcases Nat.lt_or_ge b 2 with h | h
    · interval_cases b
      · rw [pow_zero, Polynomial.coeff_one]; simp
      · omega
    · rw [Ysub_pow_coeff1 b h, mul_zero]
  · intro h
    simp only [Polynomial.mem_support_iff, not_not] at h
    simp [h]

theorem prodIcc_fact (n : ℕ) : ∏ i ∈ Icc 1 n, i = n ! := by
  induction n with
  | zero => simp
  | succ k IH =>
    rw [show Icc 1 (k+1) = insert (k+1) (Icc 1 k) by
          ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega,
        Finset.prod_insert (by simp only [Finset.mem_Icc]; omega), IH, Nat.factorial_succ]

/-- `bpoly.coeff 0 = (p-1)!`. -/
theorem bpoly_coeff0 (p : ℕ) : (bpoly p).coeff 0 = ((p - 1)! : ℕ) := by
  rw [Polynomial.coeff_zero_eq_eval_zero]
  unfold bpoly
  rw [Polynomial.eval_prod, ← prodIcc_fact (p-1)]
  push_cast
  apply Finset.prod_congr rfl
  intro i _; simp

/-- The symmetric sum `Σ_i ∏_{j≠i} j`. -/
noncomputable def Ssum (p : ℕ) : ℤ := ∑ i ∈ Icc 1 (p-1), ∏ j ∈ (Icc 1 (p-1)).erase i, (j:ℤ)

theorem bpoly_coeff1_eq (p : ℕ) : (bpoly p).coeff 1 = (p:ℤ) * Ssum p := by
  have h1 : (bpoly p).coeff 1 = (Polynomial.derivative (bpoly p)).coeff 0 := by
    rw [Polynomial.coeff_derivative]; push_cast; ring
  rw [h1, Polynomial.coeff_zero_eq_eval_zero]
  unfold bpoly Ssum
  rw [Polynomial.derivative_prod_finset, Polynomial.eval_finset_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Polynomial.eval_mul, Polynomial.eval_prod]
  have hd : Polynomial.derivative (C (i:ℤ) + C (p:ℤ) * X) = C (p:ℤ) := by
    simp [Polynomial.derivative_C, Polynomial.derivative_mul]
  rw [hd, Polynomial.eval_C, mul_comm]
  congr 1
  apply Finset.prod_congr rfl
  intro j _; simp

-- ===== Wolstenholme machinery (copied from Ref) =====
/-- In `ZMod (p^2)`, if the reduction of `X` to `ZMod p` is `0`, then `p * X = 0`. -/
theorem pmul_eq_zero (hp : 0 < p) (X : ZMod (p ^ 2))
    (h : (ZMod.castHom (dvd_pow_self p two_ne_zero) (ZMod p)) X = 0) :
    (p : ZMod (p ^ 2)) * X = 0 := by
  have hne : NeZero p := ⟨hp.ne'⟩
  have hpd : p ∣ X.val := by
    rw [ZMod.castHom_apply, ← ZMod.natCast_val, ZMod.natCast_eq_zero_iff] at h
    exact h
  obtain ⟨c, hc⟩ := hpd
  have e1 : (p : ZMod (p ^ 2)) * X = ((p * X.val : ℕ) : ZMod (p ^ 2)) := by
    rw [Nat.cast_mul, ZMod.natCast_zmod_val]
  rw [e1, hc, show p * (p * c) = p ^ 2 * c by ring, Nat.cast_mul,
      ZMod.natCast_self, zero_mul]

/-- `i` is a unit in `ZMod (p^2)` for `1 ≤ i ≤ p-1`. -/
theorem isUnit_cast2 [Fact p.Prime] (i : ℕ) (h1 : 1 ≤ i) (h2 : i ≤ p - 1) :
    IsUnit ((i : ℕ) : ZMod (p ^ 2)) := by
  have hp : p.Prime := Fact.out
  rw [ZMod.isUnit_iff_coprime]
  have hnd : ¬ p ∣ i := by intro hd; have := Nat.le_of_dvd (by omega) hd; omega
  exact (hp.coprime_iff_not_dvd.mpr hnd).symm.pow_right 2

/-- Harmonic order-2 sum vanishes mod p (recalled). -/
theorem harm2_p [Fact p.Prime] (hp5 : 5 ≤ p) :
    ∑ i ∈ (Icc 1 (p - 1) : Finset ℕ), ((i : ZMod p)⁻¹) ^ 2 = 0 := by
  -- reuse the standard FiniteField argument
  have hp0 : 0 < p := (Fact.out (p := p.Prime)).pos
  have hne : NeZero p := ⟨hp0.ne'⟩
  have key : ∑ x : ZMod p, (x⁻¹) ^ 2 = 0 := by
    have h := Equiv.sum_comp (Function.Involutive.toPerm (Inv.inv : ZMod p → ZMod p) inv_inv)
      (fun y => y ^ 2)
    simp only [Function.Involutive.coe_toPerm] at h
    rw [h]
    apply FiniteField.sum_pow_lt_card_sub_one
    rw [ZMod.card]; omega
  rw [show (∑ x : ZMod p, (x⁻¹)^2) = ∑ r ∈ Finset.range p, (((r : ZMod p))⁻¹)^2 by
    apply Finset.sum_nbij' (i := fun x : ZMod p => x.val) (j := fun r : ℕ => (r : ZMod p))
    · intro a _; simp [Finset.mem_range, ZMod.val_lt]
    · intro b _; exact Finset.mem_univ _
    · intro a _; exact ZMod.natCast_rightInverse a
    · intro b hb; exact ZMod.val_cast_of_lt (Finset.mem_range.mp hb)
    · intro a _; rw [ZMod.natCast_rightInverse a]] at key
  rw [show Finset.range p = insert 0 (Finset.Icc 1 (p-1)) by
    ext x; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega,
    Finset.sum_insert (by simp)] at key
  simp only [Nat.cast_zero, inv_zero] at key
  rw [zero_pow (by norm_num), zero_add] at key
  exact key

/-- **Wolstenholme**: `∑_{i=1}^{p-1} i⁻¹ ≡ 0 (mod p²)`, i.e. `= 0` in `ZMod (p²)`. -/
theorem wolstenholme_H1 [Fact p.Prime] (hp5 : 5 ≤ p) :
    ∑ i ∈ (Icc 1 (p - 1) : Finset ℕ), ((i : ZMod (p ^ 2))⁻¹) = 0 := by
  have hp : p.Prime := Fact.out
  have hp0 : 0 < p := hp.pos
  have hne : NeZero p := ⟨hp0.ne'⟩
  set s := ∑ i ∈ Icc 1 (p - 1), ((i : ZMod (p ^ 2))⁻¹) with hs
  -- reflection: s = ∑ (p - i)⁻¹
  have hrefl : s = ∑ i ∈ Icc 1 (p - 1), (((p - i : ℕ) : ZMod (p ^ 2))⁻¹) := by
    rw [hs]
    apply Finset.sum_nbij' (i := fun x => p - x) (j := fun x => p - x)
    · intro a ha; simp only [Finset.mem_Icc] at *; omega
    · intro a ha; simp only [Finset.mem_Icc] at *; omega
    · intro a ha; simp only [Finset.mem_Icc] at ha; omega
    · intro a ha; simp only [Finset.mem_Icc] at ha; omega
    · intro a ha; simp only [Finset.mem_Icc] at ha; rw [show p - (p - a) = a by omega]
  -- 2 s = ∑ (i⁻¹ + (p-i)⁻¹) = p · X  where X = ∑ (i (p-i))⁻¹
  have hpair : ∀ i ∈ Icc 1 (p - 1),
      ((i : ZMod (p^2))⁻¹) + (((p - i : ℕ) : ZMod (p^2))⁻¹)
        = (p : ZMod (p^2)) * (((i * (p - i) : ℕ) : ZMod (p^2))⁻¹) := by
    intro i hi
    simp only [Finset.mem_Icc] at hi
    have hprod : (((i * (p - i) : ℕ)) : ZMod (p^2)) = (i : ZMod (p^2)) * ((p - i : ℕ) : ZMod (p^2)) := by
      push_cast; ring
    have hsum' : (p : ZMod (p^2)) = (i : ZMod (p^2)) + ((p - i : ℕ) : ZMod (p^2)) := by
      rw [Nat.cast_sub (by omega)]; ring
    rw [hprod, hsum']
    set a := (i : ZMod (p^2)) with ha
    set b := ((p - i : ℕ) : ZMod (p^2)) with hb
    have hua : IsUnit a := isUnit_cast2 i hi.1 hi.2
    have hub : IsUnit b := isUnit_cast2 (p - i) (by omega) (by omega)
    have haa : a * a⁻¹ = 1 := ZMod.mul_inv_of_unit a hua
    have hbb : b * b⁻¹ = 1 := ZMod.mul_inv_of_unit b hub
    have hab : (a * b) * (a * b)⁻¹ = 1 := ZMod.mul_inv_of_unit (a * b) (hua.mul hub)
    have e1 : (a * b) * (a⁻¹ + b⁻¹) = a + b := by
      rw [mul_add, show a * b * a⁻¹ = b * (a * a⁻¹) by ring,
          show a * b * b⁻¹ = a * (b * b⁻¹) by ring, haa, hbb]; ring
    have e2 : (a * b) * ((a + b) * (a * b)⁻¹) = a + b := by
      rw [show (a * b) * ((a + b) * (a * b)⁻¹) = (a + b) * ((a * b) * (a * b)⁻¹) by ring,
          hab, mul_one]
    exact (hua.mul hub).mul_right_injective (e1.trans e2.symm)
  have h2s : (2 : ZMod (p^2)) * s = (p : ZMod (p^2)) * ∑ i ∈ Icc 1 (p - 1), (((i * (p - i) : ℕ) : ZMod (p^2))⁻¹) := by
    have : (2 : ZMod (p^2)) * s = s + s := by ring
    rw [this]
    nth_rewrite 2 [hrefl]
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl hpair
  -- Now show p · X = 0
  set X := ∑ i ∈ Icc 1 (p - 1), (((i * (p - i) : ℕ) : ZMod (p^2))⁻¹) with hX
  have hpX : (p : ZMod (p^2)) * X = 0 := by
    apply pmul_eq_zero hp0
    -- reduction of X to ZMod p equals -harm2 = 0
    rw [hX, map_sum]
    have hcastle : ∀ i ∈ Icc 1 (p - 1),
        (ZMod.castHom (dvd_pow_self p two_ne_zero) (ZMod p)) ((((i * (p - i) : ℕ)) : ZMod (p^2))⁻¹)
          = - (((i : ZMod p)⁻¹) ^ 2) := by
      intro i hi
      simp only [Finset.mem_Icc] at hi
      have hu : IsUnit (((i * (p - i) : ℕ)) : ZMod (p^2)) := by
        rw [Nat.cast_mul]
        exact (isUnit_cast2 i hi.1 hi.2).mul (isUnit_cast2 (p - i) (by omega) (by omega))
      set F := ZMod.castHom (dvd_pow_self p two_ne_zero) (ZMod p) with hF
      have hone : ((i * (p - i) : ℕ) : ZMod (p^2)) * (((i * (p - i) : ℕ) : ZMod (p^2))⁻¹) = 1 :=
        ZMod.mul_inv_of_unit _ hu
      have hmul1 : F ((i * (p - i) : ℕ) : ZMod (p^2)) * F (((i * (p - i) : ℕ) : ZMod (p^2))⁻¹) = 1 := by
        rw [← map_mul, hone, map_one]
      have hcu : F ((i * (p - i) : ℕ) : ZMod (p^2)) = -((i : ZMod p))^2 := by
        rw [hF, map_natCast, Nat.cast_mul,
            show ((p - i : ℕ) : ZMod p) = (p : ZMod p) - i by rw [Nat.cast_sub (by omega)],
            ZMod.natCast_self]
        ring
      rw [hcu] at hmul1
      have hthis : F (((i * (p - i) : ℕ) : ZMod (p^2))⁻¹) = (-((i : ZMod p))^2)⁻¹ :=
        eq_inv_of_mul_eq_one_right hmul1
      rw [hthis, ← neg_inv, inv_pow]
    rw [Finset.sum_congr rfl hcastle]
    rw [Finset.sum_neg_distrib]
    rw [harm2_p hp5]
    simp
  -- 2 is a unit, so s = 0
  have hu2 : IsUnit (2 : ZMod (p^2)) := by
    rw [show (2 : ZMod (p^2)) = ((2 : ℕ) : ZMod (p^2)) by norm_num, ZMod.isUnit_iff_coprime]
    have : ¬ p ∣ 2 := by intro hd; have := Nat.le_of_dvd (by norm_num) hd; omega
    exact (hp.coprime_iff_not_dvd.mpr this).symm.pow_right 2
  have : (2 : ZMod (p^2)) * s = 0 := by rw [h2s]; exact hpX
  exact (hu2.mul_right_eq_zero).mp this

/-- Each `l`-coefficient `bpoly.coeff k` is divisible by `p^k`. -/
theorem bpoly_coeff_dvd (p : ℕ) : ∀ k, (p:ℤ)^k ∣ (bpoly p).coeff k := by
  have gen : ∀ (s : Finset ℕ) (k : ℕ),
      (p:ℤ)^k ∣ (∏ i ∈ s, (C (i:ℤ) + C (p:ℤ) * X)).coeff k := by
    intro s
    induction s using Finset.induction with
    | empty =>
        intro k
        rcases Nat.eq_zero_or_pos k with hk | hk
        · subst hk; simp
        · rw [Finset.prod_empty, Polynomial.coeff_one, if_neg (by omega)]; simp
    | insert j t hj IH =>
        intro k
        rw [Finset.prod_insert hj]
        rw [show (C (j:ℤ) + C (p:ℤ) * X) * ∏ i ∈ t, (C (i:ℤ) + C (p:ℤ) * X)
              = C (j:ℤ) * (∏ i ∈ t, (C (i:ℤ) + C (p:ℤ) * X))
                + C (p:ℤ) * (X * ∏ i ∈ t, (C (i:ℤ) + C (p:ℤ) * X)) by ring]
        rw [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_C_mul]
        apply dvd_add
        · exact Dvd.dvd.mul_left (IH k) _
        · rcases Nat.eq_zero_or_pos k with hk | hk
          · subst hk; rw [Polynomial.coeff_X_mul_zero]; simp
          · obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
            rw [Polynomial.coeff_X_mul, pow_succ, mul_comm ((p:ℤ)^k') (p:ℤ)]
            exact mul_dvd_mul_left _ (IH k')
  intro k; exact gen _ k

/-- Composition coefficient as a finite sum over `g`'s support. -/
theorem comp_Ysub_coeff (g : Polynomial ℤ) (n : ℕ) :
    (g.comp Ysub).coeff n = ∑ j ∈ g.support, g.coeff j * (Ysub^j).coeff n := by
  rw [Polynomial.comp, Polynomial.eval₂_eq_sum, Polynomial.sum_def, Polynomial.finset_sum_coeff]
  apply Finset.sum_congr rfl
  intro j _; rw [Polynomial.coeff_C_mul]

theorem natDegree_Ysub_pow (j : ℕ) : (Ysub ^ j : Polynomial ℤ).natDegree = 2 * j := by
  rw [Polynomial.natDegree_pow, natDegree_Ysub, Nat.mul_comm]

theorem Ysub_pow_coeff_self (j : ℕ) : (Ysub ^ j : Polynomial ℤ).coeff (2 * j) = 1 := by
  have hm : (Ysub ^ j : Polynomial ℤ).Monic := Ysub_monic.pow j
  have := hm.leadingCoeff
  rwa [Polynomial.leadingCoeff, natDegree_Ysub_pow] at this

/-- `b_i` valuation for `i ≥ 2`: `p⁴ ∣ g.coeff i`, by downward induction. -/
theorem block_g_coeff4 (g : Polynomial ℤ) (hg : bpoly p = g.comp Ysub) :
    ∀ t i, g.natDegree - i = t → 2 ≤ i → (p:ℤ)^4 ∣ g.coeff i := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t IH =>
    intro i ht hi
    set D := g.natDegree with hD
    by_cases hisupp : i ∈ g.support
    · have hbc : (bpoly p).coeff (2*i)
          = g.coeff i + ∑ j ∈ g.support.erase i, g.coeff j * (Ysub^j).coeff (2*i) := by
        rw [hg, comp_Ysub_coeff, ← Finset.add_sum_erase _ _ hisupp, Ysub_pow_coeff_self, mul_one]
      have hgi : g.coeff i
          = (bpoly p).coeff (2*i) - ∑ j ∈ g.support.erase i, g.coeff j * (Ysub^j).coeff (2*i) := by
        rw [hbc]; ring
      rw [hgi]
      apply _root_.dvd_sub
      · exact dvd_trans (pow_dvd_pow _ (by omega)) (bpoly_coeff_dvd p (2*i))
      · apply Finset.dvd_sum
        intro j hj
        rw [Finset.mem_erase] at hj
        obtain ⟨hjne, hjsupp⟩ := hj
        have hjD : j ≤ D := Polynomial.le_natDegree_of_mem_supp j hjsupp
        rcases Nat.lt_or_ge j i with hji | hji
        · have hz : (Ysub^j : Polynomial ℤ).coeff (2*i) = 0 := by
            apply Polynomial.coeff_eq_zero_of_natDegree_lt
            rw [natDegree_Ysub_pow]; omega
          rw [hz, mul_zero]; exact dvd_zero _
        · have hjgt : i < j := lt_of_le_of_ne hji (Ne.symm hjne)
          have hgj : (p:ℤ)^4 ∣ g.coeff j := IH (D - j) (by omega) j rfl (by omega)
          exact Dvd.dvd.mul_right hgj _
    · rw [Polynomial.mem_support_iff, not_not] at hisupp; rw [hisupp]; exact dvd_zero _

/-- Wolstenholme for the symmetric sum: `p² ∣ Ssum`. -/
theorem ssum_dvd [Fact p.Prime] (hp5 : 5 ≤ p) : (p:ℤ)^2 ∣ Ssum p := by
  have hp : p.Prime := Fact.out
  have hcast : ((p:ℤ)^2) = ((p^2 : ℕ) : ℤ) := by push_cast; ring
  rw [hcast, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
  unfold Ssum
  push_cast
  have key : ∀ i ∈ Icc 1 (p-1), ∏ j ∈ (Icc 1 (p-1)).erase i, ((j:ℕ):ZMod (p^2))
      = ((i:ℕ):ZMod (p^2))⁻¹ * ∏ j ∈ Icc 1 (p-1), ((j:ℕ):ZMod (p^2)) := by
    intro i hi
    have hu : IsUnit ((i:ℕ):ZMod (p^2)) := by
      simp only [Finset.mem_Icc] at hi; exact isUnit_cast2 i hi.1 hi.2
    rw [← Finset.mul_prod_erase _ (fun j => ((j:ℕ):ZMod (p^2))) hi, ← mul_assoc,
        mul_comm (((i:ℕ):ZMod (p^2))⁻¹) ((i:ℕ):ZMod (p^2)), ZMod.mul_inv_of_unit _ hu, one_mul]
  rw [Finset.sum_congr rfl key, ← Finset.sum_mul, wolstenholme_H1 hp5, zero_mul]

/-- `b_1` valuation: `p³ ∣ bpoly.coeff 1`. -/
theorem bpoly_coeff1_dvd [Fact p.Prime] (hp5 : 5 ≤ p) : (p:ℤ)^3 ∣ (bpoly p).coeff 1 := by
  rw [bpoly_coeff1_eq]
  obtain ⟨c, hc⟩ := ssum_dvd hp5
  exact ⟨c, by rw [hc]; ring⟩

/-- Central power sum `T_k(n) = Σ_{l<n} (l(l+1))^k`. -/
noncomputable def Tk (k n : ℕ) : ℤ := ∑ l ∈ range n, ((l:ℤ)*((l:ℤ)+1))^k

/-- `Gk(k,b,c) = T_k(b+c) - T_k(b) - T_k(c) = Σ_{l<c} ((Y(b+l))^k - (Y l)^k)`. -/
theorem Gk_shift (k b c : ℕ) :
    Tk k (b+c) - Tk k b - Tk k c
      = ∑ l ∈ range c, ((((b+l:ℕ):ℤ)*(((b+l:ℕ):ℤ)+1))^k - ((l:ℤ)*((l:ℤ)+1))^k) := by
  unfold Tk
  rw [Finset.sum_range_add, Finset.sum_sub_distrib]
  have : ∑ x ∈ range b, ((x:ℤ)*((x:ℤ)+1))^k + ∑ x ∈ range c, (((b+x:ℕ):ℤ)*(((b+x:ℕ):ℤ)+1))^k
      - ∑ l ∈ range b, ((l:ℤ)*((l:ℤ)+1))^k - ∑ l ∈ range c, ((l:ℤ)*((l:ℤ)+1))^k
      = ∑ x ∈ range c, (((b+x:ℕ):ℤ)*(((b+x:ℕ):ℤ)+1))^k - ∑ l ∈ range c, ((l:ℤ)*((l:ℤ)+1))^k := by
    ring
  rw [this, ← Finset.sum_sub_distrib]

/-- `b ∣ Gk`. -/
theorem b_dvd_Gk (k b c : ℕ) : (b:ℤ) ∣ Tk k (b+c) - Tk k b - Tk k c := by
  rw [Gk_shift]
  apply Finset.dvd_sum
  intro l _
  have hd : (b:ℤ) ∣ ((b+l:ℕ):ℤ)*(((b+l:ℕ):ℤ)+1) - (l:ℤ)*((l:ℤ)+1) := by
    have : ((b+l:ℕ):ℤ)*(((b+l:ℕ):ℤ)+1) - (l:ℤ)*((l:ℤ)+1) = (b:ℤ)*((b:ℤ)+2*(l:ℤ)+1) := by
      push_cast; ring
    rw [this]; exact Dvd.dvd.mul_right (dvd_refl _) _
  have := sub_dvd_pow_sub_pow (((b+l:ℕ):ℤ)*(((b+l:ℕ):ℤ)+1)) ((l:ℤ)*((l:ℤ)+1)) k
  exact dvd_trans hd this

/-- `c ∣ Gk` (by `b ↔ c` symmetry). -/
theorem c_dvd_Gk (k b c : ℕ) : (c:ℤ) ∣ Tk k (b+c) - Tk k b - Tk k c := by
  have := b_dvd_Gk k c b
  rw [show c+b = b+c by ring] at this
  have he : Tk k (b+c) - Tk k c - Tk k b = Tk k (b+c) - Tk k b - Tk k c := by ring
  rwa [he] at this

/-- `a = b+c ∣ Gk` (by reflection `Y(b+l) ≡ Y(c-1-l) mod a`). -/
theorem a_dvd_Gk (k b c : ℕ) : ((b+c:ℕ):ℤ) ∣ Tk k (b+c) - Tk k b - Tk k c := by
  rw [Gk_shift, Finset.sum_sub_distrib]
  have hre : ∑ l ∈ range c, (((b+l:ℕ):ℤ)*(((b+l:ℕ):ℤ)+1))^k
      = ∑ l ∈ range c, (((b+(c-1-l):ℕ):ℤ)*(((b+(c-1-l):ℕ):ℤ)+1))^k := by
    apply Finset.sum_nbij' (fun l => c-1-l) (fun l => c-1-l)
    · intro l hl; rw [mem_range] at *; omega
    · intro l hl; rw [mem_range] at *; omega
    · intro l hl; rw [mem_range] at hl; omega
    · intro l hl; rw [mem_range] at hl; omega
    · intro l hl; rw [mem_range] at hl
      have : c-1-(c-1-l) = l := by omega
      rw [this]
  rw [hre, ← Finset.sum_sub_distrib]
  apply Finset.dvd_sum
  intro l hl
  rw [mem_range] at hl
  have hbl : b+(c-1-l) = (b+c) - 1 - l := by omega
  have hd : ((b+c:ℕ):ℤ) ∣ ((b+(c-1-l):ℕ):ℤ)*(((b+(c-1-l):ℕ):ℤ)+1) - (l:ℤ)*((l:ℤ)+1) := by
    rw [hbl]
    set a := b+c with ha
    have h1 : ((a-1-l:ℕ):ℤ) = (a:ℤ)-1-(l:ℤ) := by
      have h2 : (a-1-l:ℕ) = a - (l+1) := by omega
      rw [h2, Nat.cast_sub (by omega)]; push_cast; ring
    have : ((a-1-l:ℕ):ℤ)*(((a-1-l:ℕ):ℤ)+1) - (l:ℤ)*((l:ℤ)+1) = (a:ℤ)*((a:ℤ)-1-2*(l:ℤ)) := by
      rw [h1]; ring
    rw [this]; exact Dvd.dvd.mul_right (dvd_refl _) _
  have := sub_dvd_pow_sub_pow (((b+(c-1-l):ℕ):ℤ)*(((b+(c-1-l):ℕ):ℤ)+1)) ((l:ℤ)*((l:ℤ)+1)) k
  exact dvd_trans hd this

/-- Reindex a sum over `ZMod p` as a sum over `range p`. -/
theorem zmod_sum_range {M : Type*} [AddCommMonoid M] [NeZero p] (f : ZMod p → M) :
    ∑ x : ZMod p, f x = ∑ r ∈ Finset.range p, f (r : ZMod p) := by
  apply Finset.sum_nbij' (i := fun x : ZMod p => x.val) (j := fun r : ℕ => (r : ZMod p))
  · intro a _; simp [Finset.mem_range, ZMod.val_lt]
  · intro b _; exact Finset.mem_univ _
  · intro a _; exact ZMod.natCast_rightInverse a
  · intro b hb; exact ZMod.val_cast_of_lt (Finset.mem_range.mp hb)
  · intro a _; rw [ZMod.natCast_rightInverse a]

/-- Sum of a polynomial of degree `< p-1` over all of `ZMod p` vanishes. -/
theorem sum_eval_eq_zero [Fact p.Prime] (P : Polynomial (ZMod p)) (hP : P.natDegree < p - 1) :
    ∑ x : ZMod p, P.eval x = 0 := by
  have hcard : Fintype.card (ZMod p) = p := ZMod.card p
  simp_rw [Polynomial.eval_eq_sum_range]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro k hk
  rw [mem_range] at hk
  rw [← Finset.mul_sum]
  have hk2 : k < Fintype.card (ZMod p) - 1 := by rw [hcard]; omega
  rw [FiniteField.sum_pow_lt_card_sub_one (K := ZMod p) k hk2, mul_zero]

/-- `∑_{s<p}(2s+1) = p²`. -/
theorem sum_two_s_plus_one (p : ℕ) : ∑ s ∈ range p, (2*s+1) = p^2 := by
  induction p with
  | zero => simp
  | succ n IH => rw [Finset.sum_range_succ, IH]; ring

/-- Wolstenholme-type cancellation via the involution `s ↦ p-1-s`:
    for ALL `j ≥ 1`, `p ∣ ∑_{s<p}(2s+1)·(s(s+1))^j`. -/
theorem sum_two_s_Y_dvd [Fact p.Prime] (hp5 : 5 ≤ p) (j : ℕ) (hj : 1 ≤ j) :
    (p:ℤ) ∣ ∑ s ∈ range p, ((2*(s:ℤ)+1)*((s:ℤ)*((s:ℤ)+1))^j) := by
  have hpp : 0 < p := (Fact.out (p := p.Prime)).pos
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  set f : ℕ → ZMod p := fun s => (2*(s:ZMod p)+1)*((s:ZMod p)*((s:ZMod p)+1))^j with hf
  show (∑ s ∈ range p, f s) = 0
  -- reflection f (p-1-s) = - f s
  have hrefl : ∀ s ∈ range p, f (p-1-s) = - f s := by
    intro s hs
    rw [mem_range] at hs
    have hc : ((p-1-s : ℕ) : ZMod p) = -1 - (s : ZMod p) := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
      push_cast
      rw [ZMod.natCast_self]; ring
    rw [hf]
    simp only
    rw [hc]
    ring
  have hsum : (∑ s ∈ range p, f s) = ∑ s ∈ range p, - f s := by
    calc ∑ s ∈ range p, f s
        = ∑ s ∈ range p, f (p-1-s) := (Finset.sum_range_reflect f p).symm
      _ = ∑ s ∈ range p, - f s := Finset.sum_congr rfl hrefl
  rw [Finset.sum_neg_distrib] at hsum
  -- S = -S ⟹ 2 S = 0 ⟹ S = 0
  have h2 : (2 : ZMod p) * (∑ s ∈ range p, f s) = 0 := by
    linear_combination hsum
  have hu2 : IsUnit (2 : ZMod p) := by
    have hne : (2 : ZMod p) ≠ 0 := by
      rw [show (2 : ZMod p) = ((2:ℕ):ZMod p) by push_cast; ring,
          Ne, ZMod.natCast_eq_zero_iff]
      intro hd; have := Nat.le_of_dvd (by norm_num) hd; omega
    exact isUnit_iff_ne_zero.mpr hne
  exact (hu2.mul_right_eq_zero).mp h2

/-- The central "moment" `I_j = ∑_{s<p}(2s+1)·(s(s+1))^j`. -/
noncomputable def Idef (p j : ℕ) : ℤ := ∑ s ∈ range p, (2*(s:ℤ)+1)*((s:ℤ)*((s:ℤ)+1))^j

/-- `I_0 = p²`. -/
theorem Idef_zero (p : ℕ) : Idef p 0 = (p:ℤ)^2 := by
  unfold Idef
  simp only [pow_zero, mul_one]
  have : ∑ s ∈ range p, (2*(s:ℤ)+1) = ((∑ s ∈ range p, (2*s+1) : ℕ) : ℤ) := by
    push_cast; rfl
  rw [this, sum_two_s_plus_one]; push_cast; ring

/-- `p ∣ I_j` for `j ≥ 1` (the pairing cancellation). -/
theorem Idef_dvd [Fact p.Prime] (hp5 : 5 ≤ p) (j : ℕ) (hj : 1 ≤ j) :
    (p:ℤ) ∣ Idef p j := sum_two_s_Y_dvd hp5 j hj

/-- Key valuation bound for the linear (`d₁`) part of a level-up:
    if `p^M ∣ g₁` and `p^{M+1} ∣ g_k (k≥2)` then `p^{M+2} ∣ ∑_k k·g_k·I_{k-1}`. -/
theorem firstpart_dvd [Fact p.Prime] (hp5 : 5 ≤ p) (g : Polynomial ℤ) (M : ℕ)
    (h1 : (p:ℤ)^M ∣ g.coeff 1) (hk : ∀ k, 2 ≤ k → (p:ℤ)^(M+1) ∣ g.coeff k) :
    (p:ℤ)^(M+2) ∣ ∑ k ∈ range (g.natDegree+1), (k:ℤ) * g.coeff k * Idef p (k-1) := by
  apply Finset.dvd_sum
  intro k hk0
  rcases Nat.lt_or_ge k 2 with hlt | hge
  · interval_cases k
    · simp
    · -- k = 1: term = 1 * g₁ * I_0 = g₁ * p²
      simp only [Nat.cast_one, one_mul, Nat.sub_self, Idef_zero]
      obtain ⟨c, hc⟩ := h1
      exact ⟨c, by rw [hc, pow_add]; ring⟩
  · -- k ≥ 2: p^{M+1} ∣ g_k, p ∣ I_{k-1}
    have hgk := hk k hge
    have hIk : (p:ℤ) ∣ Idef p (k-1) := Idef_dvd hp5 (k-1) (by omega)
    obtain ⟨a, ha⟩ := hgk
    obtain ⟨b, hb⟩ := hIk
    rw [ha, hb]
    rw [show M + 2 = (M+1) + 1 by ring, pow_add, pow_one]
    exact ⟨(k:ℤ) * a * b, by ring⟩

/-- Level-up of an arbitrary base polynomial `f`: `(LevelUp f)(q) = ∏_{s<p} f(pq+s)`. -/
noncomputable def levelUpP (p : ℕ) (f : Polynomial ℤ) : Polynomial ℤ :=
  ∏ s ∈ range p, f.comp (C (p:ℤ) * X + C (s:ℤ))

/-- If `f` is symmetric (`f(-1-X)=f`), so is its level-up. -/
theorem levelUpP_sym (p : ℕ) (f : Polynomial ℤ) (hf : f.comp (-1 - X) = f) :
    (levelUpP p f).comp (-1 - X) = levelUpP p f := by
  unfold levelUpP
  rw [Polynomial.prod_comp]
  have hsymb' : ∀ ψ : Polynomial ℤ, f.comp (-1 - ψ) = f.comp ψ := by
    intro ψ
    have h2 : (-1 - ψ : Polynomial ℤ) = (-1 - X : Polynomial ℤ).comp ψ := by
      simp [Polynomial.sub_comp, Polynomial.X_comp]
    rw [h2, ← Polynomial.comp_assoc, hf]
  have key : ∀ s ∈ range p, (f.comp (C (p:ℤ) * X + C (s:ℤ))).comp (-1 - X)
      = f.comp (-(C (p:ℤ) * X) + C ((s:ℤ) - (p:ℤ))) := by
    intro s _
    rw [Polynomial.comp_assoc]
    congr 1
    rw [Polynomial.add_comp, Polynomial.mul_comp, Polynomial.C_comp, Polynomial.C_comp,
        Polynomial.X_comp, Polynomial.C_sub]
    ring
  rw [Finset.prod_congr rfl key]
  apply Finset.prod_nbij' (fun s => p - 1 - s) (fun s => p - 1 - s)
  · intro s hs; simp only [Finset.mem_range] at *; omega
  · intro s hs; simp only [Finset.mem_range] at *; omega
  · intro s hs; simp only [Finset.mem_range] at hs; omega
  · intro s hs; simp only [Finset.mem_range] at hs; omega
  · intro s hs
    simp only [Finset.mem_range] at hs
    rw [← hsymb' (C (p:ℤ) * X + C ((p-1-s:ℕ):ℤ))]
    congr 1
    have hcast : ((p - 1 - s : ℕ) : ℤ) = (p:ℤ) - 1 - (s:ℤ) := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
    rw [hcast]
    simp only [Polynomial.C_sub, Polynomial.C_1]
    ring

/-- The level-up block polynomial `BLOCK(q) = ∏_{s<p} block(pq+s)`, as a polynomial in `q`. -/
noncomputable def blockUp (p : ℕ) : Polynomial ℤ :=
  ∏ s ∈ range p, (bpoly p).comp (C (p:ℤ) * X + C (s:ℤ))

/-- The level-up block is symmetric under `q ↦ -1-q`, hence a polynomial in `Y = q(q+1)`. -/
theorem blockUp_sym (p : ℕ) (hodd : Odd p) (hp : 5 ≤ p) :
    (blockUp p).comp (-1 - X) = blockUp p := by
  unfold blockUp
  rw [Polynomial.prod_comp]
  -- rewrite each factor's composition
  have hsymb : (bpoly p).comp (-1 - X) = bpoly p := bpoly_sym p hodd hp
  have hsymb' : ∀ ψ : Polynomial ℤ, (bpoly p).comp (-1 - ψ) = (bpoly p).comp ψ := by
    intro ψ
    have h2 : (-1 - ψ : Polynomial ℤ) = (-1 - X : Polynomial ℤ).comp ψ := by
      simp [Polynomial.sub_comp, Polynomial.X_comp]
    rw [h2, ← Polynomial.comp_assoc, hsymb]
  have key : ∀ s ∈ range p, ((bpoly p).comp (C (p:ℤ) * X + C (s:ℤ))).comp (-1 - X)
      = (bpoly p).comp (-(C (p:ℤ) * X) + C ((s:ℤ) - (p:ℤ))) := by
    intro s _
    rw [Polynomial.comp_assoc]
    congr 1
    rw [Polynomial.add_comp, Polynomial.mul_comp, Polynomial.C_comp, Polynomial.C_comp,
        Polynomial.X_comp, Polynomial.C_sub]
    ring
  rw [Finset.prod_congr rfl key]
  -- reindex s ↦ p-1-s
  apply Finset.prod_nbij' (fun s => p - 1 - s) (fun s => p - 1 - s)
  · intro s hs; simp only [Finset.mem_range] at *; omega
  · intro s hs; simp only [Finset.mem_range] at *; omega
  · intro s hs; simp only [Finset.mem_range] at hs; omega
  · intro s hs; simp only [Finset.mem_range] at hs; omega
  · intro s hs
    simp only [Finset.mem_range] at hs
    -- LHSfun(s) = RHSfun(p-1-s)
    rw [← hsymb' (C (p:ℤ) * X + C ((p-1-s:ℕ):ℤ))]
    congr 1
    have hcast : ((p - 1 - s : ℕ) : ℤ) = (p:ℤ) - 1 - (s:ℤ) := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
    rw [hcast]
    simp only [Polynomial.C_sub, Polynomial.C_1]
    ring

/-- Hence the level-up block is representable as a polynomial in `Ysub = X²+X`. -/
theorem blockUp_rep (p : ℕ) (hodd : Odd p) (hp : 5 ≤ p) :
    ∃ h : Polynomial ℤ, blockUp p = h.comp Ysub :=
  sym_rep (blockUp p) (blockUp_sym p hodd hp)

end Kaz
