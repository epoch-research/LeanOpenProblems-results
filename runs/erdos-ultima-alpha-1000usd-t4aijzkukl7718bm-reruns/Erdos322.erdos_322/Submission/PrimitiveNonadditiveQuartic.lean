import Submission.Spec

/-! An elementary recurrence producing distinct nonadditive rational points on
`a^4 + b^4 + c^4 = 10082`. This does not establish a positive-power count bound. -/

namespace Erdos322Research.PrimitiveNonadditive

private def F {R : Type*} [CommRing R] (s t : R) : R :=
  3468*s^8 - 612*s^4*t^4 - 140*s^2*t^6 - 9*t^8
private def G {R : Type*} [CommRing R] (s t : R) : R :=
  10404*s^8 + 4760*s^6*t^2 + 612*s^4*t^4 - 3*t^8
private def H {R : Type*} [CommRing R] (s t : R) : R :=
  3468*s^8 + 2312*s^6*t^2 + 612*s^4*t^4 + 72*s^2*t^6 + 3*t^8
private def J {R : Type*} [CommRing R] (s t : R) : R :=
  3468*s^8 + 2448*s^6*t^2 + 612*s^4*t^4 + 68*s^2*t^6 + 3*t^8
private def K {R : Type*} [CommRing R] (s t : R) : R :=
  F s t ^ 4 + 4*t^4*(102*s^4+35*s^2*t^2+3*t^4)*
    (F s t - G s t)*(F s t ^ 2 + G s t ^ 2)

private theorem first_quadric {R : Type*} [CommRing R] (s t : R) :
    (6*s^2+t^2)*H s t ^ 2 = 6*(s*F s t)^2+(t*G s t)^2 := by
  simp only [F, G, H]
  ring

private theorem second_quadric {R : Type*} [CommRing R] (s t : R) :
    (1207*s^2+213*t^2)*J s t ^ 2 = 1207*(s*F s t)^2+213*(t*G s t)^2 := by
  simp only [F, G, J]
  ring

private theorem defect_step {R : Type*} [CommRing R] (s t : R) :
    34*(s*F s t)^4-(t*G s t)^4 = (34*s^4-t^4)*K s t := by
  simp only [F, G, K]
  ring

private theorem mod_three : ∀ s t : ZMod 3, s ≠ 0 → t ≠ 0 →
    F s t = 1 ∧ G s t = 2 ∧ H s t = 2 ∧ J s t = 2 := by
  decide

private theorem mod_nine : ∀ s t : ZMod 9,
    s^2 ≠ 0 → t^2 ≠ 0 → K s t = 6 := by
  decide

structure QuadPoint where
  s : ℤ
  t : ℤ
  z : ℤ
  w : ℤ

def next (P : QuadPoint) : QuadPoint :=
  ⟨P.s * F P.s P.t, P.t * G P.s P.t, P.z * H P.s P.t, P.w * J P.s P.t⟩

def point : ℕ → QuadPoint
  | 0 => ⟨2, 1, 5, 71⟩
  | n+1 => next (point n)

private theorem next_preserves (P : QuadPoint)
    (h₁ : P.z^2 = 6*P.s^2+P.t^2)
    (h₂ : P.w^2 = 1207*P.s^2+213*P.t^2) :
    (next P).z^2 = 6*(next P).s^2+(next P).t^2 ∧
    (next P).w^2 = 1207*(next P).s^2+213*(next P).t^2 := by
  constructor
  · change (P.z * H P.s P.t)^2 = _
    rw [mul_pow, h₁, first_quadric]
    rfl
  · change (P.w * J P.s P.t)^2 = _
    rw [mul_pow, h₂, second_quadric]
    rfl

theorem point_on_quadrics (n : ℕ) :
    (point n).z^2 = 6*(point n).s^2+(point n).t^2 ∧
    (point n).w^2 = 1207*(point n).s^2+213*(point n).t^2 := by
  induction n with
  | zero => norm_num [point]
  | succ n ih => exact next_preserves _ ih.1 ih.2

private theorem point_units_three (n : ℕ) :
    ((point n).s : ZMod 3) ≠ 0 ∧ ((point n).t : ZMod 3) ≠ 0 ∧
    ((point n).w : ZMod 3) ≠ 0 := by
  induction n with
  | zero => norm_num [point]; decide
  | succ n ih =>
    obtain ⟨hF, hG, hH, hJ⟩ := mod_three _ _ ih.1 ih.2.1
    have hf : ((F (point n).s (point n).t : ℤ) : ZMod 3) = 1 := by
      simpa [F] using hF
    have hg : ((G (point n).s (point n).t : ℤ) : ZMod 3) = 2 := by
      simpa [G] using hG
    have hj : ((J (point n).s (point n).t : ℤ) : ZMod 3) = 2 := by
      simpa [J] using hJ
    simpa only [point, next, Int.cast_mul, hf, hg, hj, mul_one, ne_eq,
      mul_eq_zero, not_or] using
      And.intro ih.1 (And.intro (And.intro ih.2.1 (by decide : (2 : ZMod 3) ≠ 0))
        (And.intro ih.2.2 (by decide : (2 : ZMod 3) ≠ 0)))

private theorem square_mod_nine_ne_zero (a : ℤ) (h : (a : ZMod 3) ≠ 0) :
    (a : ZMod 9)^2 ≠ 0 := by
  intro he
  have hd : (9 : ℤ) ∣ a^2 := by
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (by simpa using he)
  have hd3 : (3 : ℤ) ∣ a^2 := dvd_trans (by norm_num) hd
  have ha : (3 : ℤ) ∣ a := Int.prime_three.dvd_of_dvd_pow hd3
  exact h ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr ha)

private theorem factor_mod_nine (n : ℕ) :
    ((K (point n).s (point n).t : ℤ) : ZMod 9) = 6 := by
  have h := mod_nine ((point n).s : ZMod 9) ((point n).t : ZMod 9)
    (square_mod_nine_ne_zero _ (point_units_three n).1)
    (square_mod_nine_ne_zero _ (point_units_three n).2.1)
  simpa [K, F, G] using h

private theorem factor_valuation (n : ℕ) :
    K (point n).s (point n).t ≠ 0 ∧ padicValInt 3 (K (point n).s (point n).t) = 1 := by
  let k : ℤ := K (point n).s (point n).t
  have hk : (k : ZMod 9) = 6 := factor_mod_nine n
  have hn : k ≠ 0 := by
    intro h
    rw [h, Int.cast_zero] at hk
    exact (by decide : (0 : ZMod 9) ≠ 6) hk
  have hd : (9 : ℤ) ∣ k-6 := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    simpa using sub_eq_zero.mpr hk
  have hd3 : (3 : ℤ) ∣ k := by
    have : (3 : ℤ) ∣ k-6 := dvd_trans (by norm_num) hd
    omega
  have hn9 : ¬(9 : ℤ) ∣ k := by
    intro h
    have hz : (k : ZMod 9) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h
    rw [hz] at hk
    exact (by decide : (0 : ZMod 9) ≠ 6) hk
  have hlo : 1 ≤ padicValInt 3 k := by
    have h := (padicValInt_dvd_iff (p := 3) 1 k).mp (by simpa using hd3)
    exact h.resolve_left hn
  have hhi : ¬ 2 ≤ padicValInt 3 k := by
    intro h
    apply hn9
    simpa using (padicValInt_dvd_iff (p := 3) 2 k).mpr (Or.inr h)
  refine ⟨hn, ?_⟩
  change padicValInt 3 k = 1
  omega

def defect (n : ℕ) : ℤ := 34*(point n).s^4-(point n).t^4

theorem defect_valuation (n : ℕ) : defect n ≠ 0 ∧ padicValInt 3 (defect n) = n+1 := by
  induction n with
  | zero =>
    constructor
    · decide
    · change padicValNat 3 (3*181) = 1
      rw [padicValNat.mul (by decide) (by decide), padicValNat.self (by decide),
        padicValNat.eq_zero_of_not_dvd (by decide : ¬3 ∣ 181)]
  | succ n ih =>
    have he : defect (n+1) = defect n * K (point n).s (point n).t := by
      exact defect_step _ _
    obtain ⟨hk, hv⟩ := factor_valuation n
    rw [he]
    exact ⟨mul_ne_zero ih.1 hk, by rw [padicValInt.mul ih.1 hk, ih.2, hv]⟩

private theorem point_t_ne_zero (n : ℕ) : (point n).t ≠ 0 := by
  intro h
  exact (point_units_three n).2.1 (by simp [h])

private theorem point_w_ne_zero (n : ℕ) : (point n).w ≠ 0 := by
  intro h
  exact (point_units_three n).2.2 (by simp [h])

private theorem point_t_valuation (n : ℕ) : padicValInt 3 (point n).t = 0 := by
  apply padicValInt.eq_zero_of_not_dvd
  intro h
  exact (point_units_three n).2.1 ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h)

def ratio (n : ℕ) : ℚ := ((point n).s : ℚ)^2 / ((point n).t : ℚ)^2

theorem ratio_valuation (n : ℕ) : padicValRat 3 (34*ratio n ^ 2 - 1) = n+1 := by
  have ht : ((point n).t : ℚ) ≠ 0 := by exact_mod_cast point_t_ne_zero n
  have hd : ((defect n : ℤ) : ℚ) ≠ 0 := by exact_mod_cast (defect_valuation n).1
  have he : 34*ratio n ^ 2 - 1 = (defect n : ℚ) / ((point n).t : ℚ)^4 := by
    simp only [ratio, defect, Int.cast_sub, Int.cast_mul, Int.cast_pow, Int.cast_ofNat]
    field_simp
  rw [he, padicValRat.div hd (pow_ne_zero 4 ht), padicValRat.pow ht]
  rw [padicValRat.of_int, padicValRat.of_int, (defect_valuation n).2,
    point_t_valuation]
  simp

theorem ratio_injective : Function.Injective ratio := by
  intro m n h
  have hv := congrArg (fun x : ℚ ↦ padicValRat 3 (34*x^2-1)) h
  dsimp only at hv
  rw [ratio_valuation, ratio_valuation] at hv
  exact_mod_cast (by omega : (m : ℤ) = n)

def rationalTriple (n : ℕ) : Fin 3 → ℚ :=
  ![71*((point n).s+(point n).t)/(point n).w,
    71*((point n).s-(point n).t)/(point n).w,
    142*(point n).z/(point n).w]

theorem rationalTriple_sum (n : ℕ) : ∑ i, rationalTriple n i ^ 4 = 10082 := by
  have hw : ((point n).w : ℚ) ≠ 0 := by exact_mod_cast point_w_ne_zero n
  have h₁ : ((point n).z : ℚ)^2 = 6*((point n).s : ℚ)^2+((point n).t : ℚ)^2 := by
    exact_mod_cast (point_on_quadrics n).1
  have h₂ : ((point n).w : ℚ)^2 = 1207*((point n).s : ℚ)^2+213*((point n).t : ℚ)^2 := by
    exact_mod_cast (point_on_quadrics n).2
  simp only [rationalTriple, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  field_simp
  linear_combination (142 : ℚ)^4 * congrArg (fun x : ℚ ↦ x^2) h₁ -
    10082 * congrArg (fun x : ℚ ↦ x^2) h₂

private theorem ratio_recovery (n : ℕ) : ratio n =
    (rationalTriple n 2 ^ 2 - 2*(rationalTriple n 0 ^ 2 + rationalTriple n 1 ^ 2)) /
    (12*(rationalTriple n 0 ^ 2 + rationalTriple n 1 ^ 2)-rationalTriple n 2 ^ 2) := by
  have ht : ((point n).t : ℚ) ≠ 0 := by exact_mod_cast point_t_ne_zero n
  have hw : ((point n).w : ℚ) ≠ 0 := by exact_mod_cast point_w_ne_zero n
  have h₁ : ((point n).z : ℚ)^2 = 6*((point n).s : ℚ)^2+((point n).t : ℚ)^2 := by
    exact_mod_cast (point_on_quadrics n).1
  have hd : 12*(rationalTriple n 0 ^ 2 + rationalTriple n 1 ^ 2)-rationalTriple n 2 ^ 2 =
      100820 * ((point n).t : ℚ)^2 / ((point n).w : ℚ)^2 := by
    simp only [rationalTriple, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    field_simp
    linear_combination -20164 * h₁
  rw [hd]
  simp only [ratio, rationalTriple, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  field_simp
  linear_combination -20164 * h₁

theorem squared_triple_injective : Function.Injective
    (fun n : ℕ ↦ fun i : Fin 3 ↦ rationalTriple n i ^ 2) := by
  intro m n h
  apply ratio_injective
  have hi : ∀ i, rationalTriple m i ^ 2 = rationalTriple n i ^ 2 := fun i ↦ congrFun h i
  rw [ratio_recovery, ratio_recovery, hi 0, hi 1, hi 2]

def integerTriple (n : ℕ) : Fin 3 → ℤ :=
  ![71*((point n).s+(point n).t), 71*((point n).s-(point n).t), 142*(point n).z]

private theorem rationalTriple_eq (n : ℕ) (i : Fin 3) :
    rationalTriple n i = (integerTriple n i : ℚ) / (point n).w := by
  fin_cases i <;> simp [rationalTriple, integerTriple]

theorem integerTriple_sum (n : ℕ) :
    ∑ i, integerTriple n i ^ 4 = 10082 * (point n).w^4 := by
  have h := rationalTriple_sum n
  simp only [rationalTriple_eq, div_pow, ← Finset.sum_div] at h
  have hw : ((point n).w : ℚ) ≠ 0 := by exact_mod_cast point_w_ne_zero n
  have he := (div_eq_iff (pow_ne_zero 4 hw)).mp h
  exact_mod_cast he

private theorem norm_three_obstruction (a b w : ℤ) (hw : (w : ZMod 3) ≠ 0) :
    a^2+a*b+b^2 ≠ 71*w^2 := by
  intro he
  have hc : (a : ZMod 3)^2+(a : ZMod 3)*b+b^2 = 71*(w : ZMod 3)^2 := by
    simpa using congrArg (Int.castRingHom (ZMod 3)) he
  have hw2 : (w : ZMod 3)^2 = 1 := by
    have h : ∀ x : ZMod 3, x ≠ 0 → x^2 = 1 := by decide
    exact h _ hw
  rw [hw2] at hc
  norm_num at hc
  have h : ∀ x y : ZMod 3, x^2+x*y+y^2 ≠ 71 := by decide
  exact h _ _ hc

private theorem not_additive_of_sum (a b c w : ℤ)
    (hs : a^4+b^4+c^4 = 10082*w^4) (hw : (w : ZMod 3) ≠ 0) : c ≠ a+b := by
  intro he
  rw [he] at hs
  have hi : a^4+b^4+(a+b)^4 = 2*(a^2+a*b+b^2)^2 := by ring
  rw [hi] at hs
  have hsq : (a^2+a*b+b^2)^2 = (71*w^2)^2 := by nlinarith [hs]
  have hp : 0 ≤ a^2+a*b+b^2 := by nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg (a+b)]
  exact norm_three_obstruction a b w hw ((sq_eq_sq₀ hp (by positivity)).mp hsq)

theorem integerTriple_abs_nonadditive (n : ℕ) (σ : Equiv.Perm (Fin 3)) :
    |integerTriple n (σ 2)| ≠ |integerTriple n (σ 0)| + |integerTriple n (σ 1)| := by
  have hs : ∑ i, |integerTriple n (σ i)| ^ 4 = 10082 * (point n).w^4 := by
    simpa only [Even.pow_abs (by decide : Even 4)] using
      (Equiv.sum_comp σ (fun i ↦ integerTriple n i ^ 4)).trans (integerTriple_sum n)
  simp only [Fin.sum_univ_three] at hs
  exact not_additive_of_sum _ _ _ _ hs (point_units_three n).2.2

private def natTriple (n : ℕ) (i : Fin 3) : ℕ := (integerTriple n i).natAbs

private theorem natTriple_sum (n : ℕ) :
    ∑ i, natTriple n i ^ 4 = 10082 * (point n).w.natAbs^4 := by
  have hi := integerTriple_sum n
  have h : ∑ i, (natTriple n i : ℤ)^4 = 10082 * ((point n).w.natAbs : ℤ)^4 := by
    simpa only [natTriple, Int.natCast_natAbs, Even.pow_abs (by decide : Even 4)] using hi
  exact_mod_cast h

private theorem natTriple_nonadditive (n : ℕ) (i j k : Fin 3)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    natTriple n k ≠ natTriple n i + natTriple n j := by
  have h₀ := integerTriple_abs_nonadditive n (Equiv.refl _)
  have h₁ := integerTriple_abs_nonadditive n (Equiv.swap 1 2)
  have h₂ := integerTriple_abs_nonadditive n (Equiv.swap 0 2)
  simp only [Equiv.refl_apply] at h₀
  simp [Equiv.swap_apply_def, Fin.ext_iff] at h₁ h₂
  have hh₀ : natTriple n 2 ≠ natTriple n 0 + natTriple n 1 := by
    have h : (natTriple n 2 : ℤ) ≠ (natTriple n 0 : ℤ) + natTriple n 1 := by
      simpa only [natTriple, Int.natCast_natAbs] using h₀
    exact_mod_cast h
  have hh₁ : natTriple n 1 ≠ natTriple n 0 + natTriple n 2 := by
    have h : (natTriple n 1 : ℤ) ≠ (natTriple n 0 : ℤ) + natTriple n 2 := by
      simpa only [natTriple, Int.natCast_natAbs] using h₁
    exact_mod_cast h
  have hh₂ : natTriple n 0 ≠ natTriple n 2 + natTriple n 1 := by
    have h : (natTriple n 0 : ℤ) ≠ (natTriple n 2 : ℤ) + natTriple n 1 := by
      simpa only [natTriple, Int.natCast_natAbs] using h₂
    exact_mod_cast h
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all <;> omega

def commonDenominator (m : ℕ) : ℕ := ∏ i : Fin (m+1), (point i).w.natAbs

private theorem commonDenominator_pos (m : ℕ) : 0 < commonDenominator m := by
  apply Finset.prod_pos
  intro i _
  exact Int.natAbs_pos.mpr (point_w_ne_zero i)

private theorem point_denominator_dvd (m : ℕ) (i : Fin (m+1)) :
    (point i).w.natAbs ∣ commonDenominator m :=
  Finset.dvd_prod_of_mem _ (Finset.mem_univ i)

private def scale (m : ℕ) (i : Fin (m+1)) : ℕ := commonDenominator m / (point i).w.natAbs

private theorem scale_mul (m : ℕ) (i : Fin (m+1)) :
    (point i).w.natAbs * scale m i = commonDenominator m :=
  Nat.mul_div_cancel' (point_denominator_dvd m i)

private theorem scale_pos (m : ℕ) (i : Fin (m+1)) : 0 < scale m i :=
  Nat.div_pos (Nat.le_of_dvd (commonDenominator_pos m) (point_denominator_dvd m i))
    (Int.natAbs_pos.mpr (point_w_ne_zero i))

private def tuple (m : ℕ) (i : Fin (m+1)) : Fin 4 → ℕ :=
  Fin.snoc (fun j : Fin 3 ↦ 2 * natTriple i j * scale m i) 1

def representedNumber (m : ℕ) : ℕ := 10082 * (2*commonDenominator m)^4+1

private theorem tuple_sum (m : ℕ) (i : Fin (m+1)) :
    ∑ j, tuple m i j ^ 4 = representedNumber m := by
  rw [Fin.sum_univ_castSucc]
  simp only [tuple, Fin.snoc_castSucc, Fin.snoc_last, one_pow]
  simp_rw [mul_pow]
  rw [← Finset.sum_mul, ← Finset.mul_sum, natTriple_sum]
  dsimp [representedNumber]
  have h := scale_mul m i
  calc
    2^4 * (10082 * (point i).w.natAbs^4) * scale m i ^ 4 + 1 =
        10082 * (2*((point i).w.natAbs * scale m i))^4+1 := by ring
    _ = _ := by rw [h]

private theorem tuple_gcd (m : ℕ) (i : Fin (m+1)) :
    Finset.univ.gcd (tuple m i) = 1 := by
  apply Nat.dvd_one.mp
  have h := Finset.gcd_dvd (f := tuple m i) (Finset.mem_univ (Fin.last 3))
  simpa only [tuple, Fin.snoc_last] using h

private theorem tuple_abs_ratio (m : ℕ) (i : Fin (m+1)) (j : Fin 3) :
    ((tuple m i j.castSucc : ℕ) : ℚ) / (2*commonDenominator m) = |rationalTriple i j| := by
  have hd : ((point i).w.natAbs : ℚ) ≠ 0 := by
    exact_mod_cast (Int.natAbs_pos.mpr (point_w_ne_zero i)).ne'
  have hl : (commonDenominator m : ℚ) ≠ 0 := by
    exact_mod_cast (commonDenominator_pos m).ne'
  have hs : ((point i).w.natAbs : ℚ) * (scale m i : ℚ) = commonDenominator m := by
    exact_mod_cast scale_mul m i
  rw [rationalTriple_eq, abs_div]
  simp only [tuple, Fin.snoc_castSucc, natTriple, Nat.cast_mul, Nat.cast_ofNat,
    Nat.cast_natAbs, Int.cast_abs]
  rw [show |((point i).w : ℚ)| = ((point i).w.natAbs : ℚ) by
    simp only [Nat.cast_natAbs, Int.cast_abs]]
  field_simp
  linear_combination |(integerTriple i j : ℚ)| * hs

private theorem tuple_injective (m : ℕ) : Function.Injective (tuple m) := by
  intro i j he
  apply Fin.ext
  apply squared_triple_injective
  funext k
  have h := congrArg (fun f : Fin 4 → ℕ ↦ ((f k.castSucc : ℕ) : ℚ) /
    (2*commonDenominator m)) he
  change ((tuple m i k.castSucc : ℕ) : ℚ) / (2*commonDenominator m) =
    ((tuple m j k.castSucc : ℕ) : ℚ) / (2*commonDenominator m) at h
  rw [tuple_abs_ratio, tuple_abs_ratio] at h
  have h2 := congrArg (fun x : ℚ ↦ x^2) h
  dsimp only at h2
  simpa only [sq_abs] using h2

private theorem tuple_nonadditive_indices (m : ℕ) (n : Fin (m+1)) (i j k : Fin 4)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    tuple m n k ≠ tuple m n i + tuple m n j := by
  rcases Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | rfl <;>
    rcases Fin.eq_castSucc_or_eq_last j with ⟨j, rfl⟩ | rfl <;>
    rcases Fin.eq_castSucc_or_eq_last k with ⟨k, rfl⟩ | rfl
  all_goals simp only [tuple, Fin.snoc_castSucc, Fin.snoc_last] at *
  · intro he
    apply natTriple_nonadditive n i j k
      (fun h ↦ hij (congrArg Fin.castSucc h)) (fun h ↦ hik (congrArg Fin.castSucc h))
      (fun h ↦ hjk (congrArg Fin.castSucc h))
    apply Nat.mul_left_cancel (n := 2*scale m n) (by have := scale_pos m n; positivity)
    nlinarith [he]
  all_goals try simp only [mul_assoc] at *
  all_goals omega

private def boundedTuple (m : ℕ) (n : Fin (m+1)) : Fin 4 → Fin (representedNumber m+1) :=
  fun i ↦ ⟨tuple m n i, by
    have hs := tuple_sum m n
    have hi : tuple m n i ^ 4 ≤ ∑ j, tuple m n j ^ 4 :=
      Finset.single_le_sum (f := fun j ↦ tuple m n j ^ 4)
        (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)
    have hp := Nat.le_pow (a := tuple m n i) (by decide : 0 < 4)
    omega⟩

private theorem boundedTuple_injective (m : ℕ) : Function.Injective (boundedTuple m) := by
  intro i j he
  apply tuple_injective m
  funext k
  exact congrArg (fun f ↦ ((f k : Fin (representedNumber m+1)) : ℕ)) he

private theorem boundedTuple_nonadditive (m : ℕ) (n : Fin (m+1)) :
    ¬ Erdos322.QuarticAdditive.HasAdditiveTriple (boundedTuple m n) := by
  rintro ⟨σ, he⟩
  exact tuple_nonadditive_indices m n (σ 0) (σ 1) (σ 2)
    (σ.injective.ne (by decide)) (σ.injective.ne (by decide)) (σ.injective.ne (by decide)) he

/-- The part of the quartic count that is both primitive and outside every additive-triple locus. -/
def primitiveNonadditiveCount (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun a : Fin 4 → Fin (n+1) ↦
    (∑ i, (a i : ℕ)^4 = n) ∧ Finset.univ.gcd (fun i ↦ (a i : ℕ)) = 1 ∧
      ¬ Erdos322.QuarticAdditive.HasAdditiveTriple a)).card

theorem primitive_nonadditive_count_lower (m : ℕ) :
    m+1 ≤ primitiveNonadditiveCount (representedNumber m) := by
  classical
  unfold primitiveNonadditiveCount
  have hc := Finset.card_le_card_of_injOn (boundedTuple m) (s := Finset.univ)
    (t := Finset.univ.filter (fun a : Fin 4 → Fin (representedNumber m+1) ↦
      (∑ i, (a i : ℕ)^4 = representedNumber m) ∧
        Finset.univ.gcd (fun i ↦ (a i : ℕ)) = 1 ∧
        ¬ Erdos322.QuarticAdditive.HasAdditiveTriple a))
    (by
      intro i _
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨tuple_sum m i, tuple_gcd m i, boundedTuple_nonadditive m i⟩)
    (boundedTuple_injective m).injOn
  simpa using hc

theorem primitive_nonadditive_counts_exceed_any_bound (M : ℕ) :
    {n : ℕ | M < primitiveNonadditiveCount n}.Infinite := by
  intro hf
  let C := hf.toFinset.sup primitiveNonadditiveCount
  let m := M+C
  have hc := primitive_nonadditive_count_lower m
  have hm : M < primitiveNonadditiveCount (representedNumber m) := by omega
  have hn : representedNumber m ∈ hf.toFinset := hf.mem_toFinset.mpr hm
  have hu : primitiveNonadditiveCount (representedNumber m) ≤ C := Finset.le_sup hn
  omega

theorem primitiveNonadditiveCount_le_primitive (n : ℕ) :
    primitiveNonadditiveCount n ≤ Erdos322.primitiveRepresentationCount 4 n := by
  apply Finset.card_le_card
  intro a ha
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
  exact ⟨ha.1, ha.2.1⟩

theorem primitiveNonadditiveCount_le_nonadditive (n : ℕ) :
    primitiveNonadditiveCount n ≤ Erdos322.QuarticAdditive.nonadditiveQuarticCount n := by
  apply Finset.card_le_card
  intro a ha
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
  exact ⟨ha.1, ha.2.2⟩

end Erdos322Research.PrimitiveNonadditive
