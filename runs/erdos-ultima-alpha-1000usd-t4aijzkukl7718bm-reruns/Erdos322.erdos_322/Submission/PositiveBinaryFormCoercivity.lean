import Submission.RationalCurveDenominatorBound

/-! Automatic coercivity for monic binary denominators without real poles,
and its application to fixed rational families of quartic representations.
This is not a bound for unrestricted representations. -/
namespace Erdos322Research.PositiveBinaryFormCoercivity

open Polynomial Finset PositiveBinaryFormBound RationalCurveDenominatorBound
set_option Elab.async false

noncomputable def realValue (f : ℤ[X]) (x y : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (f.natDegree+1), (f.coeff j : ℝ)*x^j*y^(f.natDegree-j)

lemma realValue_nat (f : ℤ[X]) (a b : ℕ) :
    realValue f (a : ℝ) (b : ℝ) = (binaryValue f a b : ℝ) := by
  simp only [realValue, binaryValue, Int.cast_sum, Int.cast_mul, Int.cast_pow,
    Int.cast_natCast]

lemma realValue_smul (f : ℤ[X]) (s x y : ℝ) :
    realValue f (s*x) (s*y) = s^f.natDegree*realValue f x y := by
  unfold realValue
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjd : j ≤ f.natDegree := by simpa using Finset.mem_range.mp hj
  have hp : s^j*s^(f.natDegree-j)=s^f.natDegree := by
    rw [← pow_add, Nat.add_sub_of_le hjd]
  rw [mul_pow, mul_pow]
  calc
    (f.coeff j : ℝ)*(s^j*x^j)*(s^(f.natDegree-j)*y^(f.natDegree-j)) =
        (s^j*s^(f.natDegree-j))*((f.coeff j : ℝ)*x^j*y^(f.natDegree-j)) := by ring
    _ = _ := by rw [hp]

lemma realValue_ratio (f : ℤ[X]) (r x y : ℝ) (hr : r*y=x) :
    realValue f x y = y^f.natDegree*f.eval₂ (Int.castRingHom ℝ) r := by
  rw [Polynomial.eval₂_eq_sum_range' _ (Nat.lt_succ_self f.natDegree)]
  unfold realValue
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjd : j ≤ f.natDegree := by simpa using Finset.mem_range.mp hj
  have hp : y^j*y^(f.natDegree-j)=y^f.natDegree := by
    rw [← pow_add, Nat.add_sub_of_le hjd]
  rw [← hr, mul_pow]
  calc
    (f.coeff j : ℝ)*(r^j*y^j)*y^(f.natDegree-j) =
        (y^j*y^(f.natDegree-j))*((f.coeff j : ℝ)*r^j) := by ring
    _ = _ := by rw [hp]; rfl

lemma realValue_one_zero (f : ℤ[X]) (hf : f.Monic) : realValue f 1 0=1 := by
  classical
  unfold realValue
  rw [Finset.sum_eq_single f.natDegree]
  · simp [hf.coeff_natDegree]
  · intro j hj hne
    have hjd : j < f.natDegree := by
      have := Finset.mem_range.mp hj
      omega
    simp [Nat.ne_of_gt (Nat.sub_pos_of_lt hjd)]
  · simp

/-- A reduced quartic rational norm identity has no finite real denominator
zero. Positivity of fourth powers and the numerator Bezout certificate suffice. -/
theorem denominator_no_real_zero {ι : Type*} [Fintype ι]
    (f B : ℤ[X]) (g A : ι → ℤ[X]) (C : ℕ) (N : ℤ) (hC : 0 < C)
    (hnorm : ∑ i, g i^4=Polynomial.C N*f^4)
    (hbez : (∑ i, A i*g i)+B*f=Polynomial.C (C : ℤ)) :
    ∀ t : ℝ, f.eval₂ (Int.castRingHom ℝ) t ≠ 0 := by
  intro t ht
  have hh := congrArg (Polynomial.eval₂ (Int.castRingHom ℝ) t) hnorm
  simp only [eval₂_finset_sum, eval₂_pow, eval₂_mul, eval₂_C, ht,
    zero_pow (by decide : 4 ≠ 0), mul_zero] at hh
  have hg (i : ι) : (g i).eval₂ (Int.castRingHom ℝ) t=0 := by
    apply (pow_eq_zero_iff (by decide : 4 ≠ 0)).mp
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => by positivity)).mp hh i (Finset.mem_univ i)
  have hb := congrArg (Polynomial.eval₂ (Int.castRingHom ℝ) t) hbez
  simp only [eval₂_add, eval₂_finset_sum, eval₂_mul, eval₂_C, ht, hg,
    mul_zero, Finset.sum_const_zero, add_zero] at hb
  have hp : (0 : ℝ) < C := by exact_mod_cast hC
  have hz : (0 : ℝ) = C := by simpa using hb
  linarith

/-- Compactness supplies a fixed coercivity constant for the homogenization.
The absolute value permits stating this without a separate sign theorem. -/
theorem exists_coercivity (f : ℤ[X]) (hf : f.Monic) (hd : 0 < f.natDegree)
    (hnoroot : ∀ t : ℝ, f.eval₂ (Int.castRingHom ℝ) t ≠ 0) :
    ∃ H : ℕ, 0 < H ∧ ∀ a b : ℕ,
      (a+b)^f.natDegree ≤ H*(binaryValue f a b).natAbs := by
  let φ : ℝ → ℝ := fun t => realValue f t (1-t)
  have hφ : Continuous φ := by
    dsimp [φ, realValue]
    fun_prop
  have hne (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : φ t ≠ 0 := by
    by_cases he : t=1
    · subst t
      simpa [φ] using (show realValue f 1 0 ≠ 0 by rw [realValue_one_zero f hf]; norm_num)
    · have hy : 1-t ≠ 0 := sub_ne_zero.mpr (fun hh => he hh.symm)
      have hh := realValue_ratio f (t/(1-t)) t (1-t) (div_mul_cancel₀ t hy)
      change realValue f t (1-t) ≠ 0
      rw [hh]
      exact mul_ne_zero (pow_ne_zero _ hy) (hnoroot _)
  obtain ⟨t₀,ht₀,hmin⟩ := isCompact_Icc.exists_isMinOn
    (show (Set.Icc (0 : ℝ) 1).Nonempty from ⟨0,by norm_num⟩) hφ.abs.continuousOn
  let μ : ℝ := |φ t₀|
  have hμ : 0 < μ := abs_pos.mpr (hne t₀ ht₀)
  obtain ⟨H,hH⟩ := exists_nat_gt (1/μ)
  have hHp : 0 < H := by
    have hh : (0 : ℝ) < H := (div_pos (by norm_num) hμ).trans hH
    exact_mod_cast hh
  have hHμ : 1 ≤ (H : ℝ)*μ := (div_le_iff₀ hμ).mp hH.le
  refine ⟨H,hHp,?_⟩
  intro a b
  by_cases hs : a+b=0
  · simp only [hs, zero_pow hd.ne']
    exact Nat.zero_le _
  have hsp : (0 : ℝ) < (a : ℝ)+b := by exact_mod_cast (Nat.pos_of_ne_zero hs)
  let s : ℝ := (a : ℝ)+b
  let t : ℝ := (a : ℝ)/s
  have hs0 : s ≠ 0 := hsp.ne'
  have ht : t ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · dsimp [t,s]; positivity
    · apply (div_le_one hsp).mpr
      dsimp [s]
      have := Nat.cast_nonneg (α := ℝ) b
      linarith
  have hml : μ ≤ |φ t| := hmin ht
  have hsa : s*t=(a : ℝ) := by dsimp [t]; field_simp
  have hsb : s*(1-t)=(b : ℝ) := by
    dsimp [t]
    field_simp
    dsimp [s]
    ring
  have hscale := realValue_smul f s t (1-t)
  rw [hsa,hsb,realValue_nat] at hscale
  have habs : |(binaryValue f a b : ℝ)| = s^f.natDegree*|φ t| := by
    rw [hscale,abs_mul,abs_of_nonneg (pow_nonneg hsp.le _)]
  have hbound : s^f.natDegree ≤ (H : ℝ)*|(binaryValue f a b : ℝ)| := by
    calc
      s^f.natDegree = s^f.natDegree*1 := by ring
      _ ≤ s^f.natDegree*((H : ℝ)*μ) := mul_le_mul_of_nonneg_left hHμ (pow_nonneg hsp.le _)
      _ ≤ s^f.natDegree*((H : ℝ)*|φ t|) := by gcongr
      _ = (H : ℝ)*|(binaryValue f a b : ℝ)| := by rw [habs]; ring
  have habs' : (((binaryValue f a b).natAbs : ℕ) : ℝ) = |(binaryValue f a b : ℝ)| := by
    simp only [Nat.cast_natAbs, Int.cast_abs]
  rw [← habs'] at hbound
  dsimp [s] at hbound
  exact_mod_cast hbound

lemma realValue_segment_nonzero (f : ℤ[X]) (hf : f.Monic)
    (hnoroot : ∀ t : ℝ, f.eval₂ (Int.castRingHom ℝ) t ≠ 0)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : realValue f t (1-t) ≠ 0 := by
  by_cases he : t=1
  · subst t
    simpa using (show realValue f 1 0 ≠ 0 by rw [realValue_one_zero f hf]; norm_num)
  · have hy : 1-t ≠ 0 := sub_ne_zero.mpr (fun hh => he hh.symm)
    rw [realValue_ratio f (t/(1-t)) t (1-t) (div_mul_cancel₀ t hy)]
    exact mul_ne_zero (pow_ne_zero _ hy) (hnoroot _)

lemma realValue_segment_positive (f : ℤ[X]) (hf : f.Monic)
    (hnoroot : ∀ t : ℝ, f.eval₂ (Int.castRingHom ℝ) t ≠ 0)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : 0 < realValue f t (1-t) := by
  let φ : ℝ → ℝ := fun u => realValue f u (1-u)
  have hφ : Continuous φ := by dsimp [φ, realValue]; fun_prop
  by_contra hh
  have hle : φ t ≤ 0 := le_of_not_gt hh
  have h1 : φ 1=1 := by simpa [φ] using realValue_one_zero f hf
  have hmem : (0 : ℝ) ∈ Set.Icc (φ t) (φ 1) := ⟨hle, by rw [h1]; norm_num⟩
  obtain ⟨u,hu,huz⟩ := intermediate_value_Icc ht.2 hφ.continuousOn hmem
  exact realValue_segment_nonzero f hf hnoroot u ⟨ht.1.trans hu.1,hu.2⟩ huz

lemma binaryValue_positive (f : ℤ[X]) (hf : f.Monic)
    (hnoroot : ∀ t : ℝ, f.eval₂ (Int.castRingHom ℝ) t ≠ 0)
    (a b : ℕ) (hab : 0 < a+b) : 0 < binaryValue f a b := by
  let s : ℝ := (a : ℝ)+b
  let t : ℝ := (a : ℝ)/s
  have hsp : 0 < s := by dsimp [s]; exact_mod_cast hab
  have hs0 : s ≠ 0 := hsp.ne'
  have ht : t ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · dsimp [t,s]; positivity
    · apply (div_le_one hsp).mpr
      dsimp [s]
      have := Nat.cast_nonneg (α := ℝ) b
      linarith
  have hsa : s*t=(a : ℝ) := by dsimp [t]; field_simp
  have hsb : s*(1-t)=(b : ℝ) := by
    dsimp [t]
    field_simp
    dsimp [s]
    ring
  have hh := realValue_smul f s t (1-t)
  rw [hsa,hsb,realValue_nat] at hh
  have hp : (0 : ℝ) < (binaryValue f a b : ℝ) := by
    rw [hh]
    exact mul_pos (pow_pos hsp _) (realValue_segment_positive f hf hnoroot t ht)
  exact_mod_cast hp

/-- For fixed quartic rational norm families with the displayed monic,
separability and coprimality certificates, the positivity and coercivity
hypotheses in the preceding denominator bound follow automatically. -/
theorem quartic_rational_family_bound {ι : Type*} [Fintype ι]
    (f U V B : ℤ[X]) (g A : ι → ℤ[X]) (D C : ℕ) (N : ℤ)
    (hf : f.Monic) (hd : 3 ≤ f.natDegree) (hD : 0 < D) (hC : 0 < C)
    (hdeg : ∀ i, (g i).natDegree ≤ f.natDegree)
    (hder : U*f+V*f.derivative = Polynomial.C (D : ℤ))
    (hbez : (∑ i, A i*g i)+B*f = Polynomial.C (C : ℤ))
    (hnorm : ∑ i, g i^4=Polynomial.C N*f^4)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ K > (0 : ℝ), ∀ (S : Finset (ℕ × ℕ)) (L : ℕ), 0 < L →
      (∀ a ∈ S, a.1.Coprime a.2) →
      (∀ a ∈ S, 0 < a.2) →
      (∀ a ∈ S, ∀ i, ∃ z : ℤ,
        (L : ℚ)*(g i).eval₂ (Int.castRingHom ℚ) ((a.1 : ℚ)/a.2) /
          f.eval₂ (Int.castRingHom ℚ) ((a.1 : ℚ)/a.2) = z) →
      (S.card : ℝ) ≤ K*(L : ℝ)^ε := by
  have hnoroot := denominator_no_real_zero f B g A C N hC hnorm hbez
  obtain ⟨H,hH,hheight⟩ := exists_coercivity f hf (by omega) hnoroot
  obtain ⟨K,hK,hbound⟩ := rational_parameter_bound f U V B g A D C H hf hd hD hC
    hdeg hder hbez ε hε
  refine ⟨K,hK,?_⟩
  intro S L hL hprim hbpos hint
  have hpos (a : ℕ × ℕ) (ha : a ∈ S) : 0 < binaryValue f a.1 a.2 :=
    binaryValue_positive f hf hnoroot a.1 a.2 (by have := hbpos a ha; omega)
  apply hbound S L hL hprim hbpos hpos hint
  intro a ha
  have he : (binaryValue f a.1 a.2).natAbs=(binaryValue f a.1 a.2).toNat := by
    have hz := (Int.natAbs_of_nonneg (hpos a ha).le).trans
      (Int.toNat_of_nonneg (hpos a ha).le).symm
    exact_mod_cast hz
  simpa only [he] using hheight a.1 a.2

end Erdos322Research.PositiveBinaryFormCoercivity
