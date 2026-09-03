import Submission.BinaryNormBound

/-! Denominator control for the Euler rational curve on the quartic level two.
These bounds concern this curve, not the full quartic representation count. -/
namespace Erdos322Research.QuarticCurveDenominators

/-- Even after cancellation, integrality of the difference coordinate forces
its unreduced denominator to divide twice the common scale. -/
theorem denominator_dvd_twice_scale {x y L : ℕ} (hc : x.Coprime y)
    (h : ((x^4+y^4 : ℕ) : ℤ) ∣ (L : ℤ)*((x : ℤ)^4-(y : ℤ)^4)) :
    x^4+y^4 ∣ 2*L := by
  have hs : ((x^4+y^4 : ℕ) : ℤ) ∣ (L : ℤ)*((x : ℤ)^4+(y : ℤ)^4) := by
    simpa only [Nat.cast_add, Nat.cast_pow] using
      (dvd_mul_left ((x^4+y^4 : ℕ) : ℤ) (L : ℤ))
  have ha : ((x^4+y^4 : ℕ) : ℤ) ∣ (2*(L : ℤ))*(x : ℤ)^4 := by
    convert dvd_add h hs using 1
    ring
  have han : x^4+y^4 ∣ (2*L)*x^4 := by exact_mod_cast ha
  have hh : (x^4+y^4).Coprime (x^4) :=
    Nat.coprime_self_add_left.mpr (hc.symm.pow 4 4)
  exact hh.dvd_of_dvd_mul_right han

/-- A finite family of primitive parameters whose quartic denominators divide
`M` has at most a divisor-function-sized number of elements. -/
theorem parameter_card_bound (S : Finset (ℕ × ℕ)) (M : ℕ) (hM : 0 < M)
    (hc : ∀ p ∈ S, p.1.Coprime p.2)
    (hd : ∀ p ∈ S, p.1^4+p.2^4 ∣ M) :
    S.card ≤ 4*M.divisors.card^2 := by
  classical
  let f : ℕ × ℕ → ℕ := fun p ↦ p.1^4+p.2^4
  let D := S.image f
  have hD : D ⊆ M.divisors := by
    intro d hd'
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hd'
    exact Nat.mem_divisors.mpr ⟨hd p hp,hM.ne'⟩
  have hfiber (d : ℕ) (hd' : d ∈ D) :
      (S.filter (fun p ↦ f p=d)).card ≤ 4*M.divisors.card := by
    have hdm := Nat.mem_divisors.mp (hD hd')
    have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdm.1 hM
    have hdiv : d.divisors.card ≤ M.divisors.card :=
      Finset.card_le_card (Nat.divisors_subset_of_dvd hM.ne' hdm.1)
    apply le_trans _ ((primitive_binary_norm_count_general (d := 1) (by decide) hdpos).trans
      (show d.divisors.card*(4*1) ≤ 4*M.divisors.card by omega))
    apply Finset.card_le_card_of_injOn (fun p : ℕ × ℕ ↦ (p.1^2,p.2^2))
    · intro p hp
      obtain ⟨hp,he⟩ := Finset.mem_filter.mp hp
      apply Finset.mem_filter.mpr
      constructor
      · apply (mem_binaryNormSolutions (by decide : 0 < 1) _).mpr
        change (p.1^2)^2+1*(p.2^2)^2=d
        dsimp only [f] at he
        nlinarith [he]
      · exact (hc p hp).pow 2 2
    · intro p hp q hq he
      apply Prod.ext
      · exact Nat.pow_left_injective (by decide : 2 ≠ 0) (congrArg Prod.fst he)
      · exact Nat.pow_left_injective (by decide : 2 ≠ 0) (congrArg Prod.snd he)
  calc
    S.card = ∑ d ∈ D, (S.filter (fun p ↦ f p=d)).card :=
      Finset.card_eq_sum_card_image f S
    _ ≤ ∑ d ∈ D, 4*M.divisors.card := Finset.sum_le_sum hfiber
    _ = D.card*(4*M.divisors.card) := by simp
    _ ≤ M.divisors.card*(4*M.divisors.card) :=
      Nat.mul_le_mul_right _ (Finset.card_le_card hD)
    _ = 4*M.divisors.card^2 := by ring

/-- Arbitrary common scales and arbitrary cancellation are allowed. This is
not limited to parameter sets coming from a chosen denominator product. -/
theorem integral_parameter_card_bound (S : Finset (ℕ × ℕ)) (L : ℕ) (hL : 0 < L)
    (hc : ∀ p ∈ S, p.1.Coprime p.2)
    (hint : ∀ p ∈ S, ((p.1^4+p.2^4 : ℕ) : ℤ) ∣
      (L : ℤ)*((p.1 : ℤ)^4-(p.2 : ℤ)^4)) :
    S.card ≤ 4*(2*L).divisors.card^2 := by
  apply parameter_card_bound S (2*L) (by omega) hc
  intro p hp
  exact denominator_dvd_twice_scale (hc p hp) (hint p hp)

/-- The complete primitive parameter contribution at any common scale is
subpolynomial. In particular, optimizing the choice of common denominator
cannot turn this particular rational curve into a power-growth construction. -/
theorem integral_parameters_subpolynomial (ε : ℝ) (hε : 0 < ε) :
    ∃ C > (0 : ℝ), ∀ (L : ℕ) (S : Finset (ℕ × ℕ)), 0 < L →
      (∀ p ∈ S, p.1.Coprime p.2) →
      (∀ p ∈ S, ((p.1^4+p.2^4 : ℕ) : ℤ) ∣
        (L : ℤ)*((p.1 : ℤ)^4-(p.2 : ℤ)^4)) →
      (S.card : ℝ) ≤ C*(L : ℝ)^ε := by
  obtain ⟨A,hA,hbound⟩ := divisor_count_subpolynomial (ε/2) (by linarith)
  refine ⟨4*A^2*(2 : ℝ)^ε,by positivity,?_⟩
  intro L S hL hc hint
  have hpos : (0 : ℝ) < (2*L : ℕ) := by exact_mod_cast (show 0 < 2*L by omega)
  have hp : (((2*L : ℕ) : ℝ)^(ε/2))^2 = ((2*L : ℕ) : ℝ)^ε := by
    rw [pow_two,← Real.rpow_add hpos]
    congr 1
    ring
  calc
    (S.card : ℝ) ≤ 4*((2*L).divisors.card : ℝ)^2 := by
      exact_mod_cast integral_parameter_card_bound S L hL hc hint
    _ ≤ 4*(A*((2*L : ℕ) : ℝ)^(ε/2))^2 := by
      gcongr
      exact hbound (2*L) (by omega)
    _ = 4*A^2*((2*L : ℕ) : ℝ)^ε := by rw [mul_pow,hp]; ring
    _ = (4*A^2*(2 : ℝ)^ε)*(L : ℝ)^ε := by
      rw [Nat.cast_mul,Nat.cast_ofNat,Real.mul_rpow (by norm_num) (Nat.cast_nonneg L)]
      ring

/-- The Euler curve, with signed rational coordinates. Taking absolute values
later does not change its quartic norm. -/
def point (p : ℕ × ℕ) : Fin 4 → ℚ :=
  ![2*p.1*p.2^3/(p.1^4+p.2^4),
    2*p.1^3*p.2/(p.1^4+p.2^4),
    ((p.1 : ℚ)^4-p.2^4)/(p.1^4+p.2^4),
    ((p.1 : ℚ)^4-p.2^4)/(p.1^4+p.2^4)]

private lemma denominator_pos {p : ℕ × ℕ} (hc : p.1.Coprime p.2) :
    0 < p.1^4+p.2^4 := by
  by_contra hn
  have h0 : p.1^4+p.2^4=0 := by omega
  have hx : p.1=0 := eq_zero_of_pow_eq_zero (show p.1^4=0 by omega)
  have hy : p.2=0 := eq_zero_of_pow_eq_zero (show p.2^4=0 by omega)
  simp [hx,hy] at hc

theorem point_norm {p : ℕ × ℕ} (hc : p.1.Coprime p.2) :
    ∑ i, point p i^4 = 2 := by
  have hn : (p.1 : ℚ)^4+p.2^4 ≠ 0 := by
    have := denominator_pos hc
    exact_mod_cast this.ne'
  simp only [point,Fin.sum_univ_succ,Fin.isValue,Matrix.cons_val_zero,
    Matrix.cons_val_succ,Matrix.cons_val_fin_one,Fin.sum_univ_zero,add_zero]
  field_simp
  ring

theorem integral_point_denominator {p : ℕ × ℕ} (hc : p.1.Coprime p.2)
    (L : ℕ) (h : ∃ z : ℤ, (L : ℚ)*point p 2=z) :
    p.1^4+p.2^4 ∣ 2*L := by
  obtain ⟨z,hz⟩ := h
  have hn : (p.1 : ℚ)^4+p.2^4 ≠ 0 := by
    have := denominator_pos hc
    exact_mod_cast this.ne'
  have he : (L : ℚ)*((p.1 : ℚ)^4-p.2^4)=
      ((p.1 : ℚ)^4+p.2^4)*z := by
    change (L : ℚ)*(((p.1 : ℚ)^4-p.2^4)/((p.1 : ℚ)^4+p.2^4))=z at hz
    field_simp at hz
    simpa only [mul_comm] using hz
  apply denominator_dvd_twice_scale hc
  refine ⟨z,?_⟩
  exact_mod_cast he

private lemma integer_of_abs_eq_nat {q : ℚ} {a : ℕ} (h : |q|=(a : ℚ)) :
    ∃ z : ℤ, q=z := by
  by_cases hq : 0 ≤ q
  · exact ⟨a,by simpa only [abs_of_nonneg hq,Int.cast_natCast] using h⟩
  · refine ⟨-(a : ℤ),?_⟩
    rw [abs_of_neg (lt_of_not_ge hq)] at h
    push_cast
    linarith

/-- Bound every distinct nonnegative integral output from the curve at scale
`L`, including arbitrary permutations, signs removed, and cancellation of
rational denominators. No particular parameter enumeration is assumed. -/
theorem curve_permutation_card_bound
    (T : Finset (Fin 4 → ℕ)) (L : ℕ) (hL : 0 < L)
    (hT : ∀ a ∈ T, ∃ p : ℕ × ℕ, p.1.Coprime p.2 ∧
      ∃ σ : Equiv.Perm (Fin 4), ∀ i,
        (a i : ℚ)=|(L : ℚ)*point p (σ i)|) :
    T.card ≤ 96*(2*L).divisors.card^2 := by
  classical
  choose p hc σ he using fun a : T ↦ hT a.val a.property
  let S : Finset (ℕ × ℕ) := Finset.univ.image p
  have hS : S.card ≤ 4*(2*L).divisors.card^2 := by
    apply parameter_card_bound S (2*L) (by omega)
    · intro q hq
      obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hq
      exact hc a
    · intro q hq
      obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hq
      apply integral_point_denominator (hc a) L
      apply integer_of_abs_eq_nat (a := a.val ((σ a).symm 2))
      simpa only [Equiv.apply_symm_apply] using (he a ((σ a).symm 2)).symm
  have hcard : T.card ≤ (S ×ˢ (Finset.univ : Finset (Equiv.Perm (Fin 4)))).card := by
    have hh := Finset.card_le_card_of_injOn (fun a : T ↦ (p a,σ a))
      (s := Finset.univ)
      (t := S ×ˢ (Finset.univ : Finset (Equiv.Perm (Fin 4))))
      (by
        intro a ha
        exact Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨a,ha,rfl⟩,Finset.mem_univ _⟩)
      (by
        intro a ha b hb hab
        have hp : p a=p b := congrArg Prod.fst hab
        have hσ : σ a=σ b := congrArg Prod.snd hab
        apply Subtype.ext
        funext i
        apply Nat.cast_injective (R := ℚ)
        rw [he a i,he b i,hp,hσ])
    simpa only [Finset.card_univ,Fintype.card_coe] using hh
  have hperm : (Finset.univ : Finset (Equiv.Perm (Fin 4))).card=24 := by decide
  rw [Finset.card_product,hperm] at hcard
  nlinarith

/-- This is an upper bound only for the Euler-curve contribution. It does not
assert an upper bound for unrestricted sums of four fourth powers. -/
theorem curve_contribution_subpolynomial (ε : ℝ) (hε : 0 < ε) :
    ∃ C > (0 : ℝ), ∀ (L : ℕ) (T : Finset (Fin 4 → ℕ)), 0 < L →
      (∀ a ∈ T, ∃ p : ℕ × ℕ, p.1.Coprime p.2 ∧
        ∃ σ : Equiv.Perm (Fin 4), ∀ i,
          (a i : ℚ)=|(L : ℚ)*point p (σ i)|) →
      (T.card : ℝ) ≤ C*((2*L^4 : ℕ) : ℝ)^ε := by
  obtain ⟨A,hA,hbound⟩ := divisor_count_subpolynomial (ε/2) (by linarith)
  refine ⟨96*A^2,by positivity,?_⟩
  intro L T hL hT
  have hpos : (0 : ℝ) < (2*L : ℕ) := by exact_mod_cast (show 0 < 2*L by omega)
  have hp : (((2*L : ℕ) : ℝ)^(ε/2))^2 = ((2*L : ℕ) : ℝ)^ε := by
    rw [pow_two,← Real.rpow_add hpos]
    congr 1
    ring
  have hle : (2*L : ℕ) ≤ 2*L^4 :=
    Nat.mul_le_mul_left 2 (Nat.le_pow (by decide : 0 < 4))
  calc
    (T.card : ℝ) ≤ 96*((2*L).divisors.card : ℝ)^2 := by
      exact_mod_cast curve_permutation_card_bound T L hL hT
    _ ≤ 96*(A*((2*L : ℕ) : ℝ)^(ε/2))^2 := by
      gcongr
      exact hbound (2*L) (by omega)
    _ = (96*A^2)*((2*L : ℕ) : ℝ)^ε := by rw [mul_pow,hp]; ring
    _ ≤ (96*A^2)*((2*L^4 : ℕ) : ℝ)^ε := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast hle) hε.le

/-- The Euler curve is a proper subfamily: this representation of the same
quartic level has four distinct coordinates, whereas every curve point has
two equal coordinates even after taking absolute values and permuting. -/
theorem outside_curve_example :
    (∑ i, (![0,7,8,15] i : ℕ)^4)=2*13^4 ∧
      ¬∃ p : ℕ × ℕ, ∃ σ : Equiv.Perm (Fin 4), ∀ i,
        ((![0,7,8,15] i : ℕ) : ℚ)=|(13 : ℚ)*point p (σ i)| := by
  constructor
  · norm_num [Fin.sum_univ_succ]
  · rintro ⟨p,σ,h⟩
    have hinj : Function.Injective (![0,7,8,15] : Fin 4 → ℕ) := by decide
    have h₂ := h (σ.symm 2)
    have h₃ := h (σ.symm 3)
    simp only [Equiv.apply_symm_apply] at h₂ h₃
    have he : ((![0,7,8,15] (σ.symm 2) : ℕ) : ℚ)=
        (![0,7,8,15] (σ.symm 3) : ℕ) := by
      rw [h₂,h₃]
      rfl
    have he' : (![0,7,8,15] (σ.symm 2) : ℕ)=![0,7,8,15] (σ.symm 3) := by
      exact_mod_cast he
    have hh := σ.symm.injective (hinj he')
    exact (by decide : (2 : Fin 4) ≠ 3) hh

/-- An integer target on quartic level two permits no genuinely fractional
scaling: the reduced denominator would have fourth power dividing two. -/
theorem rational_scale_integral {q : ℚ} {n : ℕ} (h : 2*q^4=(n : ℚ)) :
    ∃ z : ℤ, q=z := by
  have he : 2*(q.num : ℚ)^4=(n : ℚ)*q.den^4 := by
    rw [← Rat.mul_den_eq_num]
    calc
      2*(q*(q.den : ℚ))^4 = (2*q^4)*(q.den : ℚ)^4 := by ring
      _ = (n : ℚ)*q.den^4 := by rw [h]
  have hz : 2*q.num^4=(n : ℤ)*q.den^4 := by exact_mod_cast he
  have ha : 2*q.num.natAbs^4=n*q.den^4 := by
    have hp : ((q.num.natAbs : ℕ) : ℤ)^4=q.num^4 := by
      rw [Int.natCast_natAbs]
      exact Even.pow_abs (by decide : Even 4) _
    have he' : 2*((q.num.natAbs : ℕ) : ℤ)^4=(n : ℤ)*q.den^4 := by
      rw [hp,hz]
    exact_mod_cast he'
  have hd : q.den^4 ∣ 2*q.num.natAbs^4 := ⟨n,by simpa only [mul_comm] using ha⟩
  have hdiv : q.den^4 ∣ 2 := (q.reduced.symm.pow 4 4).dvd_of_dvd_mul_right hd
  have hle : q.den^4 ≤ 2 := Nat.le_of_dvd (by decide) hdiv
  have hden : q.den=1 := by
    have hp := q.den_pos
    have hdle : q.den ≤ 2 := (Nat.le_pow (by decide : 0 < 4)).trans hle
    interval_cases q.den <;> norm_num at *
  refine ⟨q.num,?_⟩
  have hh := Rat.mul_den_eq_num q
  simpa only [hden,Nat.cast_one,mul_one] using hh

/-- Rational scale, norm, and coordinate equalities reduce to a single
nonnegative integer scale. -/
theorem natural_scale_of_curve_representation
    {a : Fin 4 → ℕ} {n : ℕ} {q : ℚ} {p : ℕ × ℕ}
    (hc : p.1.Coprime p.2) (σ : Equiv.Perm (Fin 4))
    (he : ∀ i, (a i : ℚ)=|q*point p (σ i)|)
    (hn : ∑ i, a i^4=n) :
    ∃ L : ℕ, n=2*L^4 ∧ ∀ i, (a i : ℚ)=|(L : ℚ)*point p (σ i)| := by
  have hh : ∑ i, |q*point p (σ i)|^4=(n : ℚ) := by
    simp_rw [← he]
    exact_mod_cast hn
  simp_rw [Even.pow_abs (by decide : Even 4),mul_pow] at hh
  rw [← Finset.mul_sum,Equiv.sum_comp σ (fun i ↦ point p i^4),point_norm hc] at hh
  obtain ⟨z,hz⟩ := rational_scale_integral (by simpa only [mul_comm] using hh)
  refine ⟨z.natAbs,?_,?_⟩
  · have hp : ((z.natAbs : ℕ) : ℚ)^4=(z : ℚ)^4 := by
      rw [Nat.cast_natAbs,Int.cast_abs]
      exact Even.pow_abs (by decide : Even 4) _
    rw [hz] at hh
    have hh' : (n : ℚ)=2*((z.natAbs : ℕ) : ℚ)^4 := by
      rw [hp]
      linarith
    exact_mod_cast hh'
  · intro i
    rw [he i,hz,abs_mul,abs_mul]
    congr 1
    have hh' : ((z.natAbs : ℕ) : ℚ)=|(z : ℚ)| := by
      rw [Nat.cast_natAbs,Int.cast_abs]
    rw [hh',abs_abs]

/-- Full bound on this fixed rational curve, at any natural target and with
arbitrary rational scales. The restriction to this curve is essential. -/
theorem all_curve_contribution_subpolynomial (ε : ℝ) (hε : 0 < ε) :
    ∃ C > (0 : ℝ), ∀ (n : ℕ) (T : Finset (Fin 4 → ℕ)), 0 < n →
      (∀ a ∈ T, ∑ i, a i^4=n) →
      (∀ a ∈ T, ∃ q : ℚ, ∃ p : ℕ × ℕ, p.1.Coprime p.2 ∧
        ∃ σ : Equiv.Perm (Fin 4), ∀ i, (a i : ℚ)=|q*point p (σ i)|) →
      (T.card : ℝ) ≤ C*(n : ℝ)^ε := by
  obtain ⟨C,hC,hbound⟩ := curve_contribution_subpolynomial ε hε
  refine ⟨C,hC,?_⟩
  intro n T hn hnorm hT
  by_cases hEmpty : T=∅
  · subst T
    simp only [Finset.card_empty,Nat.cast_zero]
    positivity
  obtain ⟨a,ha⟩ := Finset.nonempty_iff_ne_empty.mpr hEmpty
  obtain ⟨q,p,hc,σ,he⟩ := hT a ha
  obtain ⟨L,hL,heL⟩ := natural_scale_of_curve_representation hc σ he (hnorm a ha)
  have hLpos : 0 < L := by
    by_contra h
    have hz : L=0 := by omega
    simp [hz] at hL
    omega
  rw [hL]
  apply hbound L T hLpos
  intro b hb
  obtain ⟨q',p',hc',σ',he'⟩ := hT b hb
  obtain ⟨M,hM,heM⟩ := natural_scale_of_curve_representation hc' σ' he' (hnorm b hb)
  have hML : M=L := by
    apply Nat.pow_left_injective (by decide : 4 ≠ 0)
    change M^4=L^4
    omega
  refine ⟨p',hc',σ',?_⟩
  simpa only [hML] using heM

end Erdos322Research.QuarticCurveDenominators
