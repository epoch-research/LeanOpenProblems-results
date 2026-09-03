import Submission.PolynomialCongruenceRootBound

/-! Primitive representation bounds for fixed positive binary forms.
These bounds concern two-variable forms, not the full four-variable conjecture. -/
namespace Erdos322Research.PositiveBinaryFormBound

open Polynomial Finset PolynomialCongruenceRootBound
set_option Elab.async false

/-- Homogenization evaluated on a pair of natural coordinates. -/
def binaryValue (f : ℤ[X]) (a b : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (f.natDegree+1), f.coeff j * (a : ℤ)^j * (b : ℤ)^(f.natDegree-j)

lemma binaryValue_mod_second (f : ℤ[X]) (hf : f.Monic) (a b : ℕ) :
    ((binaryValue f a b : ℤ) : ZMod b) = (a : ZMod b)^f.natDegree := by
  classical
  unfold binaryValue
  push_cast
  rw [Finset.sum_eq_single f.natDegree]
  · simp [hf.coeff_natDegree]
  · intro j hj hne
    have hjd : j < f.natDegree := by
      have := Finset.mem_range.mp hj
      omega
    simp [Nat.ne_of_gt (Nat.sub_pos_of_lt hjd)]
  · simp

lemma second_coprime_value (f : ℤ[X]) (hf : f.Monic) {a b n : ℕ}
    (hab : a.Coprime b) (h : binaryValue f a b=(n : ℤ)) : b.Coprime n := by
  have hh := congrArg (fun z : ℤ => (z : ZMod b)) h
  dsimp only at hh
  rw [binaryValue_mod_second f hf] at hh
  simp only [Int.cast_natCast] at hh
  have he : n ≡ a^f.natDegree [MOD b] :=
    (ZMod.natCast_eq_natCast_iff _ _ _).mp (by simpa using hh.symm)
  rw [Nat.coprime_comm]
  change Nat.gcd n b=1
  rw [he.gcd_eq]
  exact hab.pow_left _

lemma binaryValue_ratio (f : ℤ[X]) {n a b : ℕ} (r : ZMod n)
    (hr : r*(b : ZMod n)=a) :
    ((binaryValue f a b : ℤ) : ZMod n) =
      (b : ZMod n)^f.natDegree * f.eval₂ (Int.castRingHom (ZMod n)) r := by
  rw [Polynomial.eval₂_eq_sum_range' _ (Nat.lt_succ_self f.natDegree)]
  unfold binaryValue
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjd : j ≤ f.natDegree := by simpa using Finset.mem_range.mp hj
  have hp : (b : ZMod n)^j*(b : ZMod n)^(f.natDegree-j)=b^f.natDegree := by
    rw [← pow_add, Nat.add_sub_of_le hjd]
  rw [← hr, mul_pow]
  change (f.coeff j : ZMod n) * (r^j * (b : ZMod n)^j) * (b : ZMod n)^(f.natDegree-j) = _
  rw [show (f.coeff j : ZMod n) * (r^j * (b : ZMod n)^j) * (b : ZMod n)^(f.natDegree-j) =
    ((b : ZMod n)^j*(b : ZMod n)^(f.natDegree-j))*((f.coeff j : ZMod n)*r^j) by ring, hp]
  rfl

noncomputable def slope (n : ℕ) (a : ℕ × ℕ) : ℕ :=
  ((a.1 : ZMod n)*(a.2 : ZMod n)⁻¹).val

lemma slope_mul {n a b : ℕ} (hn : 0 < n) (hb : b.Coprime n) :
    slope n (a,b)*b ≡ a [MOD n] := by
  letI : NeZero n := ⟨hn.ne'⟩
  apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
  have hi := ZMod.mul_inv_of_unit (b : ZMod n) ((ZMod.isUnit_iff_coprime _ _).mpr hb)
  simp only [slope, Nat.cast_mul, ZMod.natCast_zmod_val]
  calc
    (a : ZMod n)*(b : ZMod n)⁻¹*b = a*(b*(b : ZMod n)⁻¹) := by ring
    _ = a := by rw [hi, mul_one]

lemma slope_root (f : ℤ[X]) (hf : f.Monic) {a b n : ℕ} (hn : 0 < n)
    (hab : a.Coprime b) (h : binaryValue f a b=(n : ℤ)) :
    slope n (a,b) ∈ rootsMod f n := by
  letI : NeZero n := ⟨hn.ne'⟩
  have hb := second_coprime_value f hf hab h
  have hu : IsUnit (b : ZMod n) := (ZMod.isUnit_iff_coprime _ _).mpr hb
  have hr := (ZMod.natCast_eq_natCast_iff _ _ _).mpr (slope_mul hn hb (a := a))
  simp only [Nat.cast_mul] at hr
  have he := binaryValue_ratio f (slope n (a,b) : ZMod n) hr
  rw [h] at he
  have hz : f.eval₂ (Int.castRingHom (ZMod n)) (slope n (a,b)) = 0 := by
    apply (hu.pow f.natDegree).mul_left_cancel
    simpa using he.symm
  refine mem_rootsMod.mpr ⟨ZMod.val_lt _, ?_⟩
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ n).mp
  have hc : (Int.castRingHom (ZMod n)) (slope n (a,b) : ℤ) =
      (slope n (a,b) : ZMod n) := by simp
  rw [← hc, Polynomial.eval₂_at_apply] at hz
  exact hz

lemma primitive_proportional {a b c d : ℕ} (hab : a.Coprime b) (hcd : c.Coprime d)
    (h : a*d=c*b) : (a,b)=(c,d) := by
  have hac : a ∣ c := hab.dvd_of_dvd_mul_right (h ▸ dvd_mul_right a d)
  have hca : c ∣ a := hcd.dvd_of_dvd_mul_right (h.symm ▸ dvd_mul_right c b)
  have he : a=c := Nat.dvd_antisymm hac hca
  subst c
  by_cases ha : a=0
  · subst a
    simp only [Nat.coprime_zero_left] at hab hcd
    simp [hab, hcd]
  · have hb : d=b := Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero ha) h
    simp [hb]

lemma cross_product_lt {a b c d n H k : ℕ} (hk : 3 ≤ k) (hH : H^2 < n)
    (ha : (a+b)^k ≤ H*n) (hb : (c+d)^k ≤ H*n) : a*d < n := by
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le _) hH
  have hap : a^k ≤ H*n := (Nat.pow_le_pow_left (Nat.le_add_right _ _) _).trans ha
  have hdp : d^k ≤ H*n := (Nat.pow_le_pow_left (Nat.le_add_left _ _) _).trans hb
  have hmul : (a*d)^k ≤ (H*n)^2 := by
    rw [mul_pow, pow_two]
    exact Nat.mul_le_mul hap hdp
  by_contra hh
  have he := (Nat.pow_le_pow_left (by omega : n ≤ a*d) k).trans hmul
  have h3 : n^3 ≤ n^k := Nat.pow_le_pow_right (by omega) hk
  have hbad : H^2*n^2 < n^3 := by
    have hh := Nat.mul_lt_mul_of_pos_right hH (pow_pos hn 2)
    convert hh using 1; ring
  nlinarith [h3.trans he]

/-- A primitive fiber of sufficiently large norm injects into polynomial
roots modulo that norm. Positivity enters through the displayed height bound. -/
theorem large_primitive_fiber_bound (f : ℤ[X]) (hf : f.Monic) (hd : 3 ≤ f.natDegree)
    (S : Finset (ℕ × ℕ)) (n H : ℕ) (hH : H^2 < n)
    (hprim : ∀ a ∈ S, a.1.Coprime a.2)
    (hval : ∀ a ∈ S, binaryValue f a.1 a.2=(n : ℤ))
    (hbound : ∀ a ∈ S, (a.1+a.2)^f.natDegree ≤ H*n) :
    S.card ≤ (rootsMod f n).card := by
  classical
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le _) hH
  apply Finset.card_le_card_of_injOn (slope n)
  · intro a ha
    exact slope_root f hf hn (hprim a ha) (hval a ha)
  · intro a ha b hb he
    have hac := second_coprime_value f hf (hprim a ha) (hval a ha)
    have hbc := second_coprime_value f hf (hprim b hb) (hval b hb)
    have hr := (slope_mul hn hac (a := a.1)).mul_right b.2
    have hs := (slope_mul hn hbc (a := b.1)).mul_right a.2
    have hc : a.1*b.2 ≡ b.1*a.2 [MOD n] := by
      apply hr.symm.trans
      convert hs using 1
      rw [he]
      ring
    have heq : a.1*b.2=b.1*a.2 := hc.eq_of_lt_of_lt
      (cross_product_lt hd hH (hbound a ha) (hbound b hb))
      (cross_product_lt hd hH (hbound b hb) (hbound a ha))
    exact primitive_proportional (hprim a ha) (hprim b hb) heq

/-- Uniform subpolynomial bounds for all primitive fibers of a fixed monic
binary form, given a fixed coercivity constant and a derivative Bezout certificate. -/
theorem primitive_fibers_subpolynomial (f A B : ℤ[X]) (hf : f.Monic)
    (hd : 3 ≤ f.natDegree) (C H : ℕ) (hC : 0 < C)
    (hbez : A*f+B*f.derivative = Polynomial.C (C : ℤ))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ K > (0 : ℝ), ∀ (S : Finset (ℕ × ℕ)) (n : ℕ), 0 < n →
      (∀ a ∈ S, a.1.Coprime a.2) →
      (∀ a ∈ S, binaryValue f a.1 a.2=(n : ℤ)) →
      (∀ a ∈ S, (a.1+a.2)^f.natDegree ≤ H*n) →
      (S.card : ℝ) ≤ K*(n : ℝ)^ε := by
  classical
  obtain ⟨K,hK,hroots⟩ := rootsMod_subpolynomial f A B hf (by omega) C hC hbez ε hε
  let J : ℕ := (H^3+1)^2
  refine ⟨K+J, by positivity, ?_⟩
  intro S n hn hprim hval hbound
  by_cases hlarge : H^2 < n
  · have hc : (S.card : ℝ) ≤ (rootsMod f n).card := by
      exact_mod_cast large_primitive_fiber_bound f hf hd S n H hlarge hprim hval hbound
    exact (hc.trans (hroots n hn)).trans (by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (Nat.cast_nonneg n) ε)
      exact le_add_of_nonneg_right (Nat.cast_nonneg J))
  · have hsmall : n ≤ H^2 := by omega
    have hs : S ⊆ Finset.range (H^3+1) ×ˢ Finset.range (H^3+1) := by
      intro a ha
      have hh : a.1+a.2 ≤ H^3 := by
        calc
          a.1+a.2 ≤ (a.1+a.2)^f.natDegree := Nat.le_pow (by omega)
          _ ≤ H*n := hbound a ha
          _ ≤ H*H^2 := Nat.mul_le_mul_left H hsmall
          _ = H^3 := by ring
      simp only [Finset.mem_product, Finset.mem_range]
      omega
    have hc : S.card ≤ J := by
      simpa [J, pow_two] using Finset.card_le_card hs
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hp : 1 ≤ (n : ℝ)^ε := Real.one_le_rpow hn1 hε.le
    calc
      (S.card : ℝ) ≤ J := by exact_mod_cast hc
      _ ≤ K+J := by linarith
      _ ≤ (K+J)*(n : ℝ)^ε := le_mul_of_one_le_right (by positivity) hp

/-- The same bound applies when the positive binary-form value is allowed to
range over all divisors of a common scale. This includes a union of fibers,
not just a single denominator value. -/
theorem primitive_divisor_fibers_subpolynomial (f A B : ℤ[X]) (hf : f.Monic)
    (hd : 3 ≤ f.natDegree) (C H : ℕ) (hC : 0 < C)
    (hbez : A*f+B*f.derivative = Polynomial.C (C : ℤ))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ K > (0 : ℝ), ∀ (S : Finset (ℕ × ℕ)) (L : ℕ), 0 < L →
      (∀ a ∈ S, a.1.Coprime a.2) →
      (∀ a ∈ S, 0 < binaryValue f a.1 a.2) →
      (∀ a ∈ S, (binaryValue f a.1 a.2).toNat ∣ L) →
      (∀ a ∈ S, (a.1+a.2)^f.natDegree ≤ H*(binaryValue f a.1 a.2).toNat) →
      (S.card : ℝ) ≤ K*(L : ℝ)^ε := by
  classical
  obtain ⟨K,hK,hfiber⟩ := primitive_fibers_subpolynomial f A B hf hd C H hC hbez
    (ε/2) (by positivity)
  obtain ⟨D,hD,hdiv⟩ := divisor_count_subpolynomial (ε/2) (by positivity)
  refine ⟨K*D, mul_pos hK hD, ?_⟩
  intro S L hL hprim hpos hdvd hbound
  let value (a : ℕ × ℕ) := (binaryValue f a.1 a.2).toNat
  let I := S.image value
  have hsub : I ⊆ L.divisors := by
    intro n hn
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hn
    exact Nat.mem_divisors.mpr ⟨hdvd a ha, hL.ne'⟩
  have hfib (n : ℕ) (hn : n ∈ I) :
      (((S.filter fun a => value a=n).card : ℕ) : ℝ) ≤ K*(L : ℝ)^(ε/2) := by
    obtain ⟨a,ha,hav⟩ := Finset.mem_image.mp hn
    have hnpos : 0 < n := by
      rw [← hav]
      have hh := hpos a ha
      change 0 < (binaryValue f a.1 a.2).toNat
      omega
    have hnL : n ≤ L := Nat.le_of_dvd hL (by rw [← hav]; exact hdvd a ha)
    have hb := hfiber (S.filter fun a => value a=n) n hnpos
      (by intro b hb; exact hprim b (Finset.mem_filter.mp hb).1)
      (by
        intro b hb
        obtain ⟨hbs,hbv⟩ := Finset.mem_filter.mp hb
        have hi := Int.toNat_of_nonneg (hpos b hbs).le
        change ((value b : ℕ) : ℤ) = _ at hi
        rw [hbv] at hi
        exact hi.symm)
      (by
        intro b hb
        obtain ⟨hbs,hbv⟩ := Finset.mem_filter.mp hb
        have hi := hbound b hbs
        change _ ≤ H*value b at hi
        rwa [hbv] at hi)
    exact hb.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg n) (by exact_mod_cast hnL) (by positivity)) hK.le)
  have hI : (I.card : ℝ) ≤ D*(L : ℝ)^(ε/2) := by
    have hi : (I.card : ℝ) ≤ L.divisors.card := by exact_mod_cast Finset.card_le_card hsub
    exact hi.trans (hdiv L hL)
  have hLp : (0 : ℝ) < L := by exact_mod_cast hL
  calc
    (S.card : ℝ) = ∑ n ∈ I, (((S.filter fun a => value a=n).card : ℕ) : ℝ) := by
      exact_mod_cast Finset.card_eq_sum_card_image value S
    _ ≤ ∑ _n ∈ I, K*(L : ℝ)^(ε/2) := Finset.sum_le_sum hfib
    _ = (I.card : ℝ)*(K*(L : ℝ)^(ε/2)) := by simp
    _ ≤ (D*(L : ℝ)^(ε/2))*(K*(L : ℝ)^(ε/2)) := by gcongr
    _ = (K*D)*(L : ℝ)^ε := by
      rw [show (D*(L : ℝ)^(ε/2))*(K*(L : ℝ)^(ε/2)) =
        (K*D)*((L : ℝ)^(ε/2)*(L : ℝ)^(ε/2)) by ring,
        ← Real.rpow_add hLp]
      congr 2
      ring

private noncomputable def exampleForm : ℤ[X] := X^4+X+1

private lemma exampleForm_monic : exampleForm.Monic := by
  unfold exampleForm
  monicity; norm_num

private lemma exampleForm_degree : exampleForm.natDegree=4 := by
  unfold exampleForm
  compute_degree; norm_num

private lemma exampleForm_bezout :
    (144*X^2-192*X+256)*exampleForm +
      (-36*X^3+48*X^2-64*X-27)*exampleForm.derivative = C (229 : ℤ) := by
  unfold exampleForm
  norm_num only [map_ofNat, derivative_add, derivative_pow, derivative_X,
    derivative_one, mul_one, add_zero]
  ring

private lemma exampleForm_value (a b : ℕ) :
    binaryValue exampleForm a b = ((a^4+a*b^3+b^4 : ℕ) : ℤ) := by
  unfold binaryValue
  rw [exampleForm_degree]
  norm_num [exampleForm, Finset.sum_range_succ, coeff_X, coeff_one]
  ring

private lemma exampleForm_coercive (a b : ℕ) :
    (a+b)^4 ≤ 8*(a^4+a*b^3+b^4) := by
  have hh : (0 : ℤ) ≤ ((a : ℤ)-(b : ℤ))^2 *
      (7*(a : ℤ)^2+10*(a : ℤ)*(b : ℤ)+7*(b : ℤ)^2) := by positivity
  have he : ((a : ℤ)+(b : ℤ))^4 ≤ 8*((a : ℤ)^4+(a : ℤ)*(b : ℤ)^3+(b : ℤ)^4) := by
    nlinarith [show (0 : ℤ) ≤ (a : ℤ)*(b : ℤ)^3 by positivity]
  exact_mod_cast he

/-- A concrete non-diagonal binary quartic example. The bound includes all
primitive pairs whose form value divides an arbitrary common scale. -/
theorem example_quartic_divisor_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ K > (0 : ℝ), ∀ (S : Finset (ℕ × ℕ)) (L : ℕ), 0 < L →
      (∀ a ∈ S, a.1.Coprime a.2) →
      (∀ a ∈ S, a.1^4+a.1*a.2^3+a.2^4 ∣ L) →
      (S.card : ℝ) ≤ K*(L : ℝ)^ε := by
  obtain ⟨K,hK,hbound⟩ := primitive_divisor_fibers_subpolynomial exampleForm
    (144*X^2-192*X+256) (-36*X^3+48*X^2-64*X-27) exampleForm_monic
    (by rw [exampleForm_degree]; decide) 229 8 (by decide) exampleForm_bezout ε hε
  refine ⟨K,hK,?_⟩
  intro S L hL hprim hdvd
  apply hbound S L hL hprim
  · intro a ha
    rw [exampleForm_value]
    have hn : 0 < a.1^4+a.1*a.2^3+a.2^4 := by
      by_contra hh
      have hz : a.1^4+a.1*a.2^3+a.2^4=0 := by omega
      have hd := hdvd a ha
      rw [hz, zero_dvd_iff] at hd
      omega
    exact_mod_cast hn
  · intro a ha
    simpa only [exampleForm_value, Int.toNat_natCast] using hdvd a ha
  · intro a ha
    simpa only [exampleForm_degree, exampleForm_value, Int.toNat_natCast] using
      exampleForm_coercive a.1 a.2

end Erdos322Research.PositiveBinaryFormBound
