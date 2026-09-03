import FormalConjecturesUtil

/-! Anisotropy of four fourth powers over the Gaussian integers. This is a
construction obstruction, not an upper bound for the full quartic count. -/
namespace Erdos322Research.GaussianQuartic

noncomputable section

private def residue : GaussianInt →+* ZMod 5 :=
  Zsqrtd.lift ⟨2, by decide⟩

private def prime : GaussianInt := ⟨1, 2⟩

private lemma residue_kernel (z : GaussianInt) (h : residue z = 0) : prime ∣ z := by
  have h5 : (5 : ℤ) ∣ z.re + 2*z.im := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 5).mp
    simpa [residue, Zsqrtd.lift_apply_apply, mul_comm] using h
  have h5' : (5 : ℤ) ∣ z.im - 2*z.re := by
    obtain ⟨a,ha⟩ := h5
    refine ⟨z.im - 2*a, ?_⟩
    linarith
  refine ⟨⟨(z.re+2*z.im)/5, (z.im-2*z.re)/5⟩, ?_⟩
  have ha := Int.ediv_mul_cancel h5
  have hb := Int.ediv_mul_cancel h5'
  apply Zsqrtd.ext <;> simp only [prime, Zsqrtd.re_mul, Zsqrtd.im_mul]
  · nlinarith
  · nlinarith

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
private lemma residue_zero (a : Fin 4 → ZMod 5) (h : ∑ i, a i^4 = 0) :
    ∀ i, a i = 0 := by
  have H : ∀ a : Fin 4 → ZMod 5, (∑ i, a i^4 = 0) → ∀ i, a i = 0 := by decide
  exact H a h

private lemma prime_ne_zero : prime ≠ 0 := by
  intro h
  have := congrArg Zsqrtd.re h
  norm_num [prime] at this

private lemma norm_prime : Zsqrtd.norm prime = 5 := by
  norm_num [prime, Zsqrtd.norm]

/-- Four Gaussian-integer fourth powers summing to zero must all vanish. -/
theorem gaussian_fourth_sum_zero (a : Fin 4 → GaussianInt)
    (h : ∑ i, a i^4 = 0) : ∀ i, a i = 0 := by
  let N := ∑ i, (Zsqrtd.norm (a i)).natAbs
  suffices H : ∀ N : ℕ, ∀ a : Fin 4 → GaussianInt,
      (∑ i, (Zsqrtd.norm (a i)).natAbs) = N →
      (∑ i, a i^4 = 0) → ∀ i, a i = 0 by
    exact H N a rfl h
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro a hN h
    by_cases hzero : N = 0
    · intro i
      have hn : (Zsqrtd.norm (a i)).natAbs = 0 := by
        have hle := Finset.single_le_sum (f := fun i : Fin 4 ↦ (Zsqrtd.norm (a i)).natAbs)
          (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)
        dsimp only at hle
        omega
      exact GaussianInt.norm_eq_zero.mp (Int.natAbs_eq_zero.mp hn)
    · have hr : ∀ i, residue (a i) = 0 := by
        apply residue_zero
        have hh := congrArg residue h
        simpa only [map_sum, map_pow, map_zero] using hh
      have hd : ∀ i, ∃ b : GaussianInt, a i = prime*b :=
        fun i ↦ residue_kernel (a i) (hr i)
      choose b hb using hd
      have hb0 : ∑ i, b i^4 = 0 := by
        apply (mul_eq_zero.mp (show prime^4*(∑ i, b i^4)=0 from ?_)).resolve_left
          (pow_ne_zero _ prime_ne_zero)
        simpa only [hb, mul_pow, Finset.mul_sum] using h
      have hscale : 5*(∑ i, (Zsqrtd.norm (b i)).natAbs) = N := by
        rw [← hN, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [hb i, Zsqrtd.norm_mul, norm_prime, Int.natAbs_mul]
        norm_num
      have hsmall : (∑ i, (Zsqrtd.norm (b i)).natAbs) < N := by omega
      have hz := ih _ hsmall b rfl hb0
      intro i
      rw [hb i, hz i, mul_zero]

/-- The Gaussian rational field. -/
abbrev GaussianRational := FractionRing GaussianInt

/-- Clearing a common denominator extends the anisotropy to `ℚ(i)`. -/
theorem gaussian_rational_fourth_sum_zero (a : Fin 4 → GaussianRational)
    (h : ∑ i, a i^4 = 0) : ∀ i, a i = 0 := by
  obtain ⟨d,hd⟩ := IsLocalization.exist_integer_multiples_of_finite
    (nonZeroDivisors GaussianInt) a
  choose b hb using hd
  have hd0 : algebraMap GaussianInt GaussianRational d ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective GaussianInt GaussianRational).ne
      (nonZeroDivisors.ne_zero d.prop)
  have hb0 : ∑ i, b i^4 = 0 := by
    apply IsFractionRing.injective GaussianInt GaussianRational
    simp only [map_sum, map_pow, map_zero, hb, Algebra.smul_def, mul_pow]
    rw [← Finset.mul_sum, h, mul_zero]
  have hz := gaussian_fourth_sum_zero b hb0
  intro i
  have hi := hb i
  rw [hz i, map_zero, Algebra.smul_def] at hi
  exact (mul_eq_zero.mp hi.symm).resolve_left hd0

open Polynomial

/-- The standard positive binary quadratic denominator, dehomogenized. -/
def circlePolynomial : Polynomial ℤ := X^2+1

private def evalI : Polynomial ℤ →+* GaussianInt :=
  Polynomial.eval₂RingHom (Int.castRingHom GaussianInt) Zsqrtd.sqrtd

private lemma circle_monic : circlePolynomial.Monic := by
  simpa [circlePolynomial] using (Polynomial.monic_X_pow_add_C (1 : ℤ) (by decide : 2 ≠ 0))

private lemma circle_degree : circlePolynomial.natDegree = 2 := by
  simpa [circlePolynomial] using (Polynomial.natDegree_X_pow_add_C (R := ℤ) (n := 2) (r := 1))

private lemma circle_ne_zero : circlePolynomial ≠ 0 := circle_monic.ne_zero

private lemma circle_ne_one : circlePolynomial ≠ 1 := by
  intro h
  have := congrArg Polynomial.natDegree h
  rw [circle_degree, Polynomial.natDegree_one] at this
  omega

private lemma evalI_circle : evalI circlePolynomial = 0 := by
  simp [evalI, circlePolynomial, pow_two, Zsqrtd.dmuld]

private lemma circle_dvd_of_evalI_zero (p : Polynomial ℤ) (h : evalI p = 0) :
    circlePolynomial ∣ p := by
  apply (Polynomial.modByMonic_eq_zero_iff_dvd circle_monic).mp
  let r := p %ₘ circlePolynomial
  have hr : r.natDegree ≤ 1 := by
    change (p %ₘ circlePolynomial).natDegree ≤ 1
    have := Polynomial.natDegree_modByMonic_lt p circle_monic circle_ne_one
    rw [circle_degree] at this
    omega
  have he : evalI r = 0 := by
    exact (Polynomial.eval₂_modByMonic_eq_self_of_root circle_monic evalI_circle).trans h
  have hre := Polynomial.eq_X_add_C_of_natDegree_le_one hr
  rw [hre] at he
  simp only [map_add, map_mul] at he
  have ha : r.coeff 0 = 0 := by
    have hh := congrArg Zsqrtd.re he
    simpa [evalI] using hh
  have hb : r.coeff 1 = 0 := by
    have hh := congrArg Zsqrtd.im he
    simpa [evalI] using hh
  change r = 0
  rw [hre, ha, hb]
  simp

/-- Divisibility of a sum of four fourth powers by `X²+1` forces
coordinatewise divisibility. This holds at arbitrary polynomial degree. -/
theorem circle_dvd_all (P : Fin 4 → Polynomial ℤ)
    (h : circlePolynomial ∣ ∑ i, P i^4) : ∀ i, circlePolynomial ∣ P i := by
  obtain ⟨Q,hQ⟩ := h
  have he : ∑ i, (evalI (P i))^4 = 0 := by
    have hh := congrArg evalI hQ
    simpa only [map_sum, map_pow, map_mul, evalI_circle, zero_mul] using hh
  exact fun i ↦ circle_dvd_of_evalI_zero (P i) (gaussian_fourth_sum_zero _ he i)

/-- A pole of order at most `m` at either Gaussian point cannot survive in
any coordinate of a constant-quartic-norm rational map. -/
theorem circle_power_dvd_all (m : ℕ) (P : Fin 4 → Polynomial ℤ)
    (h : circlePolynomial^(4*m) ∣ ∑ i, P i^4) :
    ∀ i, circlePolynomial^m ∣ P i := by
  induction m generalizing P with
  | zero => simp
  | succ m ih =>
    have hd : circlePolynomial ∣ ∑ i, P i^4 := by
      exact (dvd_pow_self circlePolynomial (by omega : 4*(m+1) ≠ 0)).trans h
    have hd' : ∀ i, ∃ Q : Polynomial ℤ, P i = circlePolynomial*Q := circle_dvd_all P hd
    choose Q hQ using hd'
    have he : (∑ i, P i^4) = circlePolynomial^4*(∑ i, Q i^4) := by
      simp only [hQ, mul_pow, Finset.mul_sum]
    have hcancel : circlePolynomial^(4*m) ∣ ∑ i, Q i^4 := by
      rw [he, show 4*(m+1)=4+4*m by omega, pow_add] at h
      exact (mul_dvd_mul_iff_left (pow_ne_zero _ circle_ne_zero)).mp h
    have hi := ih Q hcancel
    intro i
    rw [hQ i, pow_succ']
    exact mul_dvd_mul_left _ (hi i)

private lemma constant_coordinates {R : Type*} [CommRing R] [LinearOrder R]
    [IsStrictOrderedRing R] (P : Fin 4 → Polynomial R) (a : R)
    (h : ∑ i, P i^4 = C a) : ∀ i, P i = C ((P i).coeff 0) := by
  classical
  intro i
  apply Polynomial.eq_C_of_natDegree_eq_zero
  by_contra hn
  let D := Finset.univ.sup (fun j ↦ (P j).natDegree)
  have hDi : (P i).natDegree ≤ D := Finset.le_sup (f := fun j ↦ (P j).natDegree)
    (Finset.mem_univ i)
  have hDpos : 0 < D := by omega
  have hD (j : Fin 4) : (P j).natDegree ≤ D :=
    Finset.le_sup (f := fun j ↦ (P j).natDegree) (Finset.mem_univ j)
  obtain ⟨j,_,hj⟩ := Finset.exists_mem_eq_sup Finset.univ
    (Finset.univ_nonempty_iff.mpr ⟨i⟩) (fun j ↦ (P j).natDegree)
  change D = (P j).natDegree at hj
  have hp : P j ≠ 0 := by
    intro hz
    simp [hz] at hj
    omega
  have hc : (P j).coeff D ≠ 0 := by
    rw [hj, coeff_natDegree]
    exact leadingCoeff_ne_zero.mpr hp
  have he : (∑ j, P j^4).coeff (4*D) = ∑ j, (P j).coeff D^4 := by
    simp only [finset_sum_coeff]
    exact Finset.sum_congr rfl (fun j _ ↦ coeff_pow_of_natDegree_le (hD j))
  have hs : (∑ j, (P j).coeff D^4) = 0 := by
    rw [← he, h]
    simpa using (Polynomial.coeff_eq_zero_of_natDegree_lt (show (C a).natDegree < 4*D by simpa using (show 0 < 4*D by omega)))
  have hpos : 0 < (P j).coeff D^4 := by positivity
  have hle := Finset.single_le_sum (f := fun j ↦ (P j).coeff D^4)
    (fun _ _ ↦ by positivity) (Finset.mem_univ j)
  rw [hs] at hle
  linarith

/-- In any four-coordinate constant-quartic-norm rational parametrization
with denominator `(1+t²)^m`, all four numerators are constant multiples of
the denominator. There is no restriction on their degrees. -/
theorem circle_denominator_rigidity (P : Fin 4 → Polynomial ℤ) (a : ℤ) (m : ℕ)
    (h : ∑ i, P i^4 = C a * circlePolynomial^(4*m)) :
    ∃ b : Fin 4 → ℤ, ∀ i, P i = C (b i)*circlePolynomial^m := by
  have hd : circlePolynomial^(4*m) ∣ ∑ i, P i^4 := by
    rw [h]
    exact dvd_mul_left _ _
  have hd' : ∀ i, ∃ Q : Polynomial ℤ, P i = circlePolynomial^m*Q :=
    circle_power_dvd_all m P hd
  choose Q hQ using hd'
  have hpow : (circlePolynomial^m)^4 = circlePolynomial^(4*m) := by
    rw [← pow_mul]
    congr 1
    omega
  have he : (∑ i, Q i^4) = C a := by
    simp_rw [hQ, mul_pow, hpow] at h
    rw [← Finset.mul_sum, mul_comm (C a)] at h
    exact mul_left_cancel₀ (pow_ne_zero _ circle_ne_zero) h
  have hc := constant_coordinates Q a he
  refine ⟨fun i ↦ (Q i).coeff 0, fun i ↦ ?_⟩
  rw [hQ i, hc i, mul_comm]

/-- The same standard quadratic denominator with rational coefficients. -/
def circlePolynomialRat : Polynomial ℚ := X^2+1

private def rationalI : GaussianRational :=
  algebraMap GaussianInt GaussianRational Zsqrtd.sqrtd

private lemma rationalI_sq : rationalI^2 = -1 := by
  unfold rationalI
  rw [← map_pow, pow_two, Zsqrtd.dmuld]
  simp

private lemma circleRat_monic : circlePolynomialRat.Monic := by
  simpa [circlePolynomialRat] using
    (Polynomial.monic_X_pow_add_C (1 : ℚ) (by decide : 2 ≠ 0))

private lemma circleRat_degree : circlePolynomialRat.natDegree = 2 := by
  simpa [circlePolynomialRat] using
    (Polynomial.natDegree_X_pow_add_C (R := ℚ) (n := 2) (r := 1))

private lemma circleRat_irreducible : Irreducible circlePolynomialRat := by
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · simp [circleRat_degree]
  · intro x hx
    have hh : x^2+1=0 := by simpa [Polynomial.IsRoot, circlePolynomialRat] using hx
    nlinarith [sq_nonneg x]

private lemma circleRat_aeval : Polynomial.aeval rationalI circlePolynomialRat = 0 := by
  simp [circlePolynomialRat, rationalI_sq]

private lemma circleRat_minpoly : circlePolynomialRat = minpoly ℚ rationalI :=
  minpoly.eq_of_irreducible_of_monic circleRat_irreducible circleRat_aeval circleRat_monic

/-- Rational-coefficient version of coordinatewise divisibility. -/
theorem circleRat_dvd_all (P : Fin 4 → Polynomial ℚ)
    (h : circlePolynomialRat ∣ ∑ i, P i^4) : ∀ i, circlePolynomialRat ∣ P i := by
  obtain ⟨Q,hQ⟩ := h
  have he : ∑ i, (Polynomial.aeval rationalI (P i))^4 = 0 := by
    have hh := congrArg (Polynomial.aeval rationalI) hQ
    simpa only [map_sum, map_pow, map_mul, circleRat_aeval, zero_mul] using hh
  intro i
  rw [circleRat_minpoly]
  exact minpoly.dvd ℚ rationalI (gaussian_rational_fourth_sum_zero _ he i)

/-- Rational-coefficient version, with arbitrary pole order. -/
theorem circleRat_power_dvd_all (m : ℕ) (P : Fin 4 → Polynomial ℚ)
    (h : circlePolynomialRat^(4*m) ∣ ∑ i, P i^4) :
    ∀ i, circlePolynomialRat^m ∣ P i := by
  induction m generalizing P with
  | zero => simp
  | succ m ih =>
    have hd : circlePolynomialRat ∣ ∑ i, P i^4 :=
      (dvd_pow_self circlePolynomialRat (by omega : 4*(m+1) ≠ 0)).trans h
    have hd' : ∀ i, ∃ Q : Polynomial ℚ, P i = circlePolynomialRat*Q :=
      circleRat_dvd_all P hd
    choose Q hQ using hd'
    have he : (∑ i, P i^4) = circlePolynomialRat^4*(∑ i, Q i^4) := by
      simp only [hQ, mul_pow, Finset.mul_sum]
    have hcancel : circlePolynomialRat^(4*m) ∣ ∑ i, Q i^4 := by
      rw [he, show 4*(m+1)=4+4*m by omega, pow_add] at h
      exact (mul_dvd_mul_iff_left (pow_ne_zero _ circleRat_monic.ne_zero)).mp h
    have hi := ih Q hcancel
    intro i
    rw [hQ i, pow_succ']
    exact mul_dvd_mul_left _ (hi i)

/-- A four-coordinate constant-quartic-norm rational parametrization over `ℚ`
with denominator `(1+t²)^m` must be constant, at every polynomial degree. -/
theorem circle_denominator_rigidity_rat (P : Fin 4 → Polynomial ℚ) (a : ℚ) (m : ℕ)
    (h : ∑ i, P i^4 = C a * circlePolynomialRat^(4*m)) :
    ∃ b : Fin 4 → ℚ, ∀ i, P i = C (b i)*circlePolynomialRat^m := by
  have hd : circlePolynomialRat^(4*m) ∣ ∑ i, P i^4 := by
    rw [h]
    exact dvd_mul_left _ _
  have hd' : ∀ i, ∃ Q : Polynomial ℚ, P i = circlePolynomialRat^m*Q :=
    circleRat_power_dvd_all m P hd
  choose Q hQ using hd'
  have hpow : (circlePolynomialRat^m)^4 = circlePolynomialRat^(4*m) := by
    rw [← pow_mul]
    congr 1
    omega
  have he : (∑ i, Q i^4) = C a := by
    simp_rw [hQ, mul_pow, hpow] at h
    rw [← Finset.mul_sum, mul_comm (C a)] at h
    exact mul_left_cancel₀ (pow_ne_zero _ circleRat_monic.ne_zero) h
  have hc := constant_coordinates Q a he
  refine ⟨fun i ↦ (Q i).coeff 0, fun i ↦ ?_⟩
  rw [hQ i, hc i, mul_comm]

/-- Pointwise version: no nonconstant rational parametrization with these
poles can lie on a four-coordinate quartic sphere. -/
theorem circle_rational_map_constant (P : Fin 4 → Polynomial ℚ) (a : ℚ) (m : ℕ)
    (h : ∀ t : ℚ, ∑ i, ((P i).eval t / (t^2+1)^m)^4 = a) :
    ∀ i t, (P i).eval t / (t^2+1)^m = (P i).eval 0 := by
  have hp : ∑ i, P i^4 = C a*circlePolynomialRat^(4*m) := by
    apply Polynomial.funext
    intro t
    have hd : (t^2+1)^m ≠ 0 := by positivity
    have he : (∑ i, (P i).eval t^4) = a*((t^2+1)^m)^4 := by
      apply (div_eq_iff (pow_ne_zero 4 hd)).mp
      simpa only [div_pow, Finset.sum_div] using h t
    have hpow : ((t^2+1)^m)^4 = (t^2+1)^(4*m) := by
      rw [← pow_mul]
      congr 1
      omega
    simpa only [eval_finset_sum, eval_pow, eval_mul, eval_C,
      circlePolynomialRat, eval_add, eval_X, eval_one, hpow] using he
  obtain ⟨b,hb⟩ := circle_denominator_rigidity_rat P a m hp
  intro i t
  have hd : (t^2+1)^m ≠ 0 := by positivity
  rw [hb i]
  simp only [eval_mul, eval_C, eval_pow, circlePolynomialRat, eval_add, eval_X, eval_one]
  simp [hd]

end
end Erdos322Research.GaussianQuartic
