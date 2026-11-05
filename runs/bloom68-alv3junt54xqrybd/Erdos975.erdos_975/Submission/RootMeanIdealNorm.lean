import Submission.RootMeanNumberField
import Mathlib.RingTheory.UniqueFactorizationDomain.Finite
import Mathlib.RingTheory.Ideal.Int
import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Mathlib.Data.Nat.Factorization.PrimePow

/-!
# Finite norm pushforward and multiplicativity

The norm fibers of nonzero ideals are finite. Regrouping a relatively-prime
multiplicative ideal function over these fibers gives a multiplicative
arithmetic function. In particular this applies to the Dedekind-zeta
coefficients already defined in `RootMeanNumberField`.
-/

namespace Erdos975Support

open NumberField Ideal UniqueFactorizationMonoid
open scoped nonZeroDivisors

namespace IdealEuler

variable (K : Type*) [Field K] [NumberField K]

/-- The finite fiber of the absolute norm on nonzero integral ideals. -/
noncomputable def normFiber (n : ℕ) : Finset ((Ideal (𝓞 K))⁰) :=
  ((Ideal.finite_setOf_absNorm_eq n).preimage Subtype.val_injective.injOn).toFinset

@[simp]
theorem mem_normFiber {I : (Ideal (𝓞 K))⁰} {n : ℕ} :
    I ∈ normFiber K n ↔ absNorm (I : Ideal (𝓞 K)) = n := by
  simp [normFiber]

@[simp]
theorem normFiber_zero : normFiber K 0 = ∅ := by
  ext I
  have hI : (I : Ideal (𝓞 K)) ≠ ⊥ := nonZeroDivisors.coe_ne_zero I
  simp [mem_normFiber, Ideal.absNorm_eq_zero_iff, hI]

@[simp]
theorem normFiber_one : normFiber K 1 = {1} := by
  ext I
  simp only [mem_normFiber, Ideal.absNorm_eq_one_iff, Finset.mem_singleton]
  constructor
  · intro h
    exact Subtype.ext (by simpa only [Submonoid.coe_one, Ideal.one_eq_top] using h)
  · intro h
    simp only [h, Submonoid.coe_one, Ideal.one_eq_top]

section Coeff

variable {R : Type*} [AddCommMonoid R]

/-- Sum an ideal function over each norm fiber. No convergence is involved. -/
noncomputable def normCoeff (f : (Ideal (𝓞 K))⁰ → R) : ArithmeticFunction R :=
  ⟨fun n ↦ ∑ I ∈ normFiber K n, f I, by simp⟩

@[simp]
theorem normCoeff_apply (f : (Ideal (𝓞 K))⁰ → R) (n : ℕ) :
    normCoeff K f n = ∑ I ∈ normFiber K n, f I := rfl

@[simp]
theorem normCoeff_one (f : (Ideal (𝓞 K))⁰ → R) : normCoeff K f 1 = f 1 := by
  simp

end Coeff

variable {K}

/-- Coprime integer norms force relatively prime ideals. -/
theorem isRelPrime_of_coprime_absNorm {I J : Ideal (𝓞 K)}
    (h : (absNorm I).Coprime (absNorm J)) : IsRelPrime I J := by
  intro D hDI hDJ
  have hD : absNorm D = 1 :=
    (h.of_dvd_left (map_dvd absNorm hDI)).eq_one_of_dvd
    (map_dvd absNorm hDJ)
  exact Ideal.isUnit_iff.mpr (Ideal.absNorm_eq_one_iff.mp hD)

/-- The norm of a prime ideal is a positive power of a rational prime. -/
theorem isPrimePow_absNorm {P : Ideal (𝓞 K)} (hP : Prime P) : IsPrimePow (absNorm P) := by
  letI : P.IsPrime := Ideal.isPrime_of_prime hP
  letI : NeZero P := ⟨hP.ne_zero⟩
  let p := absNorm (Ideal.under ℤ P)
  have hp : p.Prime := Nat.absNorm_under_prime P
  letI : Fact p.Prime := ⟨hp⟩
  have hf : 0 < (Ideal.span {(p : ℤ)}).inertiaDeg P := Ideal.inertiaDeg_pos _ _
  exact (isPrimePow_nat_iff _).mpr
    ⟨p, (Ideal.span {(p : ℤ)}).inertiaDeg P, hp, hf,
      (Ideal.absNorm_eq_pow_inertiaDeg' P hp).symm⟩

/-- Split an ideal over any coprime factorization of its norm. -/
theorem exists_mul_of_absNorm_eq_mul {I : Ideal (𝓞 K)} {m n : ℕ}
    (hm : m ≠ 0) (hn : n ≠ 0) (hmn : m.Coprime n) (hI : absNorm I = m * n) :
    ∃ A B : Ideal (𝓞 K), absNorm A = m ∧ absNorm B = n ∧ A * B = I := by
  suffices ∀ (m n : ℕ), m ≠ 0 → n ≠ 0 → m.Coprime n → absNorm I = m * n →
      ∃ A B : Ideal (𝓞 K), absNorm A = m ∧ absNorm B = n ∧ A * B = I from
    this m n hm hn hmn hI
  clear hm hn hmn hI m n
  induction I using WfDvdMonoid.induction_on_irreducible with
  | zero =>
    intro m n hm hn _ h
    exact (mul_ne_zero hm hn (by simpa using h.symm)).elim
  | unit u hu =>
    intro m n hm hn _ h
    have hu1 : u = 1 := by simpa [Ideal.one_eq_top] using Ideal.isUnit_iff.mp hu
    subst u
    have hmn1 : m * n = 1 := by simpa using h.symm
    obtain ⟨rfl, rfl⟩ := mul_eq_one.mp hmn1
    exact ⟨1, 1, by simp⟩
  | mul J P hJ hP ih =>
    intro m n hm hn hmn h
    have hP0 : absNorm P ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr hP.ne_zero
    have hdiv : absNorm P ∣ m * n := by rw [← h, map_mul]; exact dvd_mul_right _ _
    rcases (hmn.isPrimePow_dvd_mul (isPrimePow_absNorm
      (UniqueFactorizationMonoid.irreducible_iff_prime.mp hP))).mp hdiv with hPm | hPn
    · obtain ⟨m', hm'⟩ := hPm
      have hm'0 : m' ≠ 0 := by intro hz; simp [hz] at hm'; exact hm hm'
      have hmn' : m'.Coprime n := hmn.of_dvd_left ⟨absNorm P, by rw [hm']; exact mul_comm _ _⟩
      have hJnorm : absNorm J = m' * n := by
        apply mul_left_cancel₀ hP0
        rw [← map_mul, h, hm', mul_assoc]
      obtain ⟨A, B, hA, hB, hAB⟩ := ih m' n hm'0 hn hmn' hJnorm
      exact ⟨P * A, B, by rw [map_mul, hA, ← hm'], hB, by rw [mul_assoc, hAB]⟩
    · obtain ⟨n', hn'⟩ := hPn
      have hn'0 : n' ≠ 0 := by intro hz; simp [hz] at hn'; exact hn hn'
      have hmn' : m.Coprime n' := hmn.of_dvd_right ⟨absNorm P, by rw [hn']; exact mul_comm _ _⟩
      have hJnorm : absNorm J = m * n' := by
        apply mul_left_cancel₀ hP0
        rw [← map_mul, h, hn']
        ring
      obtain ⟨A, B, hA, hB, hAB⟩ := ih m n' hm hn'0 hmn' hJnorm
      exact ⟨A, P * B, hA, by rw [map_mul, hB, ← hn'], by rw [mul_left_comm, hAB]⟩

/-- Equality of products with coprime prescribed norms is unique. -/
theorem eq_of_mul_eq_mul_of_absNorm {A B C D : Ideal (𝓞 K)} {m n : ℕ}
    (hm : m ≠ 0) (hmn : m.Coprime n)
    (hA : absNorm A = m) (_hB : absNorm B = n)
    (hC : absNorm C = m) (hD : absNorm D = n) (h : A * B = C * D) : A = C ∧ B = D := by
  have hAD : IsRelPrime A D := isRelPrime_of_coprime_absNorm (by rwa [hA, hD])
  have hAC : A ∣ C := hAD.dvd_of_dvd_mul_right (h ▸ dvd_mul_right A B)
  obtain ⟨E, hE⟩ := hAC
  have hnE : absNorm E = 1 := by
    have heq := congrArg absNorm hE
    rw [hC, map_mul, hA] at heq
    exact mul_left_cancel₀ hm (by simpa using heq.symm)
  have hE1 : E = 1 := by simpa [Ideal.one_eq_top] using Ideal.absNorm_eq_one_iff.mp hnE
  have hACeq : A = C := by simpa [hE1] using hE.symm
  refine ⟨hACeq, ?_⟩
  apply mul_left_cancel₀ (show A ≠ 0 from fun hA0 ↦ hm (by simpa [hA0] using hA.symm))
  simpa [hACeq] using h

variable (K)

/-- Multiplication gives a bijection of coprime norm fibers. -/
theorem normFiber_mul_bijective {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0)
    (hmn : m.Coprime n) : Function.Bijective
    (fun q : {I // I ∈ normFiber K m} × {I // I ∈ normFiber K n} ↦
      (⟨q.1.1 * q.2.1, by
        rw [mem_normFiber, Submonoid.coe_mul, map_mul,
          (mem_normFiber K).mp q.1.2, (mem_normFiber K).mp q.2.2]⟩ :
        {I // I ∈ normFiber K (m * n)})) := by
  constructor
  · intro q r h
    obtain ⟨h1, h2⟩ := eq_of_mul_eq_mul_of_absNorm hm hmn
      ((mem_normFiber K).mp q.1.2) ((mem_normFiber K).mp q.2.2)
      ((mem_normFiber K).mp r.1.2) ((mem_normFiber K).mp r.2.2)
      (congrArg (fun z ↦ (z.1 : Ideal (𝓞 K))) h)
    exact Prod.ext (Subtype.ext (Subtype.ext h1)) (Subtype.ext (Subtype.ext h2))
  · intro I
    obtain ⟨A, B, hA, hB, hAB⟩ := exists_mul_of_absNorm_eq_mul hm hn hmn
      ((mem_normFiber K).mp I.2)
    have hA0 : A ≠ 0 := fun h ↦ hm (by simpa [h] using hA.symm)
    have hB0 : B ≠ 0 := fun h ↦ hn (by simpa [h] using hB.symm)
    refine ⟨(⟨⟨A, mem_nonZeroDivisors_of_ne_zero hA0⟩, (mem_normFiber K).mpr hA⟩,
      ⟨⟨B, mem_nonZeroDivisors_of_ne_zero hB0⟩, (mem_normFiber K).mpr hB⟩), ?_⟩
    exact Subtype.ext (Subtype.ext hAB)

variable {R : Type*} [CommSemiring R]

/-- Norm pushforward preserves multiplicativity on coprime ideals. -/
theorem isMultiplicative_normCoeff (f : (Ideal (𝓞 K))⁰ → R) (hf1 : f 1 = 1)
    (hf : ∀ (A B : (Ideal (𝓞 K))⁰), IsRelPrime (A : Ideal (𝓞 K)) (B : Ideal (𝓞 K)) →
      f (A * B) = f A * f B) : (normCoeff K f).IsMultiplicative := by
  classical
  refine ArithmeticFunction.IsMultiplicative.iff_ne_zero.mpr ⟨by simpa using hf1, ?_⟩
  intro m n hm hn hmn
  let e := Equiv.ofBijective _ (normFiber_mul_bijective K hm hn hmn)
  calc
    normCoeff K f (m * n) = ∑ I : {I // I ∈ normFiber K (m * n)}, f I.1 := by
      rw [normCoeff_apply, Finset.sum_coe_sort]
    _ = ∑ q : {I // I ∈ normFiber K m} × {I // I ∈ normFiber K n},
        f (q.1.1 * q.2.1) :=
      (Fintype.sum_equiv e _ _ (fun _ ↦ rfl)).symm
    _ = ∑ A : {I // I ∈ normFiber K m}, ∑ B : {I // I ∈ normFiber K n},
        f A.1 * f B.1 := by
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun A _ ↦ Finset.sum_congr rfl fun B _ ↦ ?_
      exact hf A.1 B.1 (isRelPrime_of_coprime_absNorm (by
        rwa [(mem_normFiber K).mp A.2, (mem_normFiber K).mp B.2]))
    _ = normCoeff K f m * normCoeff K f n := by
      rw [← Finset.sum_mul_sum, Finset.sum_coe_sort, Finset.sum_coe_sort]
      rfl

end IdealEuler

/-- The previously defined norm-counting coefficients are the pushforward of
one on the nonzero ideals. -/
theorem idealNormCoefficients_eq_normCoeff_one (K : Type*) [Field K] [NumberField K] :
    idealNormCoefficients K = IdealEuler.normCoeff K (fun _ ↦ (1 : ℝ)) := by
  classical
  ext n
  by_cases hn : n = 0
  · simp [hn]
  simp only [idealNormCoefficients, ArithmeticFunction.coe_mk, if_neg hn,
    IdealEuler.normCoeff_apply, Finset.sum_const, nsmul_eq_mul, mul_one]
  congr 1
  let e : {I : Ideal (𝓞 K) // absNorm I = n} ≃
      {I : (Ideal (𝓞 K))⁰ // I ∈ IdealEuler.normFiber K n} :=
    { toFun I := ⟨⟨I.1, mem_nonZeroDivisors_of_ne_zero (fun h ↦ hn (by
        simpa [h] using I.2.symm))⟩, (IdealEuler.mem_normFiber K).mpr I.2⟩
      invFun I := ⟨I.1.1, (IdealEuler.mem_normFiber K).mp I.2⟩
      left_inv I := rfl
      right_inv I := rfl }
  calc
    Nat.card {I : Ideal (𝓞 K) // absNorm I = n} =
        Nat.card {I : (Ideal (𝓞 K))⁰ // I ∈ IdealEuler.normFiber K n} := Nat.card_congr e
    _ = _ := by rw [Nat.card_eq_fintype_card, Fintype.card_coe]

@[simp]
theorem idealNormCoefficients_one (K : Type*) [Field K] [NumberField K] :
    idealNormCoefficients K 1 = 1 := by
  rw [idealNormCoefficients_eq_normCoeff_one, IdealEuler.normCoeff_one]

/-- The ideal norm-counting coefficients are multiplicative. -/
theorem isMultiplicative_idealNormCoefficients (K : Type*) [Field K] [NumberField K] :
    (idealNormCoefficients K).IsMultiplicative := by
  rw [idealNormCoefficients_eq_normCoeff_one]
  exact IdealEuler.isMultiplicative_normCoeff K _ rfl (fun _ _ _ ↦ by simp)

end Erdos975Support
