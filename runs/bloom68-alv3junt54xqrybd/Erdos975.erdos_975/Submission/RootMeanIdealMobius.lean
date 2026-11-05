import Submission.RootMeanIdealNorm
import Mathlib.Data.Nat.Choose.Sum

/-!
# The ideal Möbius coefficients and their actual Dirichlet inverse

The ideal Möbius function is zero off squarefree ideals, and is `(-1)^r`
on an ideal with `r` distinct prime factors. Its finite norm pushforward is
an explicit two-sided Dirichlet-convolution inverse of the ideal norm-counting
coefficients. The identity here is the delta function `1`, not `zeta`.

The finite-fiber convolution and powerset divisor-sum arguments are minimal
adaptations of TauCeti's `ArithmeticDirichletSeries/Convolution` and `Moebius`.
-/

namespace Erdos975Support

open NumberField Ideal UniqueFactorizationMonoid
open scoped nonZeroDivisors

/-- Integer-valued Möbius function of an integral ideal. -/
noncomputable def idealMobius {K : Type*} [Field K] [NumberField K]
    (I : Ideal (𝓞 K)) : ℤ :=
  by
    classical
    exact if Squarefree I then (-1) ^ (normalizedFactors I).card else 0

@[simp]
theorem idealMobius_of_not_squarefree {K : Type*} [Field K] [NumberField K]
    {I : Ideal (𝓞 K)} (h : ¬ Squarefree I) : idealMobius I = 0 := if_neg h

theorem idealMobius_of_squarefree {K : Type*} [Field K] [NumberField K]
    {I : Ideal (𝓞 K)} (h : Squarefree I) :
    idealMobius I = (-1) ^ (normalizedFactors I).card := if_pos h

@[simp]
theorem idealMobius_one (K : Type*) [Field K] [NumberField K] :
    idealMobius (1 : Ideal (𝓞 K)) = 1 := by
  rw [idealMobius_of_squarefree squarefree_one, normalizedFactors_one]
  rfl

@[simp]
theorem idealMobius_top (K : Type*) [Field K] [NumberField K] :
    idealMobius (⊤ : Ideal (𝓞 K)) = 1 := by
  rw [← Ideal.one_eq_top]
  exact idealMobius_one K

/-- Ideal Möbius is multiplicative on relatively prime nonzero ideals. -/
theorem idealMobius_mul {K : Type*} [Field K] [NumberField K]
    {I J : Ideal (𝓞 K)} (hI : I ≠ 0) (hJ : J ≠ 0) (h : IsRelPrime I J) :
    idealMobius (I * J) = idealMobius I * idealMobius J := by
  classical
  by_cases hsI : Squarefree I <;> by_cases hsJ : Squarefree J <;>
    simp [idealMobius, squarefree_mul_iff, h, hsI, hsJ,
      normalizedFactors_mul hI hJ, Multiset.card_add, pow_add]

/-- Every ideal Möbius value has absolute value at most one. -/
theorem abs_idealMobius_le_one {K : Type*} [Field K] [NumberField K]
    (I : Ideal (𝓞 K)) : |idealMobius I| ≤ 1 := by
  classical
  by_cases h : Squarefree I <;> simp [idealMobius, h, abs_pow]

namespace IdealEuler

variable {K : Type*} [Field K] [NumberField K]

/-- Finite factorizations of a nonzero integral ideal. -/
theorem finite_idealFactorizations (A : (Ideal (𝓞 K))⁰) :
    {q : (Ideal (𝓞 K))⁰ × (Ideal (𝓞 K))⁰ | q.1 * q.2 = A}.Finite := by
  classical
  let hfin : Fintype {I : Ideal (𝓞 K) // I ∣ (A : Ideal (𝓞 K))} :=
    UniqueFactorizationMonoid.fintypeSubtypeDvd _ (nonZeroDivisors.coe_ne_zero A)
  have hdvd : {I : Ideal (𝓞 K) | I ∣ (A : Ideal (𝓞 K))}.Finite :=
    Set.Finite.ofFinset
      (Finset.univ.image (Subtype.val : {I : Ideal (𝓞 K) // I ∣ (A : Ideal (𝓞 K))} → _))
      (by simp)
  refine Set.Finite.of_finite_image (f := fun q ↦ ((q.1 : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)))
    (hdvd.subset ?_) ?_
  · rintro _ ⟨q, hq, rfl⟩
    exact ⟨(q.2 : Ideal (𝓞 K)), by simpa using congrArg Subtype.val hq.symm⟩
  · rintro q hq r hr hqr
    have h1 : q.1 = r.1 := Subtype.ext hqr
    have h2 : q.2 = r.2 := by
      refine mul_left_cancel (a := q.1) ?_
      rw [hq, ← hr, h1]
    exact Prod.ext h1 h2

/-- The ideal analogue of the natural divisor antidiagonal. -/
noncomputable def divisorsAntidiagonal (A : (Ideal (𝓞 K))⁰) :
    Finset ((Ideal (𝓞 K))⁰ × (Ideal (𝓞 K))⁰) :=
  (finite_idealFactorizations A).toFinset

@[simp]
theorem mem_divisorsAntidiagonal {A : (Ideal (𝓞 K))⁰}
    {q : (Ideal (𝓞 K))⁰ × (Ideal (𝓞 K))⁰} :
    q ∈ divisorsAntidiagonal A ↔ q.1 * q.2 = A := by simp [divisorsAntidiagonal]

@[simp]
theorem divisorsAntidiagonal_one : divisorsAntidiagonal (1 : (Ideal (𝓞 K))⁰) = {(1, 1)} := by
  classical
  ext q
  simp only [mem_divisorsAntidiagonal, Finset.mem_singleton]
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := mul_eq_one.mp (congrArg Subtype.val h)
    exact Prod.ext (Subtype.ext h1) (Subtype.ext h2)
  · rintro rfl
    simp

theorem fst_dvd_of_mem_divisorsAntidiagonal {A : (Ideal (𝓞 K))⁰}
    {q : (Ideal (𝓞 K))⁰ × (Ideal (𝓞 K))⁰} (hq : q ∈ divisorsAntidiagonal A) :
    (q.1 : Ideal (𝓞 K)) ∣ (A : Ideal (𝓞 K)) :=
  ⟨(q.2 : Ideal (𝓞 K)), by
    simpa using congrArg Subtype.val (mem_divisorsAntidiagonal.mp hq).symm⟩

section Convolution

variable {R : Type*} [CommSemiring R]

/-- Delta at the unit ideal, the identity for ideal convolution. -/
noncomputable def delta : (Ideal (𝓞 K))⁰ → R := by
  classical
  exact fun A ↦ if A = 1 then 1 else 0

/-- Ideal convolution, deliberately distinct from pointwise multiplication. -/
noncomputable def convolution (f g : (Ideal (𝓞 K))⁰ → R) : (Ideal (𝓞 K))⁰ → R :=
  fun A ↦ ∑ q ∈ divisorsAntidiagonal A, f q.1 * g q.2

@[simp]
theorem convolution_apply (f g : (Ideal (𝓞 K))⁰ → R) (A : (Ideal (𝓞 K))⁰) :
    convolution f g A = ∑ q ∈ divisorsAntidiagonal A, f q.1 * g q.2 := rfl

variable (K)

@[simp]
theorem normCoeff_delta : normCoeff K (delta : (Ideal (𝓞 K))⁰ → R) = 1 := by
  classical
  ext n
  by_cases hn : n = 1
  · subst n
    simp [delta]
  · simp only [normCoeff_apply, ArithmeticFunction.one_apply, if_neg hn]
    refine Finset.sum_eq_zero fun I hI ↦ ?_
    have hI1 : I ≠ 1 := by
      intro h
      apply hn
      simpa [h] using ((mem_normFiber K).mp hI).symm
    simp [delta, hI1]

/-- Regrouping by norm commutes with finite Dirichlet convolution. -/
theorem normCoeff_convolution (f g : (Ideal (𝓞 K))⁰ → R) :
    normCoeff K (convolution f g) = normCoeff K f * normCoeff K g := by
  classical
  ext n
  rcases n with _ | n
  · simp
  simp only [normCoeff_apply, convolution_apply, ArithmeticFunction.mul_apply,
    Finset.sum_mul_sum, Finset.sum_sigma']
  refine Finset.sum_nbij'
    (fun ⟨A, q⟩ ↦
      ⟨(absNorm (q.1 : Ideal (𝓞 K)), absNorm (q.2 : Ideal (𝓞 K))), ⟨q.1, q.2⟩⟩)
    (fun ⟨_d, ⟨B, C⟩⟩ ↦ ⟨B * C, (B, C)⟩) ?_ ?_ ?_ ?_ ?_ <;>
    simp only [Finset.mem_sigma, mem_normFiber, mem_divisorsAntidiagonal,
      Nat.mem_divisorsAntidiagonal] <;>
    aesop (add simp [map_mul])

end Convolution

open Classical in
/-- Squarefree ideals are determined by their finite set of prime factors. -/
theorem eq_of_squarefree_factors_eq {I J : Ideal (𝓞 K)} (hI : I ≠ 0) (hJ : J ≠ 0)
    (hsI : Squarefree I) (hsJ : Squarefree J)
    (h : (normalizedFactors I).toFinset = (normalizedFactors J).toFinset) : I = J := by
  classical
  have hfac : normalizedFactors I = normalizedFactors J := by
    rw [← ((squarefree_iff_nodup_normalizedFactors hI).mp hsI).dedup,
      ← ((squarefree_iff_nodup_normalizedFactors hJ).mp hsJ).dedup,
      ← Multiset.toFinset_val, ← Multiset.toFinset_val, h]
  exact associated_iff_eq.mp
    ((prod_normalizedFactors hI).symm.trans (by rw [hfac]; exact prod_normalizedFactors hJ))

/-- The ideal Möbius divisor sum vanishes off the unit ideal. -/
theorem sum_idealMobius_divisors_of_ne_one {A : (Ideal (𝓞 K))⁰} (hA : A ≠ 1) :
    ∑ q ∈ divisorsAntidiagonal A, idealMobius (q.1 : Ideal (𝓞 K)) = 0 := by
  classical
  have hA0 : (A : Ideal (𝓞 K)) ≠ 0 := nonZeroDivisors.coe_ne_zero A
  set P : Finset (Ideal (𝓞 K)) := (normalizedFactors (A : Ideal (𝓞 K))).toFinset with hPdef
  have hPne : P.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty, hPdef, Ne, Multiset.toFinset_eq_empty,
      normalizedFactors_eq_zero_iff hA0, Ideal.isUnit_iff]
    exact fun h ↦ hA (Subtype.ext (by simpa [Ideal.one_eq_top] using h))
  rw [← Finset.sum_filter_of_ne
    (p := fun q : (Ideal (𝓞 K))⁰ × (Ideal (𝓞 K))⁰ ↦ Squarefree (q.1 : Ideal (𝓞 K)))
    (fun q _ hq ↦ by
      by_contra h
      exact hq (idealMobius_of_not_squarefree h))]
  have hreindex :
      ∑ q ∈ (divisorsAntidiagonal A).filter (fun q ↦ Squarefree (q.1 : Ideal (𝓞 K))),
        idealMobius (q.1 : Ideal (𝓞 K)) = ∑ S ∈ P.powerset, (-1 : ℤ) ^ S.card := by
    refine Finset.sum_nbij (fun q ↦ (normalizedFactors (q.1 : Ideal (𝓞 K))).toFinset)
      ?_ ?_ ?_ ?_
    · intro q hq
      rw [Finset.mem_filter] at hq
      refine Finset.mem_powerset.mpr ?_
      rw [hPdef]
      exact Multiset.toFinset_subset.mpr (Multiset.subset_of_le
        ((dvd_iff_normalizedFactors_le_normalizedFactors
          (nonZeroDivisors.coe_ne_zero q.1) hA0).mp
          (fst_dvd_of_mem_divisorsAntidiagonal hq.1)))
    · intro q hq r hr hqr
      rw [Finset.mem_coe, Finset.mem_filter] at hq hr
      have h1 : q.1 = r.1 := Subtype.ext (eq_of_squarefree_factors_eq
        (nonZeroDivisors.coe_ne_zero q.1) (nonZeroDivisors.coe_ne_zero r.1) hq.2 hr.2 hqr)
      have h2 : q.2 = r.2 := by
        refine mul_left_cancel (a := q.1) ?_
        rw [mem_divisorsAntidiagonal.mp hq.1, ← mem_divisorsAntidiagonal.mp hr.1, h1]
      exact Prod.ext h1 h2
    · intro S hS
      rw [Finset.mem_coe, Finset.mem_powerset] at hS
      have hsub : S.val ⊆ normalizedFactors (A : Ideal (𝓞 K)) :=
        fun _ hx ↦ Multiset.mem_toFinset.mp (hS (Finset.mem_val.mp hx))
      have hB0 : S.val.prod ≠ 0 := Multiset.prod_ne_zero (by
        intro hz
        exact (prime_of_normalized_factor 0 (hsub hz)).ne_zero rfl)
      have hBfac : normalizedFactors S.val.prod = S.val :=
        normalizedFactors_prod_of_prime (fun Q hQ ↦ prime_of_normalized_factor Q (hsub hQ))
      obtain ⟨C, hC⟩ : S.val.prod ∣ (A : Ideal (𝓞 K)) :=
        (Multiset.prod_dvd_prod_of_le ((Multiset.le_iff_subset S.nodup).mpr hsub)).trans
          (prod_normalizedFactors hA0).dvd
      have hC0 : C ≠ 0 := by
        rintro rfl
        exact hA0 (by rw [hC, mul_zero])
      refine ⟨(⟨S.val.prod, mem_nonZeroDivisors_of_ne_zero hB0⟩,
        ⟨C, mem_nonZeroDivisors_of_ne_zero hC0⟩), ?_, ?_⟩
      · rw [Finset.mem_coe, Finset.mem_filter]
        refine ⟨mem_divisorsAntidiagonal.mpr (Subtype.ext (by simpa using hC.symm)), ?_⟩
        exact (squarefree_iff_nodup_normalizedFactors hB0).mpr (by rw [hBfac]; exact S.nodup)
      · change (normalizedFactors S.val.prod).toFinset = S
        rw [hBfac, Finset.val_toFinset]
    · intro q hq
      rw [Finset.mem_filter] at hq
      rw [idealMobius_of_squarefree hq.2,
        Multiset.toFinset_card_of_nodup
          ((squarefree_iff_nodup_normalizedFactors (nonZeroDivisors.coe_ne_zero q.1)).mp hq.2)]
  rw [hreindex]
  exact Finset.sum_powerset_neg_one_pow_card_of_nonempty hPne

/-- The ideal Möbius function is an inverse of one under ideal convolution. -/
theorem convolution_idealMobius_one {R : Type*} [CommRing R] :
    convolution (fun I : (Ideal (𝓞 K))⁰ ↦ (idealMobius (I : Ideal (𝓞 K)) : R))
      (fun _ ↦ 1) = delta := by
  classical
  funext A
  by_cases hA : A = 1
  · subst A
    simp [delta]
  · simp only [delta, if_neg hA, convolution_apply, mul_one, ← Int.cast_sum]
    rw [sum_idealMobius_divisors_of_ne_one hA, Int.cast_zero]

end IdealEuler

/-- The integer norm-fiber sum of the actual ideal Möbius function. -/
noncomputable def idealNormMobiusIntegerCoefficients (K : Type*) [Field K] [NumberField K] :
    ArithmeticFunction ℤ := IdealEuler.normCoeff K (fun I ↦ idealMobius (I : Ideal (𝓞 K)))

/-- Real ideal-norm Möbius coefficients, explicitly obtained by casting the
integer norm-fiber sums. -/
noncomputable def idealNormMobiusCoefficients (K : Type*) [Field K] [NumberField K] :
    ArithmeticFunction ℝ := (idealNormMobiusIntegerCoefficients K : ArithmeticFunction ℝ)

/-- The real inverse is still an explicit finite ideal Möbius sum. -/
theorem idealNormMobiusCoefficients_eq_normCoeff (K : Type*) [Field K] [NumberField K] :
    idealNormMobiusCoefficients K =
      IdealEuler.normCoeff K (fun I ↦ (idealMobius (I : Ideal (𝓞 K)) : ℝ)) := by
  ext n
  simp [idealNormMobiusCoefficients, idealNormMobiusIntegerCoefficients,
    ArithmeticFunction.intCoe_apply, IdealEuler.normCoeff_apply, Int.cast_sum]

@[simp]
theorem idealNormMobiusIntegerCoefficients_one (K : Type*) [Field K] [NumberField K] :
    idealNormMobiusIntegerCoefficients K 1 = 1 := by
  simp [idealNormMobiusIntegerCoefficients]

@[simp]
theorem idealNormMobiusCoefficients_one (K : Type*) [Field K] [NumberField K] :
    idealNormMobiusCoefficients K 1 = 1 := by
  simp [idealNormMobiusCoefficients]

theorem isMultiplicative_idealNormMobiusIntegerCoefficients
    (K : Type*) [Field K] [NumberField K] :
    (idealNormMobiusIntegerCoefficients K).IsMultiplicative := by
  refine IdealEuler.isMultiplicative_normCoeff K _ (by simp) fun A B h ↦ ?_
  exact idealMobius_mul (nonZeroDivisors.coe_ne_zero A) (nonZeroDivisors.coe_ne_zero B) h

theorem isMultiplicative_idealNormMobiusCoefficients (K : Type*) [Field K] [NumberField K] :
    (idealNormMobiusCoefficients K).IsMultiplicative :=
  (isMultiplicative_idealNormMobiusIntegerCoefficients K).intCast

/-- The explicit norm-fiber Möbius coefficients are a left Dirichlet inverse. -/
@[simp]
theorem idealNormMobiusCoefficients_mul_idealNormCoefficients
    (K : Type*) [Field K] [NumberField K] :
    idealNormMobiusCoefficients K * idealNormCoefficients K = 1 := by
  rw [idealNormMobiusCoefficients_eq_normCoeff, idealNormCoefficients_eq_normCoeff_one,
    ← IdealEuler.normCoeff_convolution, IdealEuler.convolution_idealMobius_one,
    IdealEuler.normCoeff_delta]

/-- The identity is the arithmetic delta `1`, not the constant zeta function. -/
@[simp]
theorem idealNormCoefficients_mul_idealNormMobiusCoefficients
    (K : Type*) [Field K] [NumberField K] :
    idealNormCoefficients K * idealNormMobiusCoefficients K = 1 := by
  rw [mul_comm, idealNormMobiusCoefficients_mul_idealNormCoefficients]

/-- Explicit finite norm-fiber formula for the integer inverse coefficients. -/
theorem idealNormMobiusIntegerCoefficients_apply
    (K : Type*) [Field K] [NumberField K] (n : ℕ) :
    idealNormMobiusIntegerCoefficients K n =
      ∑ I ∈ IdealEuler.normFiber K n, idealMobius (I : Ideal (𝓞 K)) := rfl

/-- Explicit finite norm-fiber formula for the real inverse coefficients. -/
theorem idealNormMobiusCoefficients_apply
    (K : Type*) [Field K] [NumberField K] (n : ℕ) :
    idealNormMobiusCoefficients K n =
      ∑ I ∈ IdealEuler.normFiber K n, (idealMobius (I : Ideal (𝓞 K)) : ℝ) := by
  rw [idealNormMobiusCoefficients_eq_normCoeff, IdealEuler.normCoeff_apply]

end Erdos975Support
