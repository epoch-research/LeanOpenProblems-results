import Submission.FiniteFourier

/-! Quadratic phases have flat linear Fourier spectra but maximal mixed four-term
AP correlation. This obstructs a naive ordinary-Fourier counting argument;
it is not a counterexample to the Erdős conjecture. -/
namespace Erdos3QuadraticFourAPBarrier
open Finset Erdos3FiniteFourier
open scoped BigOperators Classical ComplexConjugate
set_option maxHeartbeats 3000000

variable {G : Type*} [AddCommGroup G] [Fintype G]

noncomputable def complexCorr (f : G → ℂ) (t : G) : ℂ := 𝔼 x : G, f (x+t)*conj (f x)

lemma hat_complexCorr (f : G → ℂ) (ψ : AddChar G ℂ) :
    hat (complexCorr f) ψ = (‖hat f ψ‖^2 : ℝ) := by
  have hinner (x : G) : (𝔼 t : G, f (x+t)*conj (ψ t)) = ψ x*hat f ψ := by
    simpa only [hat,add_comm x] using hat_shift f x ψ
  have he : hat (complexCorr f) ψ = conj (hat f ψ)*hat f ψ := by
    unfold hat complexCorr
    simp_rw [expect_mul]
    rw [expect_comm]
    calc
      _ = 𝔼 x : G, conj (f x)*(𝔼 t : G, f (x+t)*conj (ψ t)) := by
        apply expect_congr rfl
        intro x _
        rw [mul_expect]
        apply expect_congr rfl
        intro t _
        ring
      _ = 𝔼 x : G, conj (f x)*(ψ x*hat f ψ) := by simp_rw [hinner]
      _ = (𝔼 x : G, conj (f x)*ψ x)*hat f ψ := by
        simp_rw [← mul_assoc]
        rw [← expect_mul]
      _ = _ := by
        congr 1
        rw [expect_conj]
        apply expect_congr rfl
        intro x _
        simp only [map_mul,starRingEnd_self_apply]
  rw [he,mul_comm,Complex.mul_conj,Complex.normSq_eq_norm_sq]

variable {F : Type*} [Field F] [Fintype F]

noncomputable def quadraticPhase (χ : AddChar F ℂ) (a : F) (x : F) : ℂ := χ (a*x^2)

lemma quadraticPhase_norm (χ : AddChar F ℂ) (a x : F) : ‖quadraticPhase χ a x‖ = 1 := χ.norm_apply _

lemma quadratic_derivative (χ : AddChar F ℂ) (a x t : F) :
    quadraticPhase χ a (x+t)*conj (quadraticPhase χ a x) =
      χ (a*t^2)*χ (x*(2*a*t)) := by
  unfold quadraticPhase
  rw [← char_sub,show a*(x+t)^2-a*x^2 = a*t^2+x*(2*a*t) by ring,χ.map_add_eq_mul]

lemma quadratic_complexCorr (χ : AddChar F ℂ) (hχ : χ.IsPrimitive)
    (h2 : (2 : F) ≠ 0) {a : F} (ha : a ≠ 0) (t : F) :
    complexCorr (quadraticPhase χ a) t = if t = 0 then 1 else 0 := by
  unfold complexCorr
  simp_rw [quadratic_derivative]
  rw [← mul_expect,Fintype.expect_eq_sum_div_card,AddChar.sum_mulShift _ hχ]
  by_cases ht : t = 0
  · subst t
    simp
  · have hn : 2*a*t ≠ 0 := mul_ne_zero (mul_ne_zero h2 ha) ht
    simp only [if_neg hn,if_neg ht,Nat.cast_zero,zero_div,mul_zero]

/-- Every linear Fourier coefficient of a nondegenerate quadratic phase has
squared norm exactly the reciprocal of the field size. -/
theorem quadratic_hat_norm_sq (χ : AddChar F ℂ) (hχ : χ.IsPrimitive)
    (h2 : (2 : F) ≠ 0) {a : F} (ha : a ≠ 0) (ψ : AddChar F ℂ) :
    ‖hat (quadraticPhase χ a) ψ‖^2 = 1/(Fintype.card F : ℝ) := by
  have hh := hat_complexCorr (quadraticPhase χ a) ψ
  have he : hat (complexCorr (quadraticPhase χ a)) ψ = 1/(Fintype.card F : ℂ) := by
    unfold hat
    simp_rw [quadratic_complexCorr χ hχ h2 ha]
    rw [Fintype.expect_eq_sum_div_card]
    simp
  rw [he] at hh
  apply Complex.ofReal_injective
  simpa only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_natCast] using hh.symm

noncomputable def fourAPAverage (f₀ f₁ f₂ f₃ : F → ℂ) : ℂ :=
  𝔼 x : F, 𝔼 d : F, f₀ x*f₁ (x+d)*f₂ (x+2*d)*f₃ (x+3*d)

lemma quadratic_four_term_identity (χ : AddChar F ℂ) (x d : F) :
    quadraticPhase χ 1 x*quadraticPhase χ (-3) (x+d)*
      quadraticPhase χ 3 (x+2*d)*quadraticPhase χ (-1) (x+3*d) = 1 := by
  unfold quadraticPhase
  rw [← χ.map_add_eq_mul,← χ.map_add_eq_mul,← χ.map_add_eq_mul,
    show 1*x^2+(-3)*(x+d)^2+3*(x+2*d)^2+(-1)*(x+3*d)^2 = 0 by ring,
    χ.map_zero_eq_one]

theorem quadratic_fourAPAverage (χ : AddChar F ℂ) :
    fourAPAverage (quadraticPhase χ 1) (quadraticPhase χ (-3))
      (quadraticPhase χ 3) (quadraticPhase χ (-1)) = 1 := by
  unfold fourAPAverage
  simp only [quadratic_four_term_identity,Fintype.expect_const]

/-- In every prime field of characteristic >3 there are four unit-bounded
functions with flat linear spectra and mixed four-term AP average equal to one. -/
theorem prime_field_fourier_barrier (p : ℕ) [Fact p.Prime] (hp : 3 < p) :
    ∃ f : Fin 4 → ZMod p → ℂ,
      (∀ i x, ‖f i x‖ = 1) ∧
      (∀ i (ψ : AddChar (ZMod p) ℂ), ‖hat (f i) ψ‖^2 = 1/(p : ℝ)) ∧
      fourAPAverage (f 0) (f 1) (f 2) (f 3) = 1 := by
  let χ : AddChar (ZMod p) ℂ := ZMod.stdAddChar
  let a : Fin 4 → ZMod p := ![1,-3,3,-1]
  have h2 : (2 : ZMod p) ≠ 0 := by
    exact (ZMod.natCast_eq_zero_iff 2 p).not.mpr (Nat.not_dvd_of_pos_of_lt (by decide) (by omega))
  have h3 : (3 : ZMod p) ≠ 0 := by
    exact (ZMod.natCast_eq_zero_iff 3 p).not.mpr (Nat.not_dvd_of_pos_of_lt (by decide) hp)
  have ha (i : Fin 4) : a i ≠ 0 := by fin_cases i <;> simp [a,h3]
  refine ⟨fun i ↦ quadraticPhase χ (a i),fun i x ↦ quadraticPhase_norm χ (a i) x,?_,?_⟩
  · intro i ψ
    simpa only [ZMod.card] using quadratic_hat_norm_sq χ (ZMod.isPrimitive_stdAddChar p) h2 (ha i) ψ
  · exact quadratic_fourAPAverage χ

/-- The linear Fourier coefficients in the preceding obstruction can be made
arbitrarily small, while the four-term correlation remains exactly one. -/
theorem arbitrarily_flat_fourAP {ε : ℝ} (hε : 0 < ε) :
    ∃ p : ℕ, ∃ hp : p.Prime,
      letI : Fact p.Prime := ⟨hp⟩
      ∃ f : Fin 4 → ZMod p → ℂ,
        (∀ i x, ‖f i x‖ = 1) ∧
        (∀ i (ψ : AddChar (ZMod p) ℂ), ‖hat (f i) ψ‖ ≤ ε) ∧
        fourAPAverage (f 0) (f 1) (f 2) (f 3) = 1 := by
  obtain ⟨p,hpBound,hp⟩ := Nat.exists_infinite_primes (⌈1/ε^2⌉₊+5)
  letI : Fact p.Prime := ⟨hp⟩
  have hp3 : 3 < p := by omega
  obtain ⟨f,hfn,hhat,havg⟩ := prime_field_fourier_barrier p hp3
  refine ⟨p,hp,f,hfn,?_,havg⟩
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hbound : 1/ε^2 ≤ (p : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast (show ⌈1/ε^2⌉₊ ≤ p by omega))
  have hrecip : 1/(p : ℝ) ≤ ε^2 := by
    apply (div_le_iff₀ hpR).mpr
    have hh := (div_le_iff₀ (sq_pos_of_pos hε)).mp hbound
    nlinarith
  intro i ψ
  have hh := (hhat i ψ).le.trans hrecip
  nlinarith [norm_nonneg (hat (f i) ψ)]

#print axioms quadratic_hat_norm_sq
#print axioms prime_field_fourier_barrier
#print axioms arbitrarily_flat_fourAP
end Erdos3QuadraticFourAPBarrier
