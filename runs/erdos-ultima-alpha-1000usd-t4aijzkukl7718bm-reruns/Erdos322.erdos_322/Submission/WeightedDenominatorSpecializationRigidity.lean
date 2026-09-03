import Submission.QuadraticDenominatorRigidity
import Submission.QuarticFormalSpecialization

/-! Specialization removes quadratic-in-one-variable poles over polynomial
coefficient rings. This is a rational-construction obstruction, not an
unrestricted representation-count estimate. -/
namespace Erdos322Research.WeightedDenominatorSpecializationRigidity
noncomputable section
open Polynomial
open QuadraticQuarticFive QuarticFormalSpecialization
set_option Elab.async false
set_option maxHeartbeats 0

/-- Divisibility by a monic polynomial can be checked by a jointly separating
family of coefficient specializations. -/
theorem monic_dvd_of_specializations {R S I : Type*} [CommRing R] [CommRing S]
    (f : I → R →+* S) (hf : ∀ r : R, (∀ i, f i r = 0) → r = 0)
    (p q : Polynomial R) (hq : q.Monic)
    (h : ∀ i, q.map (f i) ∣ p.map (f i)) : q ∣ p := by
  apply (modByMonic_eq_zero_iff_dvd hq).mp
  apply Polynomial.ext
  intro n
  simp only [coeff_zero]
  apply hf
  intro i
  have he : (p %ₘ q).map (f i) = 0 := by
    rw [map_modByMonic (f i) hq]
    exact (modByMonic_eq_zero_iff_dvd (hq.map (f i))).mpr (h i)
  have hh := congrArg (fun t : Polynomial S => t.coeff n) he
  simpa only [coeff_map, coeff_zero] using hh

/-- Pole removal for a quadratic polynomial over a coefficient ring, when
jointly separating specializations are good at five. -/
theorem denominator_power_dvd_of_specializations {R I : Type*} [CommRing R]
    (f : I → R →+* ℚ) (hf : ∀ r : R, (∀ i, f i r = 0) → r = 0)
    (D a : R) (d : I → ℤ) (hd : ∀ i, GoodFive (d i))
    (hD : ∀ i, f i D = (d i : ℚ)) (m : ℕ) (P : Fin 4 → Polynomial R)
    (h : ∑ j, P j^4 = C a*(X^2+C D)^(4*m)) :
    ∀ j, (X^2+C D)^m ∣ P j := by
  intro j
  apply monic_dvd_of_specializations f hf _ _
    ((monic_X_pow_add_C D (by decide : 2 ≠ 0)).pow m)
  intro i
  have he : ∑ j, (P j).map (f i)^4 =
      C (f i a)*denominator (d i)^(4*m) := by
    have hh := congrArg (Polynomial.mapRingHom (f i)) h
    simpa [denominator, hD i] using hh
  have hv : denominator (d i)^(4*m) ∣ ∑ j, (P j).map (f i)^4 := by
    rw [he]
    exact dvd_mul_left _ _
  have hj := denominator_power_dvd_all (d i) (hd i) m (fun j => (P j).map (f i)) hv j
  simpa [denominator, hD i] using hj

private theorem rational_anisotropic : FourthAnisotropic ℚ := by
  intro a h i
  have hle := Finset.single_le_sum (f := fun j : Fin 4 => a j^4)
    (fun _ _ => by positivity) (Finset.mem_univ i)
  rw [h] at hle
  have hz : a i^4 = 0 := le_antisymm hle (by positivity)
  exact eq_zero_of_pow_eq_zero hz

/-- For polynomial coefficient rings the remaining constant-norm coordinates
are constants, so all poles cancel completely. -/
theorem polynomial_denominator_rigidity {σ I : Type*}
    (f : I → MvPolynomial σ ℚ →+* ℚ)
    (hf : ∀ r : MvPolynomial σ ℚ, (∀ i, f i r = 0) → r = 0)
    (D : MvPolynomial σ ℚ) (d : I → ℤ)
    (hd : ∀ i, GoodFive (d i)) (hD : ∀ i, f i D = (d i : ℚ))
    (a : ℚ) (m : ℕ) (P : Fin 4 → Polynomial (MvPolynomial σ ℚ))
    (h : ∑ j, P j^4 = C (MvPolynomial.C a)*(X^2+C D)^(4*m)) :
    ∃ b : Fin 4 → ℚ, ∀ j,
      P j = C (MvPolynomial.C (b j))*(X^2+C D)^m := by
  have hdiv := denominator_power_dvd_of_specializations f hf D (MvPolynomial.C a)
    d hd hD m P h
  choose B hB using hdiv
  have hmon : (X^2+C D : Polynomial (MvPolynomial σ ℚ)).Monic :=
    monic_X_pow_add_C D (by decide : 2 ≠ 0)
  have he : ∑ j, B j^4 = C (MvPolynomial.C a) := by
    have hh := h
    simp only [hB, mul_pow, ← pow_mul, mul_comm m 4] at hh
    rw [← Finset.mul_sum, mul_comm (C (MvPolynomial.C a))] at hh
    exact mul_left_cancel₀ (pow_ne_zero _ hmon.ne_zero) hh
  have hc := polynomial_constant_norm (mvPolynomial_anisotropic rational_anisotropic)
    B (MvPolynomial.C a) he
  have he' : ∑ j, ((B j).coeff 0)^4 = MvPolynomial.C a := by
    have hh := congrArg (Polynomial.evalRingHom (0 : MvPolynomial σ ℚ)) he
    simpa only [map_sum, map_pow, coe_evalRingHom, eval_C, ← coeff_zero_eq_eval_zero] using hh
  have hc' := mvPolynomial_constant_norm rational_anisotropic
    (fun j => (B j).coeff 0) a he'
  dsimp only at hc'
  refine ⟨fun j => MvPolynomial.eval (fun _ => 0) ((B j).coeff 0), ?_⟩
  intro j
  rw [hB j, hc j, hc' j, mul_comm]


private theorem goodFive_add_twenty_five (d t : ℤ) (hd : GoodFive d) :
    GoodFive (d+25*t) := by
  rcases hd with ⟨r, hr, he⟩ | ⟨e, rfl, he⟩
  · left
    refine ⟨r, hr, ?_⟩
    simpa [show (25 : ZMod 5) = 0 by decide] using he
  · right
    refine ⟨e+5*t, by ring, ?_⟩
    intro hv
    apply he
    have hh := dvd_sub hv (dvd_mul_right (5 : ℤ) t)
    simpa using hh

private theorem goodFive_of_mod_twenty_five (d e : ℤ)
    (hd : GoodFive d) (h : (e : ZMod 25) = (d : ZMod 25)) : GoodFive e := by
  have hv : (25 : ℤ) ∣ e-d := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 25).mp
    simpa using sub_eq_zero.mpr h
  obtain ⟨t, ht⟩ := hv
  have he : e = d+25*t := by linarith
  rw [he]
  exact goodFive_add_twenty_five d t hd

private theorem grid_evaluation_congruent {σ : Type*} (D : MvPolynomial σ ℤ)
    (r a : σ → ℤ) :
    (MvPolynomial.eval (fun j => r j+25*a j) D : ZMod 25) =
      (MvPolynomial.eval r D : ZMod 25) := by
  let f : ℤ →+* ZMod 25 := Int.castRingHom (ZMod 25)
  have he : f.comp (MvPolynomial.eval (fun j => r j+25*a j)) =
      f.comp (MvPolynomial.eval r) := by
    apply MvPolynomial.ringHom_ext <;> intro j <;> simp [f, show (25 : ZMod 25) = 0 by decide]
  exact congrArg (fun g : MvPolynomial σ ℤ →+* ZMod 25 => g D) he

private def gridEvaluation {σ : Type*} (r a : σ → ℤ) :
    MvPolynomial σ ℚ →+* ℚ :=
  MvPolynomial.eval (fun j => ((r j+25*a j : ℤ) : ℚ))

private theorem grid_separates {σ : Type*} (r : σ → ℤ)
    (P : MvPolynomial σ ℚ) (h : ∀ a, gridEvaluation r a P = 0) : P = 0 := by
  let s (j : σ) : Set ℚ := Set.range (fun a : ℤ => ((r j+25*a : ℤ) : ℚ))
  have hs (j : σ) : (s j).Infinite := by
    apply Set.infinite_range_of_injective
    intro a b hab
    dsimp only at hab
    have hh : r j+25*a = r j+25*b := by exact_mod_cast hab
    omega
  apply MvPolynomial.funext_set s hs
  intro x hx
  have hx' : ∀ j, ∃ a : ℤ, ((r j+25*a : ℤ) : ℚ) = x j := by
    intro j
    exact hx j (Set.mem_univ j)
  choose a ha using hx'
  have he : (fun j => ((r j+25*a j : ℤ) : ℚ)) = x := funext ha
  simpa only [gridEvaluation, he, map_zero] using h a

private theorem grid_evaluation_map {σ : Type*} (D : MvPolynomial σ ℤ)
    (r a : σ → ℤ) :
    gridEvaluation r a (MvPolynomial.map (Int.castRingHom ℚ) D) =
      (MvPolynomial.eval (fun j => r j+25*a j) D : ℚ) := by
  let f : ℤ →+* ℚ := Int.castRingHom ℚ
  have he : (gridEvaluation r a).comp (MvPolynomial.map f) =
      f.comp (MvPolynomial.eval (fun j => r j+25*a j)) := by
    apply MvPolynomial.ringHom_ext <;> intro j <;> simp [gridEvaluation, f]
  exact congrArg (fun g : MvPolynomial σ ℤ →+* ℚ => g D) he

/-- A single good integral specialization suffices: arithmetic-progression
specializations form a separating grid. The polynomial `D` and the numerators
have no degree restriction. -/
theorem rigidity_of_one_good_specialization {σ : Type*}
    (D : MvPolynomial σ ℤ) (r : σ → ℤ)
    (hr : GoodFive (MvPolynomial.eval r D))
    (a : ℚ) (m : ℕ) (P : Fin 4 → Polynomial (MvPolynomial σ ℚ))
    (h : ∑ j, P j^4 = C (MvPolynomial.C a)*
      (X^2+C (MvPolynomial.map (Int.castRingHom ℚ) D))^(4*m)) :
    ∃ b : Fin 4 → ℚ, ∀ j, P j = C (MvPolynomial.C (b j))*
      (X^2+C (MvPolynomial.map (Int.castRingHom ℚ) D))^m := by
  apply polynomial_denominator_rigidity (gridEvaluation r) (grid_separates r)
    _ (fun u => MvPolynomial.eval (fun j => r j+25*u j) D) ?_ ?_ a m P h
  · intro u
    exact goodFive_of_mod_twenty_five _ _ hr (grid_evaluation_congruent D r u)
  · intro u
    exact grid_evaluation_map D r u

/-- Concrete weighted denominators `T^2+1+sum X_i^(e_i)` cannot yield
nonconstant constant-quartic-norm maps, for any number of variables and any
positive exponents. -/
theorem weighted_sum_denominator_rigidity {σ : Type*} [Fintype σ]
    (e : σ → ℕ) (he : ∀ j, 0 < e j)
    (a : ℚ) (m : ℕ) (P : Fin 4 → Polynomial (MvPolynomial σ ℚ))
    (h : ∑ j, P j^4 = C (MvPolynomial.C a)*
      (X^2+C (1+∑ j, MvPolynomial.X j^(e j)))^(4*m)) :
    ∃ b : Fin 4 → ℚ, ∀ j, P j = C (MvPolynomial.C (b j))*
      (X^2+C (1+∑ j, MvPolynomial.X j^(e j)))^m := by
  classical
  let D : MvPolynomial σ ℤ := 1+∑ j, MvPolynomial.X j^(e j)
  have hD : MvPolynomial.eval (fun _ => (0 : ℤ)) D = 1 := by
    simp [D, ne_of_gt (he _)]
  have hg : GoodFive (MvPolynomial.eval (fun _ => (0 : ℤ)) D) := by
    rw [hD]
    exact Or.inl ⟨2, by decide, by decide⟩
  have hmap : MvPolynomial.map (Int.castRingHom ℚ) D =
      1+∑ j, (MvPolynomial.X j : MvPolynomial σ ℚ)^(e j) := by simp [D]
  have hh := rigidity_of_one_good_specialization D (fun _ => 0) hg a m P
  rw [hmap] at hh
  exact hh h

end
end Erdos322Research.WeightedDenominatorSpecializationRigidity
