import Submission.QuadraticQuarticFive

/-! Constant-quartic-norm maps with a quadratic denominator that is not
inert at five. No representation-count bound is asserted. -/
namespace Erdos322Research.QuadraticQuarticFive
noncomputable section
open Polynomial
set_option Elab.async false
set_option maxHeartbeats 0

def denominator (d : ℤ) : Polynomial ℚ := X^2+C (d : ℚ)

lemma denominator_monic (d : ℤ) : (denominator d).Monic := by
  simpa [denominator] using (Polynomial.monic_X_pow_add_C (d : ℚ) (by decide : 2 ≠ 0))

lemma denominator_degree (d : ℤ) : (denominator d).natDegree=2 := by
  simpa [denominator] using
    (Polynomial.natDegree_X_pow_add_C (R := ℚ) (n := 2) (r := (d : ℚ)))

private def rootEval (d : ℤ) : Polynomial ℚ →ₐ[ℚ] QuadraticAlgebra ℚ (-(d : ℚ)) 0 :=
  Polynomial.aeval QuadraticAlgebra.omega

private lemma rootEval_denominator (d : ℤ) : rootEval d (denominator d)=0 := by
  apply QuadraticAlgebra.ext <;>
    simp [rootEval,denominator,pow_two,QuadraticAlgebra.omega_mul_omega_eq_mk]

private lemma denominator_dvd_of_root_zero (d : ℤ) (p : Polynomial ℚ)
    (h : rootEval d p=0) : denominator d ∣ p := by
  apply (Polynomial.modByMonic_eq_zero_iff_dvd (denominator_monic d)).mp
  let r := p %ₘ denominator d
  have hne : denominator d ≠ 1 := by
    intro hh
    have hh' := congrArg Polynomial.natDegree hh
    rw [denominator_degree,Polynomial.natDegree_one] at hh'
    omega
  have hr : r.natDegree≤1 := by
    have hh := Polynomial.natDegree_modByMonic_lt p (denominator_monic d) hne
    rw [denominator_degree] at hh
    dsimp [r]
    omega
  have he : rootEval d r=0 := by
    exact (Polynomial.eval₂_modByMonic_eq_self_of_root
      (denominator_monic d) (rootEval_denominator d)).trans h
  have hre := Polynomial.eq_X_add_C_of_natDegree_le_one hr
  rw [hre] at he
  have h0 : r.coeff 0=0 := by
    have hh := congrArg QuadraticAlgebra.re he
    simpa [rootEval] using hh
  have h1 : r.coeff 1=0 := by
    have hh := congrArg QuadraticAlgebra.im he
    simpa [rootEval] using hh
  change r=0
  rw [hre,h0,h1]
  simp

/-- Anisotropy removes a pole at either root of the quadratic denominator. -/
theorem denominator_dvd_all (d : ℤ) (hd : GoodFive d) (P : Fin 4 → Polynomial ℚ)
    (h : denominator d ∣ ∑ i, P i^4) : ∀ i, denominator d ∣ P i := by
  obtain ⟨Q,hQ⟩ := h
  have he : ∑ i, (rootEval d (P i))^4=0 := by
    have hh := congrArg (rootEval d) hQ
    simpa only [map_sum,map_pow,map_mul,rootEval_denominator,zero_mul] using hh
  exact fun i ↦ denominator_dvd_of_root_zero d (P i)
    (quadratic_algebra_fourth_sum_zero d hd _ he i)

/-- Arbitrary pole orders are removed coordinatewise. -/
theorem denominator_power_dvd_all (d : ℤ) (hd : GoodFive d) (m : ℕ)
    (P : Fin 4 → Polynomial ℚ) (h : denominator d^(4*m) ∣ ∑ i, P i^4) :
    ∀ i, denominator d^m ∣ P i := by
  induction m generalizing P with
  | zero => simp
  | succ m ih =>
    have hh : denominator d ∣ ∑ i, P i^4 :=
      (dvd_pow_self (denominator d) (by omega : 4*(m+1) ≠ 0)).trans h
    have hh' : ∀ i, ∃ Q : Polynomial ℚ, P i=denominator d*Q := denominator_dvd_all d hd P hh
    choose Q hQ using hh'
    have he : (∑ i, P i^4)=denominator d^4*(∑ i, Q i^4) := by
      simp only [hQ,mul_pow,Finset.mul_sum]
    have hcancel : denominator d^(4*m) ∣ ∑ i, Q i^4 := by
      rw [he,show 4*(m+1)=4+4*m by omega,pow_add] at h
      exact (mul_dvd_mul_iff_left (pow_ne_zero _ (denominator_monic d).ne_zero)).mp h
    have hi := ih Q hcancel
    intro i
    rw [hQ i,pow_succ']
    exact mul_dvd_mul_left _ (hi i)

theorem constant_coordinates {R : Type*} [CommRing R] [LinearOrder R]
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


/-- All constant-quartic-norm maps with this fixed quadratic pole divisor
are constant, without a degree restriction. -/
theorem denominator_rigidity (d : ℤ) (hd : GoodFive d)
    (P : Fin 4 → Polynomial ℚ) (a : ℚ) (m : ℕ)
    (h : ∑ i, P i^4=C a*denominator d^(4*m)) :
    ∃ b : Fin 4 → ℚ, ∀ i, P i=C (b i)*denominator d^m := by
  have hh : denominator d^(4*m) ∣ ∑ i, P i^4 := by rw [h]; exact dvd_mul_left _ _
  have hh' : ∀ i, ∃ Q : Polynomial ℚ, P i=denominator d^m*Q :=
    denominator_power_dvd_all d hd m P hh
  choose Q hQ using hh'
  have hpow : (denominator d^m)^4=denominator d^(4*m) := by
    rw [←pow_mul]
    congr 1
    omega
  have he : (∑ i, Q i^4)=C a := by
    simp_rw [hQ,mul_pow,hpow] at h
    rw [←Finset.mul_sum,mul_comm (C a)] at h
    exact mul_left_cancel₀ (pow_ne_zero _ (denominator_monic d).ne_zero) h
  have hc := constant_coordinates Q a he
  exact ⟨fun i ↦ (Q i).coeff 0,fun i ↦ by rw [hQ i,hc i,mul_comm]⟩

end
end Erdos322Research.QuadraticQuarticFive
