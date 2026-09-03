import Submission.ExitDepthDecomposition
import Submission.RealChain

/-! A two-digit comparison retaining the first-level counts inside the test.
This is a local conditional-exit lemma, not an arithmetic covering result. -/
namespace Erdos7TwoDigitExitComparison
open scoped BigOperators
open Erdos7ConditionalExitMeasure
set_option autoImplicit false
set_option maxHeartbeats 2000000

lemma sum_chord {p : ℕ} (φ : ℝ → ℝ) (hφ : ConvexOn ℝ Set.univ φ)
    (hmφ : Monotone φ) (A T : ℝ) (hT : 0 ≤ T) (t : Fin p → ℝ)
    (ht : ∀ v, 0 ≤ t v ∧ t v ≤ T) (hmean : (∑ v, t v) ≤ T) :
    (∑ v, φ (A+t v)) ≤ ((p : ℝ)-1)*φ A+φ (A+T) := by
  let d := (φ (A+T)-φ A)/T
  have hd : 0 ≤ d := div_nonneg (sub_nonneg.mpr (hmφ (by linarith))) hT
  have hc : d*T=φ (A+T)-φ A := by
    by_cases h : T=0
    · simp [d,h]
    · dsimp [d]; field_simp
  calc
    _ ≤ ∑ v : Fin p, (φ A+d*t v) := by
      apply Finset.sum_le_sum
      intro v _
      exact Erdos7RealChain.convex_chord_majorant φ hφ A (t v) T (ht v).1 (ht v).2
    _ = (p : ℝ)*φ A+d*(∑ v, t v) := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, Finset.mul_sum]
    _ ≤ (p : ℝ)*φ A+d*T := by gcongr
    _ = _ := by rw [hc]; ring

lemma two_digit_raw_sum {p : ℕ} (stem exit : Fin p) (hne : exit ≠ stem)
    (F : Fin p → Fin p → ℝ) :
    (∑ y : Fin 2 → Fin p, (raw stem exit 2 y : ℝ)*F (y 0) (y 1)) =
      ((p-1 : ℕ) : ℝ)*(∑ v, F exit v)+
      ((p-1 : ℕ) : ℝ)*F stem exit+F stem stem := by
  rw [sum_digits_succ]
  simp_rw [sum_digits_succ]
  have he (d v : Fin p) (z : Fin 0 → Fin p) :
      (raw stem exit 2 (Fin.cons d (Fin.cons v z)) : ℝ)*
        F d v =
      (if d=stem then
        (if v=stem then F stem stem else if v=exit then ((p-1 : ℕ) : ℝ)*F stem exit else 0)
      else if d=exit then ((p-1 : ℕ) : ℝ)*F exit v else 0) := by
    by_cases hd : d=stem
    · subst d
      by_cases hv : v=stem
      · subst v; simp [raw]
      · by_cases hx : v=exit
        · subst v; simp [raw,hv]
        · simp [raw,hv,hx]
    · by_cases hx : d=exit
      · subst d; simp [raw,hd]
      · simp [raw,hd,hx]
  simp only [Fin.cons_zero, Fin.cons_one]
  simp_rw [he]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
    pow_zero, one_smul]
  have hsplit (d v : Fin p) :
      (if d=stem then
        (if v=stem then F stem stem else if v=exit then ((p-1 : ℕ) : ℝ)*F stem exit else 0)
      else if d=exit then ((p-1 : ℕ) : ℝ)*F exit v else 0) =
      (if d=stem then (if v=stem then F stem stem else 0)+
        (if v=exit then ((p-1 : ℕ) : ℝ)*F stem exit else 0) else 0)+
      (if d=exit then ((p-1 : ℕ) : ℝ)*F exit v else 0) := by
    by_cases hd : d=stem
    · subst d; by_cases hv : v=stem
      · subst v; simp [hne.symm]
      · simp [hv,hne.symm]
    · simp [hd]
  simp_rw [hsplit, Finset.sum_add_distrib, Finset.sum_ite_irrel]
  simp only [Finset.sum_const_zero, Finset.sum_add_distrib, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  rw [← Finset.mul_sum]
  ring

/-- Exact real integral identity for the first two digits. -/
theorem two_digit_density_sum {p : ℕ} (stem exit : Fin p) (hne : exit ≠ stem)
    (F : Fin p → Fin p → ℝ) :
    (∑ y : Fin 2 → Fin p, (density stem exit y : ℝ)*F (y 0) (y 1)) =
      (((p-1 : ℕ) : ℝ)*(∑ v, F exit v)+
        ((p-1 : ℕ) : ℝ)*F stem exit+F stem stem)/(p : ℝ)^2 := by
  have he (y : Fin 2 → Fin p) :
      (density stem exit y : ℝ)*F (y 0) (y 1) =
      ((raw stem exit 2 y : ℝ)*F (y 0) (y 1))/(p : ℝ)^2 := by
    simp only [density, Rat.cast_div, Rat.cast_pow, Rat.cast_natCast]
    ring
  simp_rw [he]
  rw [← Finset.sum_div, two_digit_raw_sum stem exit hne F]

/-- The first-level terminal and stem values stay inside the test; only the
uniform second digit after an immediate exit is compressed. -/
theorem two_digit_convex_bound {p : ℕ} (hp : 2 ≤ p)
    (stem exit : Fin p) (hne : exit ≠ stem)
    (φ : ℝ → ℝ) (hφ : ConvexOn ℝ Set.univ φ) (hmφ : Monotone φ)
    (A : ℝ) (f : Fin p → ℝ) (g : Fin p → Fin p → ℝ) (T : ℝ) (hT : 0 ≤ T)
    (hg : ∀ v, 0 ≤ g exit v ∧ g exit v ≤ T) (hmean : (∑ v, g exit v) ≤ T) :
    (∑ y : Fin 2 → Fin p, (density stem exit y : ℝ)*
      φ (A+f (y 0)+g (y 0) (y 1))) ≤
      (((p : ℝ)-1)^2*φ (A+f exit)+
        ((p : ℝ)-1)*φ (A+f exit+T)+
        ((p : ℝ)-1)*φ (A+f stem+g stem exit)+
        φ (A+f stem+g stem stem))/(p : ℝ)^2 := by
  rw [two_digit_density_sum stem exit hne (fun d v => φ (A+f d+g d v))]
  have hh := sum_chord φ hφ hmφ (A+f exit) T hT (g exit) hg hmean
  have hc : ((p-1 : ℕ) : ℝ)=(p : ℝ)-1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  rw [hc]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hp1 : 0 ≤ (p : ℝ)-1 := by
    have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
    linarith
  nlinarith [mul_le_mul_of_nonneg_left hh hp1]

#print axioms sum_chord
#print axioms two_digit_raw_sum
#print axioms two_digit_density_sum
#print axioms two_digit_convex_bound
end Erdos7TwoDigitExitComparison
