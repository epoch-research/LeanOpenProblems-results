import Submission.DivisorBound

/-! Exact divisor bounds for two aligned fourth-power differences.
These will be used in a full second-moment estimate, not as a pointwise
subpolynomial estimate for the four-variable representation count. -/
namespace Erdos322Research.QuarticDifferenceFibers

open Finset
set_option Elab.async false

/-- Signed divisors, excluding zero. -/
def signedDivisors (D : ℤ) : Finset ℤ :=
  (D.natAbs.divisors.image (fun n : ℕ => (n : ℤ))) ∪
  (D.natAbs.divisors.image (fun n : ℕ => -(n : ℤ)))

lemma mem_signedDivisors {h D : ℤ} (hD : D ≠ 0) (hh : h ∣ D) :
    h ∈ signedDivisors D := by
  have hm : h.natAbs ∈ D.natAbs.divisors :=
    Nat.mem_divisors.mpr ⟨Int.natAbs_dvd_natAbs.mpr hh,Int.natAbs_ne_zero.mpr hD⟩
  by_cases hpos : 0 ≤ h
  · apply Finset.mem_union_left
    exact Finset.mem_image.mpr ⟨h.natAbs,hm,by simp [abs_of_nonneg hpos]⟩
  · apply Finset.mem_union_right
    exact Finset.mem_image.mpr ⟨h.natAbs,hm,by simp [abs_of_neg (lt_of_not_ge hpos)]⟩

lemma card_signedDivisors (D : ℤ) : (signedDivisors D).card ≤ 2*D.natAbs.divisors.card := by
  exact (Finset.card_union_le _ _).trans (by
    have h1 := Finset.card_image_le (s := D.natAbs.divisors) (f := fun n : ℕ => (n : ℤ))
    have h2 := Finset.card_image_le (s := D.natAbs.divisors) (f := fun n : ℕ => -(n : ℤ))
    omega)

def aligned (a : Fin 4 → ℕ) : Prop :=
  (a 0 : ℤ)-(a 1 : ℤ)=(a 2 : ℤ)-(a 3 : ℤ)

def difference (a : Fin 4 → ℕ) : ℤ :=
  (a 0 : ℤ)^4-(a 1 : ℤ)^4-(a 2 : ℤ)^4+(a 3 : ℤ)^4

def steps (a : Fin 4 → ℕ) : ℤ × ℤ :=
  ((a 0 : ℤ)-(a 1 : ℤ),(a 0 : ℤ)-(a 2 : ℤ))

/-- A centered factorization with a positive quadratic factor. -/
theorem difference_factorization (a : Fin 4 → ℕ) (ha : aligned a) :
    difference a=(steps a).1*(steps a).2*
      (3*((a 0 : ℤ)+(a 3 : ℤ))^2+(steps a).1^2+(steps a).2^2) := by
  dsimp [aligned] at ha
  have he : (a 0 : ℤ)=(a 1 : ℤ)+(a 2 : ℤ)-(a 3 : ℤ) := by omega
  dsimp [difference,steps]
  rw [he]
  ring

/-- The only zero differences are the two diagonal configurations. -/
theorem zero_difference_iff (a : Fin 4 → ℕ) (ha : aligned a) :
    difference a=0 ↔
      (a 0=a 1 ∧ a 2=a 3) ∨ (a 0=a 2 ∧ a 1=a 3) := by
  constructor
  · intro hz
    rw [difference_factorization a ha] at hz
    have h : (steps a).1=0 ∨ (steps a).2=0 := by
      rcases mul_eq_zero.mp hz with h | h
      · exact mul_eq_zero.mp h
      · have hh := sq_nonneg ((a 0 : ℤ)+(a 3 : ℤ))
        have h1 := sq_nonneg (steps a).1
        have h2 := sq_nonneg (steps a).2
        left
        nlinarith
    dsimp [steps,aligned] at h ha
    rcases h with h | h
    · left; constructor <;> omega
    · right; constructor <;> omega
  · rintro (⟨h0,h2⟩ | ⟨h0,h1⟩)
    · simp [difference,h0,h2]
    · simp [difference,h0,h1]

/-- On a fixed nonzero difference fiber the two signed steps determine all
four nonnegative coordinates, not merely a bounded number of possibilities. -/
theorem steps_injective_on_fiber (D : ℤ) (hD : D ≠ 0)
    (a b : Fin 4 → ℕ) (ha : aligned a) (hb : aligned b)
    (haD : difference a=D) (hbD : difference b=D) (hab : steps a=steps b) : a=b := by
  have haF := difference_factorization a ha
  have hbF := difference_factorization b hb
  rw [haD] at haF
  rw [hbD,← hab] at hbF
  have hprod : (steps a).1*(steps a).2 ≠ 0 := by
    intro hz
    rw [hz,zero_mul] at haF
    exact hD haF
  have hm := mul_left_cancel₀ hprod (haF.symm.trans hbF)
  have he : ((a 0 : ℤ)+(a 3 : ℤ))^2=((b 0 : ℤ)+(b 3 : ℤ))^2 := by nlinarith
  have hmid : (a 0 : ℤ)+(a 3 : ℤ)=(b 0 : ℤ)+(b 3 : ℤ) := by
    nlinarith [show (0 : ℤ) ≤ (a 0 : ℤ)+(a 3 : ℤ) by positivity,
      show (0 : ℤ) ≤ (b 0 : ℤ)+(b 3 : ℤ) by positivity]
  have hh := congrArg Prod.fst hab
  have hu := congrArg Prod.snd hab
  dsimp [steps,aligned] at hh hu ha hb
  funext i
  fin_cases i
  · change a 0=b 0
    omega
  · change a 1=b 1
    omega
  · change a 2=b 2
    omega
  · change a 3=b 3
    omega

/-- Every finite nonzero aligned-difference fiber has at most
`4 * tau(abs D)^2` points, uniformly without a box or coefficient condition. -/
theorem nonzero_fiber_bound (D : ℤ) (hD : D ≠ 0) (S : Finset (Fin 4 → ℕ))
    (hS : ∀ a ∈ S, aligned a ∧ difference a=D) :
    S.card ≤ 4*D.natAbs.divisors.card^2 := by
  classical
  have hc := Finset.card_le_card_of_injOn steps
    (s := S) (t := signedDivisors D ×ˢ signedDivisors D)
    (by
      intro a ha
      obtain ⟨hal,haD⟩ := hS a ha
      have hf := difference_factorization a hal
      rw [haD] at hf
      apply Finset.mem_product.mpr
      constructor
      · apply mem_signedDivisors hD
        rw [hf]
        exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _
      · apply mem_signedDivisors hD
        rw [hf]
        exact dvd_mul_of_dvd_left (dvd_mul_left _ _) _)
    (by
      intro a ha b hb hab
      exact steps_injective_on_fiber D hD a b (hS a ha).1 (hS b hb).1
        (hS a ha).2 (hS b hb).2 hab)
  have hs := card_signedDivisors D
  simp only [Finset.card_product] at hc
  nlinarith

end Erdos322Research.QuarticDifferenceFibers
