import Submission.WideConductorScales
import Submission.ReciprocalTotientTwo

/-!
# Grouping arbitrary rough moduli by primitive conductor

The completion of a conductor is bounded by a harmonic reciprocal-totient
sum. This retains all nontrivial conductors and does not assume distribution
at large moduli.
-/
open Nat Finset ArithmeticFunction Filter
open scoped Classical BigOperators
namespace Erdos821
open AnalyticSieve
set_option maxHeartbeats 3000000

lemma poolTotientMass_le_two_harmonic (D : Finset ℕ) (Q : ℕ)
    (hD : ∀ d ∈ D, 0 < d ∧ d ≤ Q) :
    poolTotientMass D ≤ 2*(harmonic Q : ℝ) := by
  apply le_trans _ (Sieve.sum_reciprocal_totient_le_two_harmonic Q)
  simp only [one_div]
  exact sum_le_sum_of_subset_of_nonneg
    (fun d hd => mem_Icc.mpr (hD d hd))
    (fun d _ _ => inv_nonneg.mpr (Nat.cast_nonneg _))

lemma reciprocal_totient_multiples_le (D : Finset ℕ) (Q c : ℕ)
    (hD : ∀ d ∈ D, 0 < d ∧ d ≤ Q) (hc : 0 < c) :
    (∑ d ∈ D.filter (fun d => c ∣ d), (d.totient : ℝ)⁻¹) ≤
      (c.totient : ℝ)⁻¹ * (2*(harmonic Q : ℝ)) := by
  let A := D.filter (fun d => c ∣ d)
  let B := A.image (fun d => d/c)
  have hq (d : ℕ) (hd : d ∈ A) : 0 < d/c ∧ d/c ≤ Q := by
    have hdD := (mem_filter.mp hd).1
    have hcd := (mem_filter.mp hd).2
    exact ⟨Nat.div_pos (Nat.le_of_dvd (hD d hdD).1 hcd) hc,
      (Nat.div_le_self d c).trans (hD d hdD).2⟩
  have hinj : Set.InjOn (fun d : ℕ => d/c) (↑A : Set ℕ) := by
    intro d hd e he h
    have hd' := Nat.mul_div_cancel' (mem_filter.mp hd).2
    have he' := Nat.mul_div_cancel' (mem_filter.mp he).2
    nlinarith [congrArg (fun a : ℕ => c*a) h]
  have hloc (d : ℕ) (hd : d ∈ A) :
      (d.totient : ℝ)⁻¹ ≤ (c.totient : ℝ)⁻¹*((d/c).totient : ℝ)⁻¹ := by
    have hφc : (0 : ℝ) < c.totient := by exact_mod_cast Nat.totient_pos.mpr hc
    have hφq : (0 : ℝ) < (d/c).totient := by exact_mod_cast Nat.totient_pos.mpr (hq d hd).1
    have hφ : (c.totient : ℝ)*((d/c).totient : ℝ) ≤ d.totient := by
      have h := Nat.totient_super_multiplicative c (d/c)
      rw [Nat.mul_div_cancel' (mem_filter.mp hd).2] at h
      exact_mod_cast h
    rw [← mul_inv]
    exact inv_anti₀ (mul_pos hφc hφq) hφ
  calc
    _ ≤ ∑ d ∈ A, (c.totient : ℝ)⁻¹*((d/c).totient : ℝ)⁻¹ := sum_le_sum hloc
    _ = (c.totient : ℝ)⁻¹ * poolTotientMass B := by
      unfold poolTotientMass B
      rw [sum_image hinj, mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (poolTotientMass_le_two_harmonic B Q (by
        intro e he
        obtain ⟨d,hd,rfl⟩ := mem_image.mp he
        exact hq d hd)) (inv_nonneg.mpr (Nat.cast_nonneg _))

/-- No factor-count bound is required: every nontrivial divisor is included. -/
theorem rough_conductor_majorant_le (D : Finset ℕ) (L Q N : ℕ)
    (hL : 2 ≤ L) (hD : ∀ d ∈ D, 0 < d ∧ d ≤ Q)
    (hrough : ∀ d ∈ D, ∀ c ∈ d.divisors.erase 1, L ≤ c) :
    (∑ d ∈ D, primitiveConductorMangoldtMajorant d N / d.totient) ≤
      (2*(harmonic Q : ℝ))*primitivePoolMean (Icc L Q) N := by
  let F : ℕ → ℝ := fun c => ∑ χ ∈ primitiveCharacters c, ‖twistedArithmeticSum χ vonMangoldt N‖
  have hF (c : ℕ) : 0 ≤ F c := sum_nonneg (fun _ _ => norm_nonneg _)
  have hdiv (d : ℕ) (hd : d ∈ D) :
      d.divisors.erase 1 = (Icc L Q).filter (fun c => c ∣ d) := by
    ext c
    simp only [mem_erase,mem_filter,mem_Icc,Nat.mem_divisors]
    constructor
    · rintro ⟨hc1,hcd,hd0⟩
      have hc := hrough d hd c (mem_erase.mpr ⟨hc1,Nat.mem_divisors.mpr ⟨hcd,hd0⟩⟩)
      exact ⟨⟨hc,(Nat.le_of_dvd (hD d hd).1 hcd).trans (hD d hd).2⟩,hcd⟩
    · rintro ⟨⟨hcL,hcQ⟩,hcd⟩
      exact ⟨by omega,hcd,(hD d hd).1.ne'⟩
  have heq : (∑ d ∈ D, primitiveConductorMangoldtMajorant d N / d.totient) =
      ∑ c ∈ Icc L Q, F c * ∑ d ∈ D.filter (fun d => c ∣ d), (d.totient : ℝ)⁻¹ := by
    calc
      _ = ∑ d ∈ D, ∑ c ∈ Icc L Q, if c ∣ d then F c/(d.totient : ℝ) else 0 := by
        apply sum_congr rfl
        intro d hd
        simp only [primitiveConductorMangoldtMajorant,hdiv d hd,sum_div,sum_filter,F,ite_div,zero_div]
      _ = ∑ c ∈ Icc L Q, ∑ d ∈ D, if c ∣ d then F c/(d.totient : ℝ) else 0 := sum_comm
      _ = _ := by
        apply sum_congr rfl
        intro c hc
        rw [← sum_filter,mul_sum]
        simp only [div_eq_mul_inv]
  rw [heq]
  calc
    _ ≤ ∑ c ∈ Icc L Q, F c*((c.totient : ℝ)⁻¹*(2*(harmonic Q : ℝ))) := by
      apply sum_le_sum
      intro c hc
      exact mul_le_mul_of_nonneg_left (reciprocal_totient_multiples_le D Q c hD
        (by have := (mem_Icc.mp hc).1; omega)) (hF c)
    _ = _ := by
      simp only [primitivePoolMean,mul_sum,div_eq_mul_inv,F]
      apply sum_congr rfl
      intro c hc
      ring

lemma bounded_pool_lift_error_le (D : Finset ℕ) (Q N : ℕ)
    (hD : ∀ d ∈ D, 0 < d ∧ d ≤ Q) :
    (∑ d ∈ D, (((d : ℝ)+1)*characterLiftError d N)/(d.totient : ℝ)) ≤
      2*((Q : ℝ)+1)*(harmonic Q : ℝ)*(Nat.log 2 N : ℝ)*Real.log Q := by
  let C : ℝ := ((Q : ℝ)+1)*(Nat.log 2 N : ℝ)*Real.log Q
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hloc (d : ℕ) (hd : d ∈ D) :
      (((d : ℝ)+1)*characterLiftError d N)/(d.totient : ℝ) ≤ C*(d.totient : ℝ)⁻¹ := by
    have hlift : characterLiftError d N ≤ (Nat.log 2 N : ℝ)*Real.log Q :=
      mul_le_mul_of_nonneg_left (log_nat_mono (hD d hd).2) (Nat.cast_nonneg _)
    have hdQ : (d : ℝ)+1 ≤ (Q : ℝ)+1 := by exact_mod_cast Nat.add_le_add_right (hD d hd).2 1
    rw [div_eq_mul_inv]
    apply mul_le_mul_of_nonneg_right _ (inv_nonneg.mpr (Nat.cast_nonneg _))
    dsimp [C]
    calc
      _ ≤ ((Q : ℝ)+1)*((Nat.log 2 N : ℝ)*Real.log Q) :=
        mul_le_mul hdQ hlift (characterLiftError_nonneg _ _) (by positivity)
      _ = _ := by ring
  calc
    _ ≤ ∑ d ∈ D, C*(d.totient : ℝ)⁻¹ := sum_le_sum hloc
    _ = C*poolTotientMass D := (mul_sum _ _ _).symm
    _ ≤ C*(2*(harmonic Q : ℝ)) :=
      mul_le_mul_of_nonneg_left (poolTotientMass_le_two_harmonic D Q hD) hC
    _ = _ := by dsimp [C]; ring

/-- A composite progression error estimate for an arbitrary rough modulus pool. -/
theorem rough_composite_error_le (D : Finset ℕ) (L Q N : ℕ)
    (hL : 2 ≤ L) (hD : ∀ d ∈ D, 0 < d ∧ d ≤ Q)
    (hrough : ∀ d ∈ D, ∀ c ∈ d.divisors.erase 1, L ≤ c) :
    (∑ d ∈ D, compositeProgressionError d N) ≤
      (2*(harmonic Q : ℝ))*primitivePoolMean (Icc L Q) N +
        2*((Q : ℝ)+1)*(harmonic Q : ℝ)*(Nat.log 2 N : ℝ)*Real.log Q := by
  simp only [compositeProgressionError,add_div,sum_add_distrib]
  exact _root_.add_le_add (rough_conductor_majorant_le D L Q N hL hD hrough)
    (bounded_pool_lift_error_le D Q N hD)

end Erdos821
