import Submission.KloostermanRingCompletion
import Submission.Sieve

/-!
# Interval Fourier mass with a gcd weight

For any positive modulus, the nonzero Fourier mass weighted by gcd is at
most q times the divisor count times the harmonic number H_(q-1).
-/
open Finset
open scoped Classical BigOperators
namespace Erdos821.Kloosterman
open Erdos821.AnalyticSieve

lemma gcd_reciprocal_sum_le (q : ℕ) (hq : q ≠ 0) :
    (∑ a ∈ Icc 1 (q-1), (Nat.gcd a q : ℕ)*(a : ℝ)⁻¹) ≤
      (q.divisors.card : ℝ)*(harmonic (q-1) : ℝ) := by
  have hpoint (a : ℕ) : (Nat.gcd a q : ℝ) ≤
      ∑ d ∈ q.divisors, if d ∣ a then (d : ℝ) else 0 := by
    have hm : Nat.gcd a q ∈ q.divisors := Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right _ _, hq⟩
    have hh := single_le_sum (s := q.divisors)
      (f := fun d => if d ∣ a then (d : ℝ) else 0) (fun _ _ => by positivity) hm
    simpa only [if_pos (Nat.gcd_dvd_left a q)] using hh
  calc
    _ ≤ ∑ a ∈ Icc 1 (q-1), (∑ d ∈ q.divisors, if d ∣ a then (d : ℝ) else 0)*(a : ℝ)⁻¹ := by
      exact sum_le_sum (fun a _ => mul_le_mul_of_nonneg_right (hpoint a) (by positivity))
    _ = ∑ d ∈ q.divisors, (d : ℝ)*∑ a ∈ Icc 1 (q-1) with d ∣ a, (a : ℝ)⁻¹ := by
      simp only [sum_mul, ite_mul, zero_mul, sum_filter, mul_sum, mul_ite, mul_zero]
      rw [sum_comm]
    _ ≤ ∑ _d ∈ q.divisors, (harmonic (q-1) : ℝ) := by
      apply sum_le_sum
      intro d hd
      have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mem_divisors hd).ne'
      calc
        _ ≤ (d : ℝ)*((d : ℝ)⁻¹*(harmonic (q-1) : ℝ)) :=
          mul_le_mul_of_nonneg_left
            (Erdos821.Sieve.sum_inv_multiples_le_harmonic (q-1) d (Nat.pos_of_mem_divisors hd))
            (Nat.cast_nonneg d)
        _ = _ := by rw [← mul_assoc, mul_inv_cancel₀ hd0, one_mul]
    _ = _ := by simp

lemma gcd_reciprocal_reflect_sum (q : ℕ) :
    (∑ a ∈ Icc 1 (q-1), (Nat.gcd a q : ℕ)*((q-a : ℕ) : ℝ)⁻¹) =
      ∑ a ∈ Icc 1 (q-1), (Nat.gcd a q : ℕ)*(a : ℝ)⁻¹ := by
  apply Finset.sum_bij (fun a _ => q-a)
  · intro a ha
    simp only [mem_Icc] at ha ⊢
    omega
  · intro a ha b hb hab
    simp only [mem_Icc] at ha hb
    omega
  · intro b hb
    refine ⟨q-b, ?_, ?_⟩
    · simp only [mem_Icc] at hb ⊢
      omega
    · simp only [mem_Icc] at hb
      omega
  · intro a ha
    rw [Nat.gcd_self_sub_left (by have := (mem_Icc.mp ha).2; omega)]

section PositiveModulus
variable {q : ℕ} [NeZero q]
noncomputable local instance ringIntervalDecidableEq : DecidableEq (ZMod q) := fun a b => Classical.propDecidable (a=b)

lemma ring_intervalResidueWeight_pairing (M : ℤ) (L : ℕ) (f : ZMod q → ℂ) :
    (∑ x : ZMod q, intervalResidueWeight q M L x * f x) =
      ∑ n ∈ range L, f ((M+n : ℤ) : ZMod q) := by
  simp only [intervalResidueWeight, sum_mul, ite_mul, one_mul, zero_mul]
  rw [sum_comm]
  simp

lemma ringFourier_intervalResidueWeight (M : ℤ) (L : ℕ) (t : ZMod q) :
    ringFourier ZMod.stdAddChar (intervalResidueWeight q M L) t =
      intervalWaveSum M L (((-t).val : ℝ)/q) := by
  rw [ringFourier, ring_intervalResidueWeight_pairing]
  unfold intervalWaveSum
  apply sum_congr rfl
  intro n _
  rw [mul_comm (-t), stdAddChar_int_mul]

lemma ring_intervalResidueWeight_mass (M : ℤ) (L : ℕ) :
    (∑ x : ZMod q, intervalResidueWeight q M L x) = (L : ℂ) := by
  have hh := ring_intervalResidueWeight_pairing (q := q) M L (fun _ => 1)
  simpa using hh

lemma sum_nonzero_residue_values (f : ℕ → ℝ) :
    (∑ t ∈ (univ : Finset (ZMod q)).erase 0, f t.val) =
      ∑ a ∈ Icc 1 (q-1), f a := by
  apply Finset.sum_bij (fun t _ => t.val)
  · intro t ht
    have ht0 : t ≠ 0 := (mem_erase.mp ht).1
    have hpos := Nat.pos_of_ne_zero ((ZMod.val_ne_zero t).mpr ht0)
    have hlt := t.val_lt
    simp only [mem_Icc]
    omega
  · intro a _ b _ hab
    exact ZMod.val_injective q hab
  · intro a ha
    have ha0 : a ≠ 0 := by have := (mem_Icc.mp ha).1; omega
    have haq : a < q := by have := (mem_Icc.mp ha).2; have := NeZero.pos q; omega
    refine ⟨(a : ZMod q), ?_, ZMod.val_natCast_of_lt haq⟩
    simp only [mem_erase, mem_univ, and_true]
    intro he
    have hv := congrArg ZMod.val he
    rw [ZMod.val_natCast_of_lt haq, ZMod.val_zero] at hv
    exact ha0 hv
  · intro _ _
    rfl

lemma sum_nonzero_residue_neg (f : ZMod q → ℝ) :
    (∑ t ∈ (univ : Finset (ZMod q)).erase 0, f (-t)) =
      ∑ t ∈ (univ : Finset (ZMod q)).erase 0, f t := by
  apply Finset.sum_bij (fun t _ => -t)
  · intro t ht
    simpa using ht
  · intro a _ b _ hab
    exact neg_injective hab
  · intro b hb
    exact ⟨-b, by simpa using hb, neg_neg b⟩
  · intro _ _
    rfl

lemma gcd_val_neg (t : ZMod q) : Nat.gcd (-t).val q = Nat.gcd t.val q := by
  by_cases ht : t=0
  · simp [ht]
  · letI : NeZero t := ⟨ht⟩
    rw [ZMod.val_neg_of_ne_zero, Nat.gcd_self_sub_left t.val_lt.le]

lemma gcd_val_mul_unit (t : ZMod q) (r : (ZMod q)ˣ) :
    Nat.gcd (t*(r : ZMod q)).val q = Nat.gcd t.val q := by
  have hr : (r : ZMod q).val.Coprime q := by
    apply (ZMod.isUnit_iff_coprime _ _).mp
    simpa only [ZMod.natCast_zmod_val] using r.isUnit
  rw [ZMod.val_mul, ← Nat.gcd_rec, Nat.gcd_comm q]
  exact hr.gcd_mul_right_cancel t.val

lemma nonzero_ringFourierMass_interval_le (M : ℤ) (L : ℕ) :
    (∑ t ∈ (univ : Finset (ZMod q)).erase 0,
      ‖ringFourier ZMod.stdAddChar (intervalResidueWeight q M L) t‖) ≤
        (q : ℝ)*(harmonic (q-1) : ℝ) := by
  simp_rw [ringFourier_intervalResidueWeight]
  rw [sum_nonzero_residue_neg (fun t => ‖intervalWaveSum M L ((t.val : ℝ)/q)‖),
    sum_nonzero_residue_values (fun a => ‖intervalWaveSum M L ((a : ℝ)/q)‖)]
  calc
    _ ≤ ∑ a ∈ Icc 1 (q-1), (q : ℝ)/2*((a : ℝ)⁻¹+((q-a : ℕ) : ℝ)⁻¹) := by
      apply sum_le_sum
      intro a ha
      have hq := NeZero.pos q
      have ha' := mem_Icc.mp ha
      exact norm_intervalWaveSum_rational_le (by omega) (by omega) M L
    _ = _ := by rw [← mul_sum, reciprocal_pair_sum]; ring

lemma ringFourierMass_interval_le (M : ℤ) (L : ℕ) :
    ringFourierMass ZMod.stdAddChar (intervalResidueWeight q M L) ≤
      (L : ℝ)+(q : ℝ)*(harmonic (q-1) : ℝ) := by
  have he := sum_erase_add univ (fun t : ZMod q =>
    ‖ringFourier ZMod.stdAddChar (intervalResidueWeight q M L) t‖) (mem_univ 0)
  dsimp only at he
  rw [ringFourier_zero, ring_intervalResidueWeight_mass, Complex.norm_natCast] at he
  rw [ringFourierMass, ← he]
  simpa only [add_comm] using add_le_add_right (nonzero_ringFourierMass_interval_le (q := q) M L) (L : ℝ)

/-- All nonzero frequencies, including nonunits, are covered by this bound. -/
theorem gcd_ringFourierMass_interval_le (M : ℤ) (L : ℕ) :
    (∑ t ∈ (univ : Finset (ZMod q)).erase 0,
      (Nat.gcd t.val q : ℕ)*‖ringFourier ZMod.stdAddChar (intervalResidueWeight q M L) t‖) ≤
        (q : ℝ)*q.divisors.card*(harmonic (q-1) : ℝ) := by
  simp_rw [ringFourier_intervalResidueWeight]
  have he : (∑ t ∈ (univ : Finset (ZMod q)).erase 0,
      (Nat.gcd t.val q : ℕ)*‖intervalWaveSum M L (((-t).val : ℝ)/q)‖) =
      ∑ t ∈ (univ : Finset (ZMod q)).erase 0,
        (Nat.gcd t.val q : ℕ)*‖intervalWaveSum M L ((t.val : ℝ)/q)‖ := by
    simpa only [gcd_val_neg] using sum_nonzero_residue_neg
      (fun t : ZMod q => (Nat.gcd t.val q : ℕ)*‖intervalWaveSum M L ((t.val : ℝ)/q)‖)
  rw [he, sum_nonzero_residue_values
    (fun a => (Nat.gcd a q : ℕ)*‖intervalWaveSum M L ((a : ℝ)/q)‖)]
  calc
    _ ≤ ∑ a ∈ Icc 1 (q-1), (Nat.gcd a q : ℕ)*
        ((q : ℝ)/2*((a : ℝ)⁻¹+((q-a : ℕ) : ℝ)⁻¹)) := by
      apply sum_le_sum
      intro a ha
      have hq := NeZero.pos q
      have ha' := mem_Icc.mp ha
      exact mul_le_mul_of_nonneg_left
        (norm_intervalWaveSum_rational_le (by omega) (by omega) M L) (by positivity)
    _ = (q : ℝ)*(∑ a ∈ Icc 1 (q-1), (Nat.gcd a q : ℕ)*(a : ℝ)⁻¹) := by
      simp_rw [mul_add, sum_add_distrib]
      have hdist : ∀ a : ℕ, (Nat.gcd a q : ℕ)*((q : ℝ)/2*(a : ℝ)⁻¹) =
          (q : ℝ)/2*((Nat.gcd a q : ℕ)*(a : ℝ)⁻¹) := by intro a; ring
      have hdist' : ∀ a : ℕ, (Nat.gcd a q : ℕ)*((q : ℝ)/2*((q-a : ℕ) : ℝ)⁻¹) =
          (q : ℝ)/2*((Nat.gcd a q : ℕ)*((q-a : ℕ) : ℝ)⁻¹) := by intro a; ring
      simp_rw [hdist, hdist', ← mul_sum, gcd_reciprocal_reflect_sum]
      ring
    _ ≤ _ := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
        (gcd_reciprocal_sum_le q (NeZero.ne q)) (Nat.cast_nonneg (α := ℝ) q)

end PositiveModulus
end Erdos821.Kloosterman
