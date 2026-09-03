import Submission.KloostermanHyperbola
import Submission.PeriodicCofactorMean

/-!
# Integer rectangle counts on a modular hyperbola

The Kloosterman completion estimate is stated here for actual integer pair
counts. The main term has the natural local factor (q-1)/q^2. This concerns
congruence counts, not primality of the products or their successors.
-/
open Finset
open scoped Classical BigOperators
namespace Erdos821.Kloosterman
open Erdos821.AnalyticSieve

variable {q : ℕ} [Fact q.Prime]
noncomputable local instance : DecidableEq (ZMod q) := fun a b => Classical.propDecidable (a=b)

lemma unit_intervalResidueWeight_pairing (M : ℤ) (B : ℕ) (f : ZMod q → ℂ) :
    (∑ u : (ZMod q)ˣ, intervalResidueWeight q M B u * f u) =
      ∑ i ∈ range B, if ((M+i : ℤ) : ZMod q)=0 then 0 else f ((M+i : ℤ) : ZMod q) := by
  calc
    _ = ∑ u : (ZMod q)ˣ, intervalResidueWeight q M B u *
        (if (u : ZMod q)=0 then 0 else f u) := by
      apply sum_congr rfl
      intro u _
      rw [if_neg u.ne_zero]
    _ = ∑ x : ZMod q, intervalResidueWeight q M B x *
        (if x=0 then 0 else f x) := by
      have hh := sum_units_add_zero (fun x : ZMod q =>
        intervalResidueWeight q M B x * (if x=0 then 0 else f x))
      simpa only [if_pos rfl, ite_true, mul_zero, add_zero] using hh
    _ = _ := intervalResidueWeight_pairing M B _

noncomputable def intervalUnitCount (q : ℕ) (M : ℤ) (B : ℕ) : ℕ :=
  ∑ i ∈ range B, if ((M+i : ℤ) : ZMod q)=0 then 0 else 1

noncomputable def rectangleCount (M N : ℤ) (B C : ℕ) (r : ZMod q) : ℕ :=
  ∑ i ∈ range B, ∑ j ∈ range C,
    if ((M+i : ℤ) : ZMod q)*((N+j : ℤ) : ZMod q)=r then 1 else 0

lemma unitMass_intervalResidueWeight (M : ℤ) (B : ℕ) :
    unitMass (intervalResidueWeight q M B) = (intervalUnitCount q M B : ℂ) := by
  have hh := unit_intervalResidueWeight_pairing (q := q) M B (fun _ => 1)
  simpa only [mul_one, unitMass, intervalUnitCount, Nat.cast_sum,
    Nat.cast_ite, Nat.cast_zero, Nat.cast_one] using hh

lemma hyperbolaWeight_eq_rectangleCount (M N : ℤ) (B C : ℕ) (r : ZMod q) (hr : r ≠ 0) :
    hyperbolaWeight (intervalResidueWeight q M B) (intervalResidueWeight q N C) r =
      (rectangleCount M N B C r : ℂ) := by
  rw [hyperbolaWeight, unit_intervalResidueWeight_pairing (q := q) M B
    (fun x : ZMod q => intervalResidueWeight q N C (r/x))]
  simp only [rectangleCount, Nat.cast_sum, Nat.cast_ite, Nat.cast_zero, Nat.cast_one]
  apply sum_congr rfl
  intro i _
  by_cases hi : ((M+i : ℤ) : ZMod q)=0
  · simp [hi, Ne.symm hr]
  · rw [if_neg hi]
    unfold intervalResidueWeight
    apply sum_congr rfl
    intro j _
    have he : ((N+j : ℤ) : ZMod q)=r/((M+i : ℤ) : ZMod q) ↔
        ((M+i : ℤ) : ZMod q)*((N+j : ℤ) : ZMod q)=r := by
      rw [eq_div_iff hi, mul_comm]
    simp only [he]

/-- A count estimate with the first interval's exact unit count. -/
theorem rectangleCount_error_units (M N : ℤ) (B C : ℕ) (r : ZMod q) (hr : r ≠ 0) :
    |(rectangleCount M N B C r : ℝ) - (C : ℝ)*intervalUnitCount q M B/q| ≤
      Real.sqrt (Real.sqrt (3*(q : ℝ)^3)) *
        ((B : ℝ)/q + (harmonic (q-1) : ℝ))*(harmonic (q-1) : ℝ) := by
  have hh := interval_hyperbola_error_le M N B C r hr
  rw [hyperbolaWeight_eq_rectangleCount M N B C r hr, unitMass_intervalResidueWeight] at hh
  simpa only [← Complex.ofReal_natCast, ← Complex.ofReal_mul, ← Complex.ofReal_div,
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using hh

lemma intervalUnitCount_error (M : ℤ) (B : ℕ) :
    |(intervalUnitCount q M B : ℝ)-((B : ℝ)-(B : ℝ)/q)| ≤ 1 := by
  let Z : ℝ := ∑ i ∈ range B, if ((M+i : ℤ) : ZMod q)=0 then (1 : ℝ) else 0
  have hp : (intervalUnitCount q M B : ℝ)+Z = B := by
    simp only [intervalUnitCount, Nat.cast_sum, Nat.cast_ite, Nat.cast_zero, Nat.cast_one, Z]
    rw [← sum_add_distrib]
    calc
      _ = ∑ _i ∈ range B, (1 : ℝ) := by
        apply sum_congr rfl
        intro i _
        split_ifs <;> norm_num
      _ = _ := by simp
  have hz := residue_prefix_range_error q B (-(M : ZMod q))
  have he (i : ℕ) : (i : ZMod q)=-(M : ZMod q) ↔ ((M+i : ℤ) : ZMod q)=0 := by
    push_cast
    constructor <;> intro h <;> linear_combination h
  simp_rw [he] at hz
  change |Z-(B : ℝ)/q| ≤ 1 at hz
  have heq : (intervalUnitCount q M B : ℝ)-((B : ℝ)-(B : ℝ)/q) = -(Z-(B : ℝ)/q) := by
    linarith only [hp]
  rw [heq, abs_neg]
  exact hz

noncomputable def rectangleError (q B C : ℕ) : ℝ :=
  Real.sqrt (Real.sqrt (3*(q : ℝ)^3)) *
    ((B : ℝ)/q+(harmonic (q-1) : ℝ))*(harmonic (q-1) : ℝ) + (C : ℝ)/q

/-- The local probability of a fixed nonzero product is (q-1)/q^2. -/
theorem rectangleCount_error_local (M N : ℤ) (B C : ℕ) (r : ZMod q) (hr : r ≠ 0) :
    |(rectangleCount M N B C r : ℝ) -
      (B : ℝ)*C*((q : ℝ)-1)/(q : ℝ)^2| ≤ rectangleError q B C := by
  have hq : (0 : ℝ) < q := by exact_mod_cast (Fact.out : q.Prime).pos
  have hU := intervalUnitCount_error (q := q) M B
  have he : (C : ℝ)*intervalUnitCount q M B/q - (B : ℝ)*C*((q : ℝ)-1)/(q : ℝ)^2 =
      (C : ℝ)/q*((intervalUnitCount q M B : ℝ)-((B : ℝ)-(B : ℝ)/q)) := by
    field_simp
  have hc : 0 ≤ (C : ℝ)/q := by positivity
  have hmain : |(C : ℝ)*intervalUnitCount q M B/q -
      (B : ℝ)*C*((q : ℝ)-1)/(q : ℝ)^2| ≤ (C : ℝ)/q := by
    rw [he, abs_mul, abs_of_nonneg hc]
    exact (mul_le_mul_of_nonneg_left hU hc).trans_eq (mul_one _)
  exact (abs_sub_le (rectangleCount M N B C r : ℝ)
    ((C : ℝ)*intervalUnitCount q M B/q) ((B : ℝ)*C*((q : ℝ)-1)/(q : ℝ)^2)).trans
      (add_le_add (rectangleCount_error_units M N B C r hr) hmain)

end Erdos821.Kloosterman
