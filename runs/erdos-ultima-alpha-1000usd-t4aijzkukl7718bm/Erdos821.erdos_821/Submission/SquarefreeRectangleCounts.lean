import Submission.IntervalFourierGcd
import Submission.CofactorPrincipalCount

/-!
# Modular rectangle estimates for squarefree moduli

The main term uses phi(q)/q^2. Both interval lengths are unrestricted;
nonunit Fourier frequencies and the local coprimality density are retained.
-/
open Finset
open scoped Classical BigOperators
namespace Erdos821.Kloosterman
open Erdos821.AnalyticSieve

variable {q : ℕ} [NeZero q]
noncomputable local instance squarefreeRectangleDecidableEq : DecidableEq (ZMod q) :=
  fun a b => Classical.propDecidable (a=b)

lemma ringWeightedKloosterman_interval_norm (hq : Squarefree q)
    (M : ℤ) (B : ℕ) (a b : ZMod q) :
    ‖ringWeightedKloosterman ZMod.stdAddChar (intervalResidueWeight q M B) a b‖ ≤
      squarefreeBound q * ((B : ℝ)/q+(harmonic (q-1) : ℝ)) * (Nat.gcd b.val q : ℕ) := by
  have hh := ringWeightedKloosterman_norm_le_of_bound ZMod.stdAddChar
    (ZMod.isPrimitive_stdAddChar q) (intervalResidueWeight q M B) a b
    (squarefreeBound q*(Nat.gcd b.val q : ℕ))
    (fun _ => ringKloosterman_squarefree_norm q hq _ (ZMod.isPrimitive_stdAddChar q) _ b)
  rw [ZMod.card] at hh
  have hqR : (0 : ℝ)<q := by exact_mod_cast NeZero.pos q
  apply (mul_le_mul_iff_right₀ hqR).mp
  calc
    _ ≤ squarefreeBound q*(Nat.gcd b.val q : ℕ)*ringFourierMass ZMod.stdAddChar
        (intervalResidueWeight q M B) := hh
    _ ≤ squarefreeBound q*(Nat.gcd b.val q : ℕ)*
        ((B : ℝ)+(q : ℝ)*(harmonic (q-1) : ℝ)) :=
      mul_le_mul_of_nonneg_left (ringFourierMass_interval_le M B)
        (mul_nonneg (squarefreeBound_nonneg q) (by positivity))
    _ = _ := by field_simp

lemma squarefree_interval_hyperbola_error (hq : Squarefree q)
    (M N : ℤ) (B C : ℕ) (r : (ZMod q)ˣ) :
    ‖ringHyperbolaWeight (intervalResidueWeight q M B) (intervalResidueWeight q N C) r -
      (C : ℂ)*ringUnitMass (intervalResidueWeight q M B)/(q : ℂ)‖ ≤
      squarefreeBound q * ((B : ℝ)/q+(harmonic (q-1) : ℝ)) *
        q.divisors.card * (harmonic (q-1) : ℝ) := by
  let K := squarefreeBound q * ((B : ℝ)/q+(harmonic (q-1) : ℝ))
  have hH : 0 ≤ (harmonic (q-1) : ℝ) := by
    by_cases hh : q-1=0
    · simp [hh]
    · exact_mod_cast (harmonic_pos hh).le
  have hK : 0 ≤ K := mul_nonneg (squarefreeBound_nonneg q)
    (add_nonneg (div_nonneg (Nat.cast_nonneg B) (Nat.cast_nonneg q)) hH)
  have hh := ringHyperbolaWeight_error_norm_le ZMod.stdAddChar (ZMod.isPrimitive_stdAddChar q)
    (intervalResidueWeight q M B) (intervalResidueWeight q N C) r
    (fun t => K*(Nat.gcd t.val q : ℕ)) (by
      intro t _
      simpa only [gcd_val_mul_unit] using ringWeightedKloosterman_interval_norm hq M B 0 (t*r))
  rw [ZMod.card, ring_intervalResidueWeight_mass] at hh
  have he : (∑ t ∈ (univ : Finset (ZMod q)).erase 0,
      K*(Nat.gcd t.val q : ℕ)*‖ringFourier ZMod.stdAddChar (intervalResidueWeight q N C) t‖) =
      K * ∑ t ∈ (univ : Finset (ZMod q)).erase 0,
        (Nat.gcd t.val q : ℕ)*‖ringFourier ZMod.stdAddChar (intervalResidueWeight q N C) t‖ := by
    simp only [mul_sum, mul_assoc]
  rw [he] at hh
  have hb := hh.trans (mul_le_mul_of_nonneg_left (gcd_ringFourierMass_interval_le N C) hK)
  have hqR : (0 : ℝ)<q := by exact_mod_cast NeZero.pos q
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne q
  apply (mul_le_mul_iff_right₀ hqR).mp
  calc
    _ = ‖(q : ℂ)*ringHyperbolaWeight (intervalResidueWeight q M B)
          (intervalResidueWeight q N C) r - (C : ℂ)*ringUnitMass (intervalResidueWeight q M B)‖ := by
      rw [← Complex.norm_natCast, ← norm_mul]
      congr 1
      field_simp
    _ ≤ K*((q : ℝ)*q.divisors.card*(harmonic (q-1) : ℝ)) := hb
    _ = _ := by dsimp [K]; ring

lemma ring_unit_interval_pairing (M : ℤ) (B : ℕ) (f : ZMod q → ℂ) :
    (∑ u : (ZMod q)ˣ, intervalResidueWeight q M B u * f u) =
      ∑ i ∈ range B, if IsUnit (((M+i : ℤ) : ZMod q)) then f ((M+i : ℤ) : ZMod q) else 0 := by
  calc
    _ = ∑ u : (ZMod q)ˣ, intervalResidueWeight q M B u *
        (if IsUnit (u : ZMod q) then f u else 0) := by
      apply sum_congr rfl
      intro u _
      rw [if_pos u.isUnit]
    _ = ∑ x : ZMod q, intervalResidueWeight q M B x *
        (if IsUnit x then f x else 0) := by
      symm
      have ht := sum_eq_sum_units (q := q) (fun x => intervalResidueWeight q M B x *
        (if IsUnit x then f x else 0)) (by intro x hx; simp only [if_neg hx, mul_zero])
      apply ht.trans
      apply sum_congr (by ext u; simp)
      intro _ _
      rfl
    _ = _ := ring_intervalResidueWeight_pairing M B _

noncomputable def ringIntervalUnitCount (q : ℕ) (M : ℤ) (B : ℕ) : ℕ :=
  ∑ i ∈ range B, if IsUnit (((M+i : ℤ) : ZMod q)) then 1 else 0

noncomputable def ringRectangleCount (q : ℕ) (M N : ℤ) (B C : ℕ) (r : ZMod q) : ℕ :=
  ∑ i ∈ range B, ∑ j ∈ range C,
    if ((M+i : ℤ) : ZMod q)*((N+j : ℤ) : ZMod q)=r then 1 else 0

lemma ringUnitMass_interval (M : ℤ) (B : ℕ) :
    ringUnitMass (intervalResidueWeight q M B) = (ringIntervalUnitCount q M B : ℂ) := by
  have hh := ring_unit_interval_pairing (q := q) M B (fun _ => 1)
  simpa only [mul_one, ringUnitMass, ringIntervalUnitCount, Nat.cast_sum,
    Nat.cast_ite, Nat.cast_zero, Nat.cast_one] using hh

lemma ringHyperbolaWeight_eq_rectangleCount (M N : ℤ) (B C : ℕ) (r : (ZMod q)ˣ) :
    ringHyperbolaWeight (intervalResidueWeight q M B) (intervalResidueWeight q N C) r =
      (ringRectangleCount q M N B C r : ℂ) := by
  have he : ringHyperbolaWeight (intervalResidueWeight q M B) (intervalResidueWeight q N C) r =
      ∑ u : (ZMod q)ˣ, intervalResidueWeight q M B u * intervalResidueWeight q N C ((r : ZMod q)*(u : ZMod q)⁻¹) := by
    simp only [ringHyperbolaWeight, ZMod.inv_coe_unit]
  rw [he, ring_unit_interval_pairing (q := q) M B
    (fun x => intervalResidueWeight q N C ((r : ZMod q)*x⁻¹))]
  simp only [ringRectangleCount, Nat.cast_sum, Nat.cast_ite, Nat.cast_zero, Nat.cast_one]
  apply sum_congr rfl
  intro i _
  let x : ZMod q := ((M+i : ℤ) : ZMod q)
  by_cases hi : IsUnit x
  · rw [if_pos hi]
    unfold intervalResidueWeight
    apply sum_congr rfl
    intro j _
    have heq (y : ZMod q) : y=(r : ZMod q)*x⁻¹ ↔ x*y=r := by
      constructor
      · intro hy
        rw [hy, mul_left_comm, ZMod.mul_inv_of_unit x hi, mul_one]
      · intro hy
        calc
          y = (x⁻¹*x)*y := by rw [ZMod.inv_mul_of_unit x hi, one_mul]
          _ = (r : ZMod q)*x⁻¹ := by rw [mul_assoc, hy, mul_comm]
    split_ifs with h₁ h₂ h₂
    · rfl
    · exact False.elim (h₂ ((heq _).mp h₁))
    · exact False.elim (h₁ ((heq _).mpr h₂))
    · rfl
  · rw [if_neg hi]
    symm
    apply sum_eq_zero
    intro j _
    have hnot : x*((N+j : ℤ) : ZMod q) ≠ r := by
      intro hxy
      apply hi
      apply IsUnit.of_mul_eq_one (((N+j : ℤ) : ZMod q)*(↑(r⁻¹) : ZMod q))
      rw [← mul_assoc, hxy, r.mul_inv]
    exact if_neg hnot

lemma ringRectangleCount_error_units (hq : Squarefree q) (M N : ℤ) (B C : ℕ) (r : (ZMod q)ˣ) :
    |(ringRectangleCount q M N B C r : ℝ)-(C : ℝ)*ringIntervalUnitCount q M B/q| ≤
      squarefreeBound q*((B : ℝ)/q+(harmonic (q-1) : ℝ))*q.divisors.card*(harmonic (q-1) : ℝ) := by
  have hh := squarefree_interval_hyperbola_error hq M N B C r
  rw [ringHyperbolaWeight_eq_rectangleCount, ringUnitMass_interval] at hh
  simpa only [← Complex.ofReal_natCast, ← Complex.ofReal_mul, ← Complex.ofReal_div,
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using hh

lemma ringIntervalUnitCount_eq_coprime (M : ℤ) (B : ℕ) :
    ringIntervalUnitCount q M B =
      coprimeCofactorCount q ((M-1 : ZMod q).val) ((M-1 : ZMod q).val+B) := by
  let A := (M-1 : ZMod q).val
  have hA : (A : ZMod q)=(M : ZMod q)-1 := ZMod.natCast_zmod_val _
  have hset : Icc (A+1) (A+B) = Ico (A+1) (A+B+1) := by
    ext n
    simp only [mem_Icc, mem_Ico]
    omega
  change _ = ((Icc (A+1) (A+B)).filter (fun a => a.Coprime q)).card
  rw [card_filter, hset, sum_Ico_eq_sum_range]
  rw [show A+B+1-(A+1)=B by omega]
  unfold ringIntervalUnitCount
  apply sum_congr rfl
  intro i _
  have he : ((A+1+i : ℕ) : ZMod q)=((M+i : ℤ) : ZMod q) := by
    push_cast
    rw [hA]
    ring
  simp only [← ZMod.isUnit_iff_coprime, he]
  split_ifs <;> rfl

lemma ringIntervalUnitCount_density_error (M : ℤ) (B : ℕ) :
    |(ringIntervalUnitCount q M B : ℝ)-(B : ℝ)*q.totient/q| ≤
      (3 : ℝ)^q.primeFactors.card := by
  rw [ringIntervalUnitCount_eq_coprime]
  simpa only [Nat.add_sub_cancel_left] using coprimeCofactorCount_density_error q
    ((M-1 : ZMod q).val) ((M-1 : ZMod q).val+B) (NeZero.pos q)

noncomputable def squarefreeRectangleError (q B C : ℕ) : ℝ :=
  squarefreeBound q*((B : ℝ)/q+(harmonic (q-1) : ℝ))*q.divisors.card*(harmonic (q-1) : ℝ) +
    (C : ℝ)/q*(3 : ℝ)^q.primeFactors.card

theorem ringRectangleCount_error_local (hq : Squarefree q)
    (M N : ℤ) (B C : ℕ) (r : (ZMod q)ˣ) :
    |(ringRectangleCount q M N B C r : ℝ) -
      (B : ℝ)*C*q.totient/(q : ℝ)^2| ≤ squarefreeRectangleError q B C := by
  have hqR : (0 : ℝ)<q := by exact_mod_cast NeZero.pos q
  have hU := ringIntervalUnitCount_density_error (q := q) M B
  have he : (C : ℝ)*ringIntervalUnitCount q M B/q - (B : ℝ)*C*q.totient/(q : ℝ)^2 =
      (C : ℝ)/q*((ringIntervalUnitCount q M B : ℝ)-(B : ℝ)*q.totient/q) := by field_simp
  have hc : 0 ≤ (C : ℝ)/q := by positivity
  have hmain : |(C : ℝ)*ringIntervalUnitCount q M B/q - (B : ℝ)*C*q.totient/(q : ℝ)^2| ≤
      (C : ℝ)/q*(3 : ℝ)^q.primeFactors.card := by
    rw [he, abs_mul, abs_of_nonneg hc]
    exact mul_le_mul_of_nonneg_left hU hc
  exact (abs_sub_le (ringRectangleCount q M N B C r : ℝ)
    ((C : ℝ)*ringIntervalUnitCount q M B/q) ((B : ℝ)*C*q.totient/(q : ℝ)^2)).trans
      (_root_.add_le_add (ringRectangleCount_error_units hq M N B C r) hmain)

end Erdos821.Kloosterman
