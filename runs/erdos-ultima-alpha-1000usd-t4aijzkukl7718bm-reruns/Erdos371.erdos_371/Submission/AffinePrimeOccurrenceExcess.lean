import FormalConjecturesUtil
import Submission.PeriodicDensity
import Submission.CofactorDensity

/-! A uniform signed excess bound for DISTINCT prime occurrences in affine
products. This does not give a signed bound for largest-prime comparisons. -/

namespace Erdos371AffinePrimeOccurrenceExcess

open Finset Filter
open scoped Topology

lemma progression_one_root {p q : ℕ} (hq : 0 < q) (hpq : p.Coprime q) (b : ℕ) :
    ((range q).filter (fun k => q ∣ p*k+b)).card = 1 := by
  letI : NeZero q := ⟨hq.ne'⟩
  let r := ((-(b : ZMod q)) * (p : ZMod q)⁻¹).val
  have hr : r < q := ZMod.val_lt _
  have hinv : (p : ZMod q) * (p : ZMod q)⁻¹ = 1 := ZMod.coe_mul_inv_eq_one p hpq
  have hroot : q ∣ p*r+b := by
    apply (ZMod.natCast_eq_zero_iff _ _).mp
    push_cast
    dsimp [r]
    rw [ZMod.natCast_zmod_val]
    calc
      _ = -(b : ZMod q)*((p : ZMod q)*(p : ZMod q)⁻¹)+b := by ring
      _ = 0 := by rw [hinv]; ring
  have hu {k : ℕ} (hk : k < q) (hd : q ∣ p*k+b) : k = r := by
    have he : Nat.ModEq q (p*k+b) (p*r+b) :=
      (Nat.modEq_zero_iff_dvd.mpr hd).trans (Nat.modEq_zero_iff_dvd.mpr hroot).symm
    have he' : Nat.ModEq q k r := Nat.ModEq.cancel_left_of_coprime hpq.symm
      (he.add_right_cancel' b)
    change k % q = r % q at he'
    simpa [Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt hr] using he'
  have he : (range q).filter (fun k => q ∣ p*k+b) = {r} := by
    ext k
    simp only [mem_filter, mem_range, mem_singleton]
    constructor
    · rintro ⟨hk, hd⟩; exact hu hk hd
    · rintro rfl; exact ⟨hr, hroot⟩
  rw [he, card_singleton]

lemma progression_count_bounds {p q : ℕ} (hq : 0 < q) (hpq : p.Coprime q)
    (b A : ℕ) :
    A/q ≤ ((range A).filter (fun k => q ∣ p*k+b)).card ∧
    ((range A).filter (fun k => q ∣ p*k+b)).card ≤ A/q+1 := by
  have hperiod (k : ℕ) : (q ∣ p*(k+q)+b) ↔ q ∣ p*k+b := by
    simp [Nat.dvd_iff_mod_eq_zero, Nat.mul_add, Nat.add_mod]
  have hc := Erdos371Exploration.periodic_count_remainder
    (fun k => q ∣ p*k+b) hperiod A
  have hr : ((range (A%q)).filter (fun k => q ∣ p*k+b)).card ≤ 1 := by
    calc
      _ ≤ ((range q).filter (fun k => q ∣ p*k+b)).card :=
        card_le_card (filter_subset_filter _ (range_mono (Nat.mod_lt A hq).le))
      _ = 1 := progression_one_root hq hpq b
  rw [progression_one_root hq hpq b, mul_one] at hc
  omega

noncomputable def primeWeight (w : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ q ∈ n.primeFactors, w q

lemma primeWeight_expand (w : ℕ → ℝ) {n X : ℕ} (hn : 0 < n) (hX : n ≤ X) :
    primeWeight w n = ∑ q ∈ (X+1).primesBelow, if q ∣ n then w q else 0 := by
  rw [← sum_filter]
  have he : ((X+1).primesBelow.filter (fun q => q ∣ n)) = n.primeFactors := by
    ext q
    simp only [mem_filter, Nat.mem_primesBelow, Nat.mem_primeFactors]
    constructor
    · rintro ⟨⟨_, hq⟩, hd⟩
      exact ⟨hq, hd, hn.ne'⟩
    · rintro ⟨hq, hd, _⟩
      exact ⟨⟨(Nat.le_of_dvd hn hd).trans_lt (by omega), hq⟩, hd⟩
  rw [he]
  rfl

lemma sum_primeWeight_expand (w : ℕ → ℝ) (F : ℕ → ℕ) {A X : ℕ}
    (hF : ∀ k < A, 0 < F k ∧ F k ≤ X) :
    (∑ k ∈ range A, primeWeight w (F k)) =
      ∑ q ∈ (X+1).primesBelow, w q * ((range A).filter (fun k => q ∣ F k)).card := by
  calc
    _ = ∑ k ∈ range A, ∑ q ∈ (X+1).primesBelow, if q ∣ F k then w q else 0 := by
      apply sum_congr rfl
      intro k hk
      exact primeWeight_expand w (hF k (mem_range.mp hk)).1 (hF k (mem_range.mp hk)).2
    _ = _ := by
      rw [sum_comm]
      apply sum_congr rfl
      intro q _
      rw [← sum_filter, sum_const, nsmul_eq_mul, mul_comm]

/-- Uniform over all weights in `[0,1]` vanishing at the slope prime. -/
theorem weighted_excess_bounds {p A X b : ℕ} (hp : p.Prime)
    (hA : A ≤ X) (hF : ∀ k < A, 0 < p*k+b ∧ p*k+b ≤ X)
    (w : ℕ → ℝ) (hw : ∀ q, 0 ≤ w q ∧ w q ≤ 1) (hwp : w p = 0) :
    0 ≤ (∑ k ∈ range A, primeWeight w (p*k+b)) -
      (∑ k ∈ range A, primeWeight w (k+1)) ∧
    (∑ k ∈ range A, primeWeight w (p*k+b)) -
      (∑ k ∈ range A, primeWeight w (k+1)) ≤ Nat.primeCounting X := by
  have hI (k : ℕ) (hk : k < A) : 0 < k+1 ∧ k+1 ≤ X := ⟨by omega, by omega⟩
  rw [sum_primeWeight_expand w (fun k => p*k+b) hF,
    sum_primeWeight_expand w (fun k => k+1) hI, ← sum_sub_distrib]
  have hterm (q : ℕ) (hq : q ∈ (X+1).primesBelow) :
      0 ≤ w q * ((range A).filter (fun k => q ∣ p*k+b)).card -
        w q * ((range A).filter (fun k => q ∣ k+1)).card ∧
      w q * ((range A).filter (fun k => q ∣ p*k+b)).card -
        w q * ((range A).filter (fun k => q ∣ k+1)).card ≤ 1 := by
    by_cases he : q = p
    · subst q; simp [hwp]
    · have hqp := Nat.prime_of_mem_primesBelow hq
      have hc := progression_count_bounds hqp.pos
        ((Nat.coprime_primes hp hqp).mpr (Ne.symm he)) b A
      rw [Nat.card_multiples]
      have hl : ((A/q : ℕ) : ℝ) ≤ ((range A).filter (fun k => q ∣ p*k+b)).card :=
        Nat.cast_le.mpr hc.1
      have hu : (((range A).filter (fun k => q ∣ p*k+b)).card : ℝ) ≤ (A/q : ℕ)+1 := by
        exact_mod_cast hc.2
      constructor <;> nlinarith [(hw q).1, (hw q).2]
  constructor
  · exact sum_nonneg (fun q hq => (hterm q hq).1)
  · calc
      _ ≤ ∑ _q ∈ (X+1).primesBelow, (1 : ℝ) :=
        sum_le_sum (fun q hq => (hterm q hq).2)
      _ = _ := by
        simp only [sum_const, nsmul_eq_mul, mul_one, Nat.primesBelow_card_eq_primeCounting']
        rfl


noncomputable def excess (p b : ℕ) (w : ℕ → ℝ) (A : ℕ) : ℝ :=
  (∑ k ∈ range A, primeWeight w (p*k+b)) -
    (∑ k ∈ range A, primeWeight w (k+1))

lemma affine_excess_bound {p b : ℕ} (hp : p.Prime) (hb : 0 < b) (hb' : b ≤ p+1)
    (w : ℕ → ℝ) (hw : ∀ q, 0 ≤ w q ∧ w q ≤ 1) (hwp : w p = 0) (A : ℕ) :
    0 ≤ excess p b w A ∧ excess p b w A ≤ Nat.primeCounting (p*A+1) := by
  have hp2 := hp.two_le
  apply weighted_excess_bounds hp (X := p*A+1) (by nlinarith) _ w hw hwp
  intro k hk
  constructor
  · omega
  · have hm := Nat.mul_le_mul_left p (show k+1 ≤ A by omega)
    nlinarith

/-- Uniform even when the bounded prime weights change at every cutoff.
Only the slope and intercept must be fixed before taking the limit. -/
theorem moving_weight_excess_mean_zero {p b : ℕ} (hp : p.Prime)
    (hb : 0 < b) (hb' : b ≤ p+1) (w : ℕ → ℕ → ℝ)
    (hw : ∀ A q, 0 ≤ w A q ∧ w A q ≤ 1) (hwp : ∀ A, w A p = 0) :
    Tendsto (fun A : ℕ => excess p b (w A) A / A) atTop (𝓝 0) := by
  have hp2 := hp.two_le
  have hscale : Tendsto (fun A : ℕ => p*A+1) atTop atTop := by
    apply tendsto_atTop.2
    intro K
    filter_upwards [eventually_ge_atTop K] with A hA
    nlinarith
  have hπ := Erdos371CofactorDensity.primeCounting_ratio_tendsto_zero.comp hscale
  have hupper : Tendsto (fun A : ℕ =>
      (Nat.primeCounting (p*A+1) : ℝ)/(p*A+1 : ℕ)*(p+1)) atTop (𝓝 0) := by
    simpa using hπ.mul_const (p+1 : ℝ)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
  · exact Eventually.of_forall fun A => div_nonneg
      (affine_excess_bound hp hb hb' (w A) (hw A) (hwp A) A).1 (Nat.cast_nonneg A)
  · filter_upwards [eventually_gt_atTop 0] with A hA
    have ha : (0 : ℝ) < A := Nat.cast_pos.mpr hA
    have hx : (0 : ℝ) < (p*A+1 : ℕ) := by positivity
    have hratio : ((p*A+1 : ℕ) : ℝ)/(A : ℝ) ≤ (p+1 : ℝ) := by
      apply (div_le_iff₀ ha).mpr
      push_cast
      have ha1 : (1 : ℝ) ≤ A := by exact_mod_cast hA
      nlinarith
    calc
      _ ≤ (Nat.primeCounting (p*A+1) : ℝ)/(A : ℝ) :=
        div_le_div_of_nonneg_right
          (affine_excess_bound hp hb hb' (w A) (hw A) (hwp A) A).2 ha.le
      _ = ((Nat.primeCounting (p*A+1) : ℝ)/(p*A+1 : ℕ))*
          (((p*A+1 : ℕ) : ℝ)/(A : ℝ)) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hratio (by positivity)

def erasingWeight (p q : ℕ) : ℝ := if q = p then 0 else 1

def distinctCount (n : ℕ) : ℕ := n.primeFactors.card

lemma erasingWeight_bounds (p q : ℕ) :
    0 ≤ erasingWeight p q ∧ erasingWeight p q ≤ 1 := by
  unfold erasingWeight
  split_ifs <;> norm_num

lemma primeWeight_erasing {p n : ℕ} (hp : p.Prime) (hn : 0 < n) :
    primeWeight (erasingWeight p) n = (distinctCount n : ℝ) -
      (if p ∣ n then 1 else 0) := by
  have he (q : ℕ) : erasingWeight p q = (1 : ℝ) - (if q = p then 1 else 0) := by
    unfold erasingWeight
    split_ifs <;> norm_num
  simp only [primeWeight, he, sum_sub_distrib, sum_const, nsmul_eq_mul,
    mul_one, sum_ite_eq']
  simp [distinctCount, Nat.mem_primeFactors, hp, hn.ne']

noncomputable def correctedCountExcess (p b A : ℕ) : ℝ :=
  (∑ k ∈ range A, (distinctCount (p*k+b) : ℝ)) -
    (∑ k ∈ range A, (distinctCount (k+1) : ℝ)) + (A/p : ℕ)

lemma excess_eq_correctedCount {p b : ℕ} (hp : p.Prime)
    (hb : 0 < b) (hpb : ¬p ∣ b) (A : ℕ) :
    excess p b (erasingWeight p) A = correctedCountExcess p b A := by
  have hout (k : ℕ) : primeWeight (erasingWeight p) (p*k+b) =
      (distinctCount (p*k+b) : ℝ) := by
    have hnd : ¬p ∣ p*k+b := fun h =>
      hpb ((Nat.dvd_add_iff_right (dvd_mul_right p k)).mpr h)
    rw [primeWeight_erasing hp (by omega), if_neg hnd, sub_zero]
  have hin (k : ℕ) : primeWeight (erasingWeight p) (k+1) =
      (distinctCount (k+1) : ℝ) - (if p ∣ k+1 then 1 else 0) :=
    primeWeight_erasing hp (by omega)
  unfold excess correctedCountExcess
  simp_rw [hout, hin]
  rw [sum_sub_distrib, sum_boole, Nat.card_multiples]
  ring

/-- The slope-prime correction is the exact integer floor `A/p`.
The remaining signed excess is nonnegative and at most a prime count. -/
theorem correctedCountExcess_bounds {p b : ℕ} (hp : p.Prime)
    (hb : 0 < b) (hb' : b ≤ p+1) (hpb : ¬p ∣ b) (A : ℕ) :
    0 ≤ correctedCountExcess p b A ∧
      correctedCountExcess p b A ≤ Nat.primeCounting (p*A+1) := by
  rw [← excess_eq_correctedCount hp hb hpb A]
  exact affine_excess_bound hp hb hb' (erasingWeight p) (erasingWeight_bounds p)
    (by simp [erasingWeight]) A

theorem correctedCountExcess_mean_zero {p b : ℕ} (hp : p.Prime)
    (hb : 0 < b) (hb' : b ≤ p+1) (hpb : ¬p ∣ b) :
    Tendsto (fun A : ℕ => correctedCountExcess p b A / A) atTop (𝓝 0) := by
  have h := moving_weight_excess_mean_zero hp hb hb' (fun _ => erasingWeight p)
    (fun _ => erasingWeight_bounds p) (fun _ => by simp [erasingWeight])
  simpa only [excess_eq_correctedCount hp hb hpb] using h

theorem both_affine_count_excess_bounds {p : ℕ} (hp : p.Prime) (A : ℕ) :
    (0 ≤ correctedCountExcess p (p-1) A ∧
      correctedCountExcess p (p-1) A ≤ Nat.primeCounting (p*A+1)) ∧
    (0 ≤ correctedCountExcess p (p+1) A ∧
      correctedCountExcess p (p+1) A ≤ Nat.primeCounting (p*A+1)) := by
  have hp2 := hp.two_le
  constructor
  · apply correctedCountExcess_bounds hp (by omega) (by omega) _ A
    intro h
    have hh := Nat.le_of_dvd (show 0 < p-1 by omega) h
    omega
  · apply correctedCountExcess_bounds hp (by omega) (by omega) _ A
    intro h
    exact hp.not_dvd_one ((Nat.dvd_add_iff_right (dvd_refl p)).mpr h)


end Erdos371AffinePrimeOccurrenceExcess

#print axioms Erdos371AffinePrimeOccurrenceExcess.weighted_excess_bounds
#print axioms Erdos371AffinePrimeOccurrenceExcess.moving_weight_excess_mean_zero
#print axioms Erdos371AffinePrimeOccurrenceExcess.correctedCountExcess_mean_zero
#print axioms Erdos371AffinePrimeOccurrenceExcess.both_affine_count_excess_bounds
