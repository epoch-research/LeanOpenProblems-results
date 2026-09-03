import FormalConjecturesUtil

/-! Uniform elementary lower bounds for coprime integers in short intervals. -/
namespace Erdos773.UnitIntervalDensity

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius

set_option maxHeartbeats 2000000

lemma totient_divisor_lower (q : ℕ) (hq : 0 < q) :
    q ≤ q.divisors.card * q.totient := by
  calc
    q = ∑ d ∈ q.divisors, d.totient := (Nat.sum_totient q).symm
    _ ≤ ∑ _d ∈ q.divisors, q.totient := by
      apply Finset.sum_le_sum
      intro d hd
      exact Nat.le_of_dvd (Nat.totient_pos.mpr hq)
        (Nat.totient_dvd_of_dvd (Nat.dvd_of_mem_divisors hd))
    _ = _ := by simp

lemma moebius_divisor_sum (n : ℕ) :
    (∑ d ∈ n.divisors, (μ d : ℝ)) = if n = 1 then 1 else 0 := by
  have hh := congrArg (fun f : ArithmeticFunction ℝ => f n)
    (coe_moebius_mul_coe_zeta (R := ℝ))
  simpa only [coe_mul_zeta_apply, intCoe_apply, one_apply] using hh

lemma coprime_indicator (q n : ℕ) (hq : 0 < q) :
    (if q.Coprime n then (1 : ℝ) else 0) =
      ∑ d ∈ q.divisors, if d ∣ n then (μ d : ℝ) else 0 := by
  have hg : 0 < q.gcd n := Nat.gcd_pos_of_pos_left n hq
  have he : q.divisors.filter (fun d => d ∣ n) = (q.gcd n).divisors := by
    ext d
    simp [Nat.mem_divisors, Nat.dvd_gcd_iff, hq.ne', hg.ne']
  rw [← Finset.sum_filter, he, moebius_divisor_sum]

lemma totient_moebius_ratio (q : ℕ) (hq : 0 < q) :
    (q.totient : ℝ) / q = ∑ d ∈ q.divisors, (μ d : ℝ) / d := by
  have hi := (sum_eq_iff_sum_mul_moebius_eq
    (f := fun n => (n.totient : ℝ)) (g := fun n => (n : ℝ))).mp
    (fun n _hn => by exact_mod_cast Nat.sum_totient n) q hq
  rw [Nat.sum_divisorsAntidiagonal (fun a b => (μ a : ℝ) * (b : ℝ))] at hi
  rw [← hi, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro d hd
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mem_divisors hd).ne'
  rw [Nat.cast_div_charZero (Nat.dvd_of_mem_divisors hd)]
  have hq0 : (q : ℝ) ≠ 0 := by positivity
  field_simp

lemma prefix_count (q m : ℕ) (hq : 0 < q) :
    ((Finset.range m).filter (fun n => q.Coprime (n + 1))).card =
      ∑ d ∈ q.divisors, (μ d : ℝ) * (m / d : ℕ) := by
  have hc : (((Finset.range m).filter (fun n => q.Coprime (n + 1))).card : ℝ) =
      ∑ n ∈ Finset.range m, if q.Coprime (n + 1) then (1 : ℝ) else 0 := by simp
  rw [hc]
  simp_rw [coprime_indicator q _ hq]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  calc
    _ = (μ d : ℝ) * ∑ n ∈ range m, if d ∣ n + 1 then (1 : ℝ) else 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      split_ifs <;> simp
    _ = _ := by simp [Nat.card_multiples]

lemma interval_count (q a b : ℕ) (hq : 0 < q) (hab : a ≤ b) :
    (((Ico a b).filter (fun n => q.Coprime (n + 1))).card : ℝ) =
      ∑ d ∈ q.divisors, (μ d : ℝ) * ((b / d : ℕ) - (a / d : ℕ) : ℝ) := by
  calc
    _ = ∑ n ∈ Ico a b, if q.Coprime (n + 1) then (1 : ℝ) else 0 := by simp
    _ = (((range b).filter (fun n => q.Coprime (n + 1))).card : ℝ) -
        (((range a).filter (fun n => q.Coprime (n + 1))).card : ℝ) := by
      rw [Finset.sum_Ico_eq_sub _ hab]
      simp
    _ = _ := by rw [prefix_count q b hq, prefix_count q a hq, ← Finset.sum_sub_distrib];
                apply Finset.sum_congr rfl; intros; ring

lemma floor_interval_error (a b d : ℕ) (hd : 0 < d) :
    |((b / d : ℕ) : ℝ) - ((a / d : ℕ) : ℝ) - ((b : ℝ) - a) / d| ≤ 1 := by
  have hdR : (0 : ℝ) < d := by positivity
  have ha : ((a / d : ℕ) : ℝ) * d ≤ a := by exact_mod_cast Nat.div_mul_le_self a d
  have hb : ((b / d : ℕ) : ℝ) * d ≤ b := by exact_mod_cast Nat.div_mul_le_self b d
  have ha' : (a : ℝ) < (a / d : ℕ) * (d : ℝ) + d := by
    exact_mod_cast Nat.lt_div_mul_add (a := a) hd
  have hb' : (b : ℝ) < (b / d : ℕ) * (d : ℝ) + d := by
    exact_mod_cast Nat.lt_div_mul_add (a := b) hd
  have he : (((b : ℝ) - a) / d) * d = (b : ℝ) - a := div_mul_cancel₀ _ hdR.ne'
  apply abs_le.mpr
  constructor <;> nlinarith only [ha, hb, ha', hb', he, hdR]

/-- Inclusion-exclusion has an error at most one per divisor. -/
theorem interval_discrepancy (q a b : ℕ) (hq : 0 < q) (hab : a ≤ b) :
    |(((Ico a b).filter (fun n => q.Coprime (n + 1))).card : ℝ) -
      ((b : ℝ) - a) * (q.totient : ℝ) / q| ≤ q.divisors.card := by
  rw [interval_count q a b hq hab]
  have he : ((b : ℝ) - a) * (q.totient : ℝ) / q =
      ∑ d ∈ q.divisors, (μ d : ℝ) * (((b : ℝ) - a) / d) := by
    rw [mul_div_assoc, totient_moebius_ratio q hq, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intros
    ring
  rw [he, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ d ∈ q.divisors, |(μ d : ℝ) * (((b / d : ℕ) : ℝ) - (a / d : ℕ)) -
        (μ d : ℝ) * (((b : ℝ) - a) / d)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _d ∈ q.divisors, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      rw [← mul_sub, abs_mul]
      have hmu : |(μ d : ℝ)| ≤ 1 := by exact_mod_cast (abs_moebius_le_one (n := d))
      have herr := floor_interval_error a b d (Nat.pos_of_mem_divisors hd)
      simpa only [one_mul] using mul_le_mul hmu herr (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
    _ = _ := by simp

/-- The units can be chosen inside [L,2L], with a natural-number density bound. -/
theorem unit_gaps (q L : ℕ) (hq : 0 < q) (hL : 2 * q.divisors.card ^ 2 ≤ L) :
    ∃ U : Finset ℕ, U ⊆ Icc L (2 * L) ∧ (∀ u ∈ U, q.Coprime u) ∧
      L ≤ 2 * q.divisors.card * U.card := by
  let V := (Ico L (2 * L)).filter (fun n => q.Coprime (n + 1))
  let U := V.image (· + 1)
  have hcard : U.card = V.card := Finset.card_image_of_injective _ Nat.succ_injective
  refine ⟨U, ?_, ?_, ?_⟩
  · intro u hu
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨hn, _⟩ := Finset.mem_filter.mp hn
    obtain ⟨hnL, hn2L⟩ := Finset.mem_Ico.mp hn
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  · intro u hu
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hu
    exact (Finset.mem_filter.mp hn).2
  · have ht := totient_divisor_lower q hq
    have hτ : 0 < q.divisors.card := Finset.card_pos.mpr
      ⟨1, Nat.one_mem_divisors.mpr hq.ne'⟩
    have hτR : (0 : ℝ) < q.divisors.card := by positivity
    have hqR : (0 : ℝ) < q := by positivity
    have htR : (q : ℝ) ≤ q.divisors.card * (q.totient : ℝ) := by exact_mod_cast ht
    have hLR : 2 * (q.divisors.card : ℝ) ^ 2 ≤ L := by exact_mod_cast hL
    have hdisc := (abs_le.mp (interval_discrepancy q L (2 * L) hq (by omega))).1
    change -(q.divisors.card : ℝ) ≤ (V.card : ℝ) - _ at hdisc
    push_cast at hdisc
    rw [show (2 : ℝ) * L - L = L by ring] at hdisc
    have hd := mul_le_mul_of_nonneg_right hdisc hqR.le
    have he : ((L : ℝ) * (q.totient : ℝ) / q) * q = (L : ℝ) * q.totient :=
      div_mul_cancel₀ _ hqR.ne'
    have h₁ : (L : ℝ) * q.totient ≤ q * ((V.card : ℝ) + q.divisors.card) := by
      nlinarith only [hd, he]
    have h₂ := mul_le_mul_of_nonneg_left h₁ hτR.le
    have h₃ := mul_le_mul_of_nonneg_left htR (show (0 : ℝ) ≤ L by positivity)
    have h₄ : (L : ℝ) ≤ q.divisors.card * ((V.card : ℝ) + q.divisors.card) := by
      nlinarith only [h₂, h₃, hqR]
    have hh : (L : ℝ) ≤ 2 * q.divisors.card * (V.card : ℝ) := by
      nlinarith only [h₄, hLR]
    rw [hcard]
    exact_mod_cast hh

#print axioms interval_discrepancy
#print axioms unit_gaps

end Erdos773.UnitIntervalDensity
