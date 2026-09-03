import Submission.LambertPrimeBand

/-! A different rational factorial series with prime units, predecessor
congruences, prime-band congruences, and exponentially bounded tails.
This is NOT the original series and is not a disproof of Erdos 68. -/

namespace PrimeBandRationalComparison

open Erdos68Development Filter
open scoped Topology

lemma band_pos (n : ℕ) : 0 < primeBandProduct n := by
  apply Finset.prod_pos
  intro p hp
  exact (Finset.mem_filter.mp hp).2.1.pos

lemma band_le_four_pow (n : ℕ) : primeBandProduct n ≤ 4^n := by
  have hd : primeBandProduct n ∣ primorial n := by
    apply Finset.prod_dvd_prod_of_subset
    intro p hp
    obtain ⟨hr, hprime, hhalf⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨hr, hprime⟩
  exact (Nat.le_of_dvd (primorial_pos n) hd).trans (primorial_le_4_pow n)

/-- At an odd prime a new prime enters the band, and no old prime leaves. -/
lemma band_at_prime (p : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p) :
    primeBandProduct p = p*primeBandProduct (p-1) := by
  classical
  obtain ⟨k, hk⟩ := hp.odd_of_ne_two (by omega)
  have hset : (Finset.range (p+1)).filter (fun q => q.Prime ∧ p<2*q) =
      insert p ((Finset.range p).filter (fun q => q.Prime ∧ p-1<2*q)) := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert]
    constructor
    · rintro ⟨hq, hqp, hhalf⟩
      by_cases he : q=p
      · exact Or.inl he
      · exact Or.inr ⟨by omega, hqp, by omega⟩
    · rintro (rfl | ⟨hq, hqp, hhalf⟩)
      · exact ⟨by omega, hp, by omega⟩
      · exact ⟨by omega, hqp, by omega⟩
  have hnot : p ∉ (Finset.range p).filter (fun q => q.Prime ∧ p-1<2*q) := by simp
  unfold primeBandProduct
  rw [hset, Finset.prod_insert hnot, Nat.sub_add_cancel (by omega : 1 ≤ p)]

def modulus (n : ℕ) : ℕ := if n.Prime then 0 else Nat.lcm (n-1) (primeBandProduct n)

/-- `tail r` is the tail at original index r+3. -/
def tail : ℕ → ℕ
  | 0 => 1
  | r+1 => 1+((r+4)*tail r-2) % modulus (r+4)

def coeffRow (r : ℕ) : ℕ := (r+4)*tail r-tail (r+1)
def coeff (n : ℕ) : ℕ := if n<4 then 0 else coeffRow (n-4)

lemma tail_pos (r : ℕ) : 0 < tail r := by cases r <;> simp [tail]

lemma tail_succ_le (r : ℕ) : tail (r+1) ≤ (r+4)*tail r-1 := by
  have hp := tail_pos r
  have hm := Nat.mod_le ((r+4)*tail r-2) (modulus (r+4))
  have ht : 4 ≤ (r+4)*tail r := by nlinarith
  simp only [tail]
  omega

lemma coeffRow_formula (r : ℕ) :
    coeffRow r = 1+modulus (r+4)*(((r+4)*tail r-2)/modulus (r+4)) := by
  have hp := tail_pos r
  have ht : 4 ≤ (r+4)*tail r := by nlinarith
  have hd := Nat.mod_add_div ((r+4)*tail r-2) (modulus (r+4))
  simp only [coeffRow, tail]
  omega

lemma coeffRow_pos (r : ℕ) : 0 < coeffRow r := by rw [coeffRow_formula]; omega
lemma coeff_add_four (r : ℕ) : coeff (r+4)=coeffRow r := by simp [coeff]

lemma coeff_prime (p : ℕ) (hp4 : 4 ≤ p) (hp : p.Prime) : coeff p=1 := by
  obtain ⟨r, rfl⟩ : ∃ r, p=r+4 := ⟨p-4, by omega⟩
  simp [coeff_add_four, coeffRow_formula, modulus, hp]

lemma modulus_dvd_coeff_sub_one (n : ℕ) (hn : 4 ≤ n) : modulus n ∣ coeff n-1 := by
  obtain ⟨r, rfl⟩ : ∃ r, n=r+4 := ⟨n-4, by omega⟩
  rw [coeff_add_four, coeffRow_formula]
  simp

lemma coeff_positive (n : ℕ) (hn : 4 ≤ n) : 0 < coeff n := by
  obtain ⟨r, rfl⟩ : ∃ r, n=r+4 := ⟨n-4, by omega⟩
  simpa only [coeff_add_four] using coeffRow_pos r

lemma predecessor_congruence (n : ℕ) (hn : 4 ≤ n) : Nat.ModEq (n-1) (coeff n) 1 := by
  by_cases hp : n.Prime
  · rw [coeff_prime n hn hp]
  · have hd := modulus_dvd_coeff_sub_one n hn
    rw [modulus, if_neg hp] at hd
    exact ((Nat.modEq_iff_dvd' (coeff_positive n hn)).mpr
      ((Nat.dvd_lcm_left _ _).trans hd)).symm

lemma prime_band_congruence (n : ℕ) (hn : 4 ≤ n) :
    Nat.ModEq (primeBandProduct n) (coeff n) 1 := by
  by_cases hp : n.Prime
  · rw [coeff_prime n hn hp]
  · have hd := modulus_dvd_coeff_sub_one n hn
    rw [modulus, if_neg hp] at hd
    exact ((Nat.modEq_iff_dvd' (coeff_positive n hn)).mpr
      ((Nat.dvd_lcm_right _ _).trans hd)).symm

/-- The same prime-band product which is a congruence modulus also bounds
the positive integer tails, with only one additional linear factor. -/
lemma tail_upper (r : ℕ) : tail r ≤ (r+2)*primeBandProduct (r+3) := by
  induction r with
  | zero =>
    have hp := band_pos 3
    simp only [tail, zero_add]
    omega
  | succ r ih =>
    by_cases hp : (r+4).Prime
    · have hs := tail_succ_le r
      have hb := band_at_prime (r+4) hp (by omega)
      rw [show r+4-1=r+3 by omega] at hb
      rw [show r+1+3=r+4 by omega, show r+1+2=r+3 by omega, hb]
      have hh := Nat.mul_le_mul_left (r+4) ih
      calc
        _ ≤ (r+4)*tail r := hs.trans (Nat.sub_le _ _)
        _ ≤ (r+4)*((r+2)*primeBandProduct (r+3)) := hh
        _ ≤ (r+4)*((r+3)*primeBandProduct (r+3)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (by omega : r+2 ≤ r+3))
        _ = _ := by ring
    · have hl : 0 < Nat.lcm (r+3) (primeBandProduct (r+4)) :=
        Nat.lcm_pos (by omega) (band_pos _)
      have hm := Nat.mod_lt ((r+4)*tail r-2) hl
      have hb := Nat.lcm_le_mul (show 0<r+3 by omega) (band_pos (r+4))
      simp only [tail, modulus, if_neg hp, show r+4-1=r+3 by omega]
      simpa only [Nat.add_assoc] using (show
        1+((r+4)*tail r-2) % Nat.lcm (r+3) (primeBandProduct (r+4)) ≤
          (r+3)*primeBandProduct (r+4) by omega)

noncomputable def normalizedTail (r : ℕ) : ℝ := (tail r : ℝ)/(r+3).factorial

lemma summable_normalizedTail : Summable normalizedTail := by
  have hs := ((summable_nat_add_iff 2).mpr (Real.summable_pow_div_factorial 4)).mul_left 4
  apply hs.of_norm_bounded
  intro r
  have hb := (tail_upper r).trans
    (Nat.mul_le_mul_left (r+2) (band_le_four_pow (r+3)))
  have hbr : (tail r : ℝ) ≤ (r+3 : ℝ)*4^(r+3) := by
    have hh : (tail r : ℝ) ≤ (r+2 : ℝ)*4^(r+3) := by exact_mod_cast hb
    nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 4) (r+3)]
  have hf : ((r+2).factorial : ℝ) ≠ 0 := by positivity
  have hn : (r+3 : ℝ) ≠ 0 := by positivity
  dsimp only [normalizedTail]
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc
    _ ≤ (r+3 : ℝ)*4^(r+3)/(r+3).factorial :=
      div_le_div_of_nonneg_right hbr (by positivity)
    _ = _ := by
      rw [show r+3=(r+2)+1 by omega, Nat.factorial_succ, pow_succ]
      push_cast
      field_simp
      ring

lemma coeffRow_div (r : ℕ) :
    (coeffRow r : ℝ)/(r+4).factorial = normalizedTail r-normalizedTail (r+1) := by
  have hl : tail (r+1) ≤ (r+4)*tail r := (tail_succ_le r).trans (Nat.sub_le _ _)
  have hf : ((r+3).factorial : ℝ) ≠ 0 := by positivity
  have hn : (r+4 : ℝ) ≠ 0 := by positivity
  simp only [coeffRow, Nat.cast_sub hl, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat,
    normalizedTail, show r+1+3=r+4 by omega]
  rw [show r+4=(r+3)+1 by omega, Nat.factorial_succ]
  push_cast
  field_simp
  ring

lemma hasSum_coeffRow :
    HasSum (fun r : ℕ => (coeffRow r : ℝ)/(r+4).factorial) (1/6 : ℝ) := by
  have hs := summable_normalizedTail
  have ht := (summable_nat_add_iff 1).mpr hs
  have he := hs.sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_one] at he
  have h0 : normalizedTail 0=(1/6 : ℝ) := by norm_num [normalizedTail, tail]
  rw [h0] at he
  have he' : (∑' r, normalizedTail r)-(∑' r, normalizedTail (r+1))=(1/6 : ℝ) := by
    linarith
  simpa only [coeffRow_div, he'] using hs.hasSum.sub ht.hasSum

lemma summable_coeff : Summable (fun n : ℕ => (coeff n : ℝ)/n.factorial) := by
  apply (summable_nat_add_iff 4).mp
  simpa only [coeff_add_four] using hasSum_coeffRow.summable

/-- The comparison series is rational, and is not the target series. -/
theorem sum_coeff : (∑' n : ℕ, (coeff n : ℝ)/n.factorial)=(1/6 : ℝ) := by
  have he := summable_coeff.sum_add_tsum_nat_add 4
  have hz : (∑ n ∈ Finset.range 4, (coeff n : ℝ)/n.factorial)=0 := by
    apply Finset.sum_eq_zero
    intro n hn
    simp [coeff, Finset.mem_range.mp hn]
  rw [hz, zero_add] at he
  simpa only [coeff_add_four, hasSum_coeffRow.tsum_eq] using he.symm

lemma prefix_identity (r : ℕ) :
    (∑ k ∈ Finset.range (r+4), (coeff k : ℝ)/k.factorial)=(1/6 : ℝ)-normalizedTail r := by
  induction r with
  | zero => norm_num [Finset.sum_range_succ, coeff, normalizedTail, tail]
  | succ r ih =>
    rw [show r+1+4=(r+4)+1 by omega, Finset.sum_range_succ, ih,
      coeff_add_four, coeffRow_div]
    ring

lemma scaled_tail_identity (r : ℕ) :
    ((r+3).factorial : ℝ)*((∑' n : ℕ, (coeff n : ℝ)/n.factorial)-
      ∑ k ∈ Finset.range (r+4), (coeff k : ℝ)/k.factorial) = tail r := by
  rw [sum_coeff, prefix_identity, sub_sub_cancel, normalizedTail]
  exact mul_div_cancel₀ _ (by positivity)

lemma different_coefficients : coeff 4=1 ∧ lambertCoeff 4=7 := by decide

theorem comparison_properties :
    (∀ n : ℕ, 4 ≤ n → 0<coeff n) ∧
    (∀ p : ℕ, 4 ≤ p → p.Prime → coeff p=1) ∧
    (∀ n : ℕ, 4 ≤ n → Nat.ModEq (n-1) (coeff n) 1) ∧
    (∀ n : ℕ, 4 ≤ n → Nat.ModEq (primeBandProduct n) (coeff n) 1) ∧
    (∀ r, 0<tail r ∧ tail r ≤ (r+2)*primeBandProduct (r+3)) ∧
    (∑' n : ℕ, (coeff n : ℝ)/n.factorial)=(1/6 : ℝ) :=
  ⟨coeff_positive, coeff_prime, predecessor_congruence, prime_band_congruence,
    fun r => ⟨tail_pos r, tail_upper r⟩, sum_coeff⟩

end PrimeBandRationalComparison

#print axioms PrimeBandRationalComparison.band_at_prime
#print axioms PrimeBandRationalComparison.tail_upper
#print axioms PrimeBandRationalComparison.sum_coeff
#print axioms PrimeBandRationalComparison.scaled_tail_identity
#print axioms PrimeBandRationalComparison.comparison_properties
