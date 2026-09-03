import Submission.LambertPrimeScaling

/-! Base-prime block congruences for the original Lambert coefficients.
These statements do not apply automatically to carried coefficients and do
not settle the irrationality conjecture. -/

namespace LambertPrimeBlocks

open Erdos68Development LambertPrimeScaling

lemma choose_two_digits (p : ℕ) (hp : p.Prime) (a b c d : ℕ)
    (hb : b < p) (hd : d < p) :
    Nat.ModEq p ((p*a+b).choose (p*c+d)) (b.choose d * a.choose c) := by
  letI : Fact p.Prime := ⟨hp⟩
  have h := Choose.choose_modEq_choose_mod_mul_choose_div_nat
    (p := p) (n := p*a+b) (k := p*c+d)
  simpa [Nat.add_mod, Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt hd,
    Nat.mul_add_div hp.pos, Nat.div_eq_of_lt hb, Nat.div_eq_of_lt hd] using h

/-- Repeated equal blocks obey a two-digit Lucas formula when there is no
carry. If the repeated low digit carries, the multinomial vanishes modulo p. -/
theorem uniform_digit_split (p : ℕ) (hp : p.Prime) (a b : ℕ) (hb : b < p)
    (k : ℕ) :
    Nat.ModEq p (uniform (p*a+b) k)
      (if b*k < p then uniform a k * uniform b k else 0) := by
  induction k with
  | zero => simp only [uniform_zero, Nat.mul_zero, if_pos hp.pos, one_mul]; rfl
  | succ k ih =>
    rw [uniform_succ]
    by_cases hnext : b*(k+1) < p
    · have hprev : b*k < p := by nlinarith
      rw [if_pos hnext, if_pos hprev] at *
      have hc := choose_two_digits p hp (a*(k+1)) (b*(k+1)) a b hnext hb
      rw [show p*(a*(k+1))+b*(k+1) = (p*a+b)*(k+1) by ring] at hc
      have hh := hc.mul ih
      rw [uniform_succ a k, uniform_succ b k]
      convert hh using 1; ring
    · rw [if_neg hnext]
      by_cases hprev : b*k < p
      · have hlo : p ≤ b*(k+1) := by omega
        have hrem : b*(k+1) % p < b := by
          rw [Nat.mod_eq_sub_mod hlo, Nat.mod_eq_of_lt (show b*(k+1)-p < p by
            have : b*(k+1) < p+p := by nlinarith
            omega)]
          have hs := Nat.sub_add_cancel hlo
          nlinarith
        letI : Fact p.Prime := ⟨hp⟩
        have hc := Choose.choose_modEq_choose_mod_mul_choose_div_nat
          (p := p) (n := (p*a+b)*(k+1)) (k := p*a+b)
        have hnmod : ((p*a+b)*(k+1)) % p = b*(k+1) % p := by
          rw [add_mul, mul_assoc]
          simp
        have hdmod : (p*a+b) % p = b := by simp [Nat.add_mod, Nat.mod_eq_of_lt hb]
        rw [hnmod, hdmod, Nat.choose_eq_zero_of_lt hrem, zero_mul] at hc
        simpa using hc.mul (Nat.ModEq.refl (uniform (p*a+b) k))
      · rw [if_neg hprev] at ih
        simpa using (Nat.ModEq.refl (((p*a+b)*(k+1)).choose (p*a+b))).mul ih

lemma fullCoeff_blocks (n : ℕ) :
    fullCoeff n = ∑ k ∈ n.divisors, uniform (n/k) k := by
  by_cases hn : n = 0
  · subst n; simp [fullCoeff]
  rw [fullCoeff_uniform]
  symm
  calc
    (∑ k ∈ n.divisors, uniform (n/k) k) =
        ∑ k ∈ n.divisors, uniform (n/k) (n/(n/k)) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [Nat.div_div_self (Nat.dvd_of_mem_divisors hk) hn]
    _ = ∑ d ∈ n.divisors, uniform d (n/d) :=
      Nat.sum_div_divisors n (fun d => uniform d (n/d))

lemma quotient_split (p m r k : ℕ) (hk : 0 < k) (hm : k ∣ m) (hr : k ∣ r) :
    (p*m+r)/k = p*(m/k)+r/k := by
  have he : p*m+r = (p*(m/k)+r/k)*k := by
    rw [add_mul, mul_assoc, Nat.div_mul_cancel hm, Nat.div_mul_cancel hr]
  rw [he, Nat.mul_div_cancel _ hk]

lemma no_carry_divides (p m r k : ℕ) (hp : 0 < p) (hr : r < p)
    (hk : k ∣ p*m+r) (hcarry : (((p*m+r)/k) % p)*k < p) :
    k ∣ m ∧ k ∣ r := by
  let d := (p*m+r)/k
  have he : p*((d/p)*k)+(d%p)*k = p*m+r := by
    calc
      p*((d/p)*k)+(d%p)*k = (d%p+p*(d/p))*k := by ring
      _ = d*k := by rw [Nat.mod_add_div]
      _ = p*m+r := Nat.div_mul_cancel hk
  have hcarry' : (d%p)*k < p := hcarry
  have hm : (d/p)*k = m := by
    have hh := congrArg (fun n : ℕ => n/p) he
    simpa [Nat.mul_add_div hp, Nat.div_eq_of_lt hcarry', Nat.div_eq_of_lt hr] using hh
  have hr' : (d%p)*k = r := by
    have hh := congrArg (fun n : ℕ => n%p) he
    simpa [Nat.add_mod, Nat.mod_eq_of_lt hcarry', Nat.mod_eq_of_lt hr] using hh
  exact ⟨⟨d/p, by simpa only [mul_comm] using hm.symm⟩,
    ⟨d%p, by simpa only [mul_comm] using hr'.symm⟩⟩

lemma block_summand (p : ℕ) (hp : p.Prime) (m r k : ℕ) (hr : r < p)
    (hkpos : 0 < k) (hk : k ∣ p*m+r) :
    Nat.ModEq p (uniform ((p*m+r)/k) k)
      (if k ∣ m ∧ k ∣ r then uniform (m/k) k * uniform (r/k) k else 0) := by
  by_cases hd : k ∣ m ∧ k ∣ r
  · rw [if_pos hd, quotient_split p m r k hkpos hd.1 hd.2]
    have hrk : r/k < p := (Nat.div_le_self r k).trans_lt hr
    have h := uniform_digit_split p hp (m/k) (r/k) hrk k
    simpa [Nat.div_mul_cancel hd.2, hr] using h
  · rw [if_neg hd]
    have hcarry : ¬ (((p*m+r)/k)%p)*k < p := by
      intro hc
      exact hd (no_carry_divides p m r k hp.pos hr hk hc)
    have h := uniform_digit_split p hp (((p*m+r)/k)/p) (((p*m+r)/k)%p)
      (Nat.mod_lt _ hp.pos) k
    rw [if_neg hcarry] at h
    have he : p*(((p*m+r)/k)/p)+((p*m+r)/k)%p = (p*m+r)/k := by
      simpa only [add_comm] using Nat.mod_add_div ((p*m+r)/k) p
    rwa [he] at h

lemma common_divisors_filter (p m r : ℕ) (hp : 0 < p) (hm : 0 < m) :
    (p*m+r).divisors.filter (fun k => k ∣ m ∧ k ∣ r) = (m.gcd r).divisors := by
  ext k
  simp only [Finset.mem_filter, Nat.mem_divisors]
  constructor
  · rintro ⟨_, hkm, hkr⟩
    exact ⟨Nat.dvd_gcd hkm hkr, (Nat.gcd_pos_of_pos_left r hm).ne'⟩
  · rintro ⟨hk, _⟩
    have hkm := hk.trans (Nat.gcd_dvd_left m r)
    have hkr := hk.trans (Nat.gcd_dvd_right m r)
    refine ⟨⟨dvd_add (dvd_mul_of_dvd_right hkm p) hkr, ?_⟩, hkm, hkr⟩
    have : 0 < p*m := Nat.mul_pos hp hm
    omega

/-- A whole prime block is determined by equal-block multinomials of the
high and low indices, summed over their common divisors. -/
theorem fullCoeff_prime_block (p : ℕ) (hp : p.Prime) (m r : ℕ)
    (hm : 0 < m) (hr : r < p) :
    Nat.ModEq p (fullCoeff (p*m+r))
      (∑ k ∈ (m.gcd r).divisors, uniform (m/k) k * uniform (r/k) k) := by
  rw [fullCoeff_blocks]
  trans ∑ k ∈ (p*m+r).divisors,
      if k ∣ m ∧ k ∣ r then uniform (m/k) k * uniform (r/k) k else 0
  · apply Nat.ModEq.sum
    intro k hk
    have hd := Nat.dvd_of_mem_divisors hk
    have hn : 0 < p*m+r := by have := Nat.mul_pos hp.pos hm; omega
    exact block_summand p hp m r k hr (Nat.pos_of_dvd_of_pos hd hn) hd
  · rw [← Finset.sum_filter, common_divisors_filter p m r hp.pos hm]

/-- The factorial singleton correction vanishes in every block with a
positive high index. This concerns the original, uncarried coefficients. -/
theorem lambertCoeff_prime_block (p : ℕ) (hp : p.Prime) (m r : ℕ)
    (hm : 0 < m) (hr : r < p) :
    Nat.ModEq p (lambertCoeff (p*m+r))
      (∑ k ∈ (m.gcd r).divisors, uniform (m/k) k * uniform (r/k) k) := by
  have hn : 0 < p*m+r := by have := Nat.mul_pos hp.pos hm; omega
  have h := fullCoeff_prime_block p hp m r hm hr
  rw [fullCoeff_eq _ hn] at h
  have hd : p ∣ (p*m+r).factorial :=
    Nat.dvd_factorial hp.pos ((Nat.le_mul_of_pos_right p hm).trans (Nat.le_add_right _ _))
  have he : Nat.ModEq p (lambertCoeff (p*m+r)+(p*m+r).factorial)
      (lambertCoeff (p*m+r)) := by
    simpa using (Nat.ModEq.refl (lambertCoeff (p*m+r))).add
      (Nat.modEq_zero_iff_dvd.mpr hd)
  exact he.symm.trans h

theorem lambertCoeff_prime_block_coprime (p : ℕ) (hp : p.Prime) (m r : ℕ)
    (hm : 0 < m) (hr : r < p) (hcop : m.Coprime r) :
    Nat.ModEq p (lambertCoeff (p*m+r)) 1 := by
  have h := lambertCoeff_prime_block p hp m r hm hr
  simpa [hcop.gcd_eq_one, uniform, Nat.div_self (Nat.factorial_pos m),
    Nat.div_self (Nat.factorial_pos r)] using h

end LambertPrimeBlocks

#print axioms LambertPrimeBlocks.uniform_digit_split
#print axioms LambertPrimeBlocks.lambertCoeff_prime_block
#print axioms LambertPrimeBlocks.lambertCoeff_prime_block_coprime
