import Submission.CarriedFixedModulusCriterion

/-!
Residues modulo four of the original Lambert coefficients, in terms of the
odd part of their indices. These are not inherited automatically by the
small-tail carry, and this file does not settle Erdős 68.
-/

namespace LambertModFour

open Finset Erdos68Development LambertPrimeScaling LambertPrimeBlocks
  LambertDoldCongruence CarriedFixedModulusCriterion

lemma uniform_two (d : ℕ) : uniform d 2 = d.centralBinom := by
  rw [show 2 = 1+1 by rfl, uniform_succ]
  simp [uniform, Nat.centralBinom, Nat.mul_comm, Nat.div_self (Nat.factorial_pos d)]

lemma four_dvd_central_odd (d : ℕ) (hd : 3 ≤ d) (hodd : d % 2 = 1) :
    4 ∣ d.centralBinom := by
  have h2 := Nat.two_dvd_centralBinom_of_one_le (show 0 < d-1 by omega)
  have he := Nat.succ_mul_centralBinom_succ (d-1)
  rw [show d-1+1 = d by omega] at he
  have h4 : 4 ∣ d*d.centralBinom := by
    rw [he]
    obtain ⟨b, hb⟩ := h2
    refine ⟨(2*(d-1)+1)*b, ?_⟩
    rw [hb]
    ring
  have hc2 : Nat.Coprime 2 d := Nat.prime_two.coprime_iff_not_dvd.mpr (by
    intro hh
    have := Nat.mod_eq_zero_of_dvd hh
    omega)
  have hc4 : Nat.Coprime 4 d := by simpa using hc2.pow_left 2
  exact hc4.dvd_of_dvd_mul_left h4

lemma four_dvd_uniform_two_odd (d : ℕ) (hd : 3 ≤ d) (hodd : d % 2 = 1) :
    4 ∣ uniform d 2 := by
  rw [uniform_two]
  exact four_dvd_central_odd d hd hodd

lemma uniform_two_double_mod_four (d : ℕ) :
    Nat.ModEq 4 (uniform (2*d) 2) (uniform d 2) := by
  have h := uniform_prime_power_lift 2 1 d 2 Nat.prime_two (by
    norm_num only [Nat.reduceAdd, Nat.reducePow]
    exact ⟨d, by ring⟩)
  norm_num only [Nat.reduceAdd, Nat.reducePow] at h
  exact h

lemma four_dvd_uniform_two_double_odd (d : ℕ) (hd : 3 ≤ d) (hodd : d % 2 = 1) :
    4 ∣ uniform (2*d) 2 := by
  apply Nat.modEq_zero_iff_dvd.mp
  exact (uniform_two_double_mod_four d).trans
    (Nat.modEq_zero_iff_dvd.mpr (four_dvd_uniform_two_odd d hd hodd))

lemma four_dvd_uniform_three_of_two (d : ℕ) (hd : 4 ∣ uniform d 2) :
    4 ∣ uniform d 3 := by
  rw [show 3 = 2+1 by rfl, uniform_succ]
  exact dvd_mul_of_dvd_right hd _

/-- All contributions with four or more blocks vanish modulo four. -/
lemma fullCoeff_mod_four_small_blocks (n : ℕ) (hn : 4 ≤ n)
    (h2 : 2 ∣ n → 4 ∣ uniform (n/2) 2)
    (h3 : 3 ∣ n → 4 ∣ uniform (n/3) 3) : Nat.ModEq 4 (fullCoeff n) 1 := by
  have hone : (∑ k ∈ n.divisors, if k=1 then 1 else 0) = 1 := by
    simp [Nat.mem_divisors, show n ≠ 0 by omega]
  rw [fullCoeff_blocks, ← hone]
  apply Nat.ModEq.sum
  intro k hk
  have hkn := Nat.dvd_of_mem_divisors hk
  have hkpos := Nat.pos_of_dvd_of_pos hkn (show 0 < n by omega)
  by_cases hk1 : k=1
  · subst k
    simpa [uniform, Nat.div_self (Nat.factorial_pos n)] using
      (Nat.ModEq.refl (n := 4) 1)
  · rw [if_neg hk1]
    apply Nat.modEq_zero_iff_dvd.mpr
    by_cases hk2 : k=2
    · subst k; exact h2 hkn
    by_cases hk3 : k=3
    · subst k; exact h3 hkn
    have hkd : 4 ∣ k.factorial := Nat.dvd_factorial (by decide) (by omega)
    exact hkd.trans (factorial_dvd_uniform_multinomial
      (Nat.div_pos (Nat.le_of_dvd (by omega) hkn) hkpos) k)

lemma coeff_mod_four_small_blocks (n : ℕ) (hn : 4 ≤ n)
    (h2 : 2 ∣ n → 4 ∣ uniform (n/2) 2)
    (h3 : 3 ∣ n → 4 ∣ uniform (n/3) 3) : Nat.ModEq 4 (lambertCoeff n) 1 := by
  have h := fullCoeff_mod_four_small_blocks n hn h2 h3
  rw [fullCoeff_eq n (by omega)] at h
  have hf := Nat.mod_eq_zero_of_dvd (Nat.dvd_factorial (by decide : 0 < 4) hn)
  simpa only [Nat.ModEq, Nat.add_mod, hf, Nat.add_zero, Nat.mod_mod] using h

lemma coeff_odd_mod_four (m : ℕ) (hm : 5 ≤ m) (hodd : m % 2 = 1) :
    Nat.ModEq 4 (lambertCoeff m) 1 := by
  apply coeff_mod_four_small_blocks m (by omega)
  · intro h2
    have := Nat.mod_eq_zero_of_dvd h2
    omega
  · intro h3
    have he : m = 3*(m/3) := (Nat.mul_div_cancel' h3).symm
    have hd : 3 ≤ m/3 := by omega
    have hod : (m/3) % 2 = 1 := by omega
    exact four_dvd_uniform_three_of_two _ (four_dvd_uniform_two_odd _ hd hod)

lemma coeff_twice_odd_mod_four (m : ℕ) (hm : 5 ≤ m) (hodd : m % 2 = 1) :
    Nat.ModEq 4 (lambertCoeff (2*m)) 1 := by
  apply coeff_mod_four_small_blocks (2*m) (by omega)
  · intro _
    rw [Nat.mul_div_cancel_left m (by decide : 0 < 2)]
    exact four_dvd_uniform_two_odd m (by omega) hodd
  · intro h3
    have h3m : 3 ∣ m := (Nat.prime_three.dvd_mul.mp h3).resolve_left (by decide)
    have he : m = 3*(m/3) := (Nat.mul_div_cancel' h3m).symm
    have hd : 3 ≤ m/3 := by omega
    have hod : (m/3) % 2 = 1 := by omega
    rw [Nat.mul_div_assoc 2 h3m]
    exact four_dvd_uniform_three_of_two _ (four_dvd_uniform_two_double_odd _ hd hod)

/-- If the odd part is at least five, the original coefficient is one
modulo four, regardless of the power of two in the index. -/
theorem coeff_mod_four_of_odd_part (m : ℕ) (hm : 5 ≤ m) (hodd : m % 2 = 1)
    (r : ℕ) : Nat.ModEq 4 (lambertCoeff (2^r*m)) 1 := by
  induction r with
  | zero => simpa using coeff_odd_mod_four m hm hodd
  | succ r ih =>
    cases r with
    | zero => simpa using coeff_twice_odd_mod_four m hm hodd
    | succ r =>
      have hpos : 0 < 2^r := by positivity
      have hm' : 2 ≤ 2^r*m := by nlinarith
      have h := original_dold_mod_four (2^r*m) hm'
      have he1 : 4*(2^r*m) = 2^(r+1+1)*m := by ring
      have he2 : 2*(2^r*m) = 2^(r+1)*m := by ring
      rw [he1, he2] at h
      exact h.trans ih

/-- The exceptional odd parts one and three give residue three once the
small initial indices have passed. -/
theorem coeff_power_two_mod_four (r : ℕ) :
    Nat.ModEq 4 (lambertCoeff (2^(r+2))) 3 := by
  induction r with
  | zero => decide
  | succ r ih =>
    have hpos : 0 < 2^r := by positivity
    have hm : 2 ≤ 2^(r+1) := by rw [pow_succ]; omega
    have h := original_dold_mod_four (2^(r+1)) hm
    have he1 : 4*2^(r+1) = 2^(r+1+2) := by ring
    have he2 : 2*2^(r+1) = 2^(r+2) := by ring
    rw [he1, he2] at h
    exact h.trans ih

theorem coeff_three_times_power_two_mod_four (r : ℕ) :
    Nat.ModEq 4 (lambertCoeff (2^(r+1)*3)) 3 := by
  induction r with
  | zero => decide
  | succ r ih =>
    have hpos : 0 < 2^r := by positivity
    have hm : 2 ≤ 2^r*3 := by omega
    have h := original_dold_mod_four (2^r*3) hm
    have he1 : 4*(2^r*3) = 2^(r+1+1)*3 := by ring
    have he2 : 2*(2^r*3) = 2^(r+1)*3 := by ring
    rw [he1, he2] at h
    exact h.trans ih

/-- At a multiple of four, the preceding carry contribution vanishes
modulo four. The remaining carry is indexed by n-3 in the existing code. -/
lemma coefficient_carry_mod_four (m : ℕ) (hm : 1 ≤ m) :
    CongruencePreservingCarry.coeff (4*m) % 4 =
      ((lambertCoeff (4*m) : ℤ)+CongruencePreservingCarry.carry (4*m-3)) % 4 := by
  have he : CongruencePreservingCarry.coeff (4*m) =
      (lambertCoeff (4*m) : ℤ)+CongruencePreservingCarry.carry (4*m-3) -
        (4*(m : ℤ))*CongruencePreservingCarry.carry (4*m-4) := by
    rw [CongruencePreservingCarry.coeff, if_neg (by omega),
      CongruencePreservingCarry.coeffRow]
    rw [show 4*m-4+4 = 4*m by omega, show 4*m-4+1 = 4*m-3 by omega]
    have hh : ((4*m-4 : ℕ) : ℤ)+4 = 4*(m : ℤ) := by omega
    rw [hh]
  rw [he]
  simp [Int.sub_emod, Int.mul_emod]

/-- Rationality would force the explicit actual carry to have residue two
at every sufficiently late index 4m with m odd. -/
theorem rational_carry_mod_four (q : ℚ)
    (hq : (∑' k : ℕ, term k) = (q : ℝ)) (m : ℕ)
    (hm : q.den+6 ≤ m) (hodd : m % 2 = 1) :
    CongruencePreservingCarry.carry (4*m-3) % 4 = 2 := by
  have hbase := coeff_mod_four_of_odd_part m (by omega) hodd 2
  norm_num only [Nat.reducePow] at hbase
  have hbase' : (lambertCoeff (4*m) : ℤ) % 4 = 1 := by
    exact_mod_cast hbase
  have hnew := rational_even_coefficient_mod_four q hq (4*m) (by omega) (by omega)
  rw [coefficient_carry_mod_four m (by omega)] at hnew
  push_cast at hnew
  omega

/-- Only arbitrarily late failures of that single carry residue would be
needed. No such infinitude is proved for the actual carry. -/
theorem irrational_of_frequent_carry_residue_failure
    (hfailure : ∀ M : ℕ, ∃ m ≥ M, m % 2 = 1 ∧
      CongruencePreservingCarry.carry (4*m-3) % 4 ≠ 2) :
    Irrational (∑' k : ℕ, term k) := by
  rintro ⟨q, hq⟩
  obtain ⟨m, hm, hodd, hne⟩ := hfailure (q.den+6)
  exact hne (rational_carry_mod_four q hq.symm m hm hodd)

end LambertModFour

#print axioms LambertModFour.coeff_mod_four_of_odd_part
#print axioms LambertModFour.coeff_power_two_mod_four
#print axioms LambertModFour.coeff_three_times_power_two_mod_four

#print axioms LambertModFour.rational_carry_mod_four
#print axioms LambertModFour.irrational_of_frequent_carry_residue_failure
