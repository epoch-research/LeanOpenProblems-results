import Submission.PrimeRowRemainder

/-!
Prime-row fractional remainders at fixed multiples of `p-1`.
These are auxiliary arithmetic identities, not a settlement of Erdős 68.
-/
namespace PrimeMultiplierRowRemainder

open Erdos68Development LambertPrimeScaling FactorialClearingIndex
open RowRemainderBounds Filter

def numerator (p j : ℕ) : ℕ := p * (j * (p-1)).factorial / p.factorial^j

lemma denominator_dvd (p j : ℕ) (hp : p.Prime) (hj : 0 < j) (hjp : j ≤ p) :
    p.factorial^j ∣ p * (j*(p-1)).factorial := by
  have hpl : p-1 < p := by omega
  have hd₁ : p^(j-1) ∣ (j*(p-1)).factorial := by
    apply ((pow_dvd_pow_of_dvd (Nat.dvd_factorial hp.pos le_rfl) _).trans
      (factorial_pow_dvd_factorial_mul p (j-1))).trans
    apply Nat.factorial_dvd_factorial
    have he₁ := Nat.sub_add_cancel hp.pos
    have he₂ := Nat.sub_add_cancel hj
    nlinarith
  have hd₂ : (p-1).factorial^j ∣ (j*(p-1)).factorial := by
    simpa [Nat.mul_comm] using factorial_pow_dvd_factorial_mul (p-1) j
  have hcop := (hp.coprime_factorial_of_lt hpl).pow (j-1) j
  obtain ⟨u, hu⟩ := hcop.mul_dvd_of_dvd_of_dvd hd₁ hd₂
  refine ⟨u, ?_⟩
  have hf : p.factorial = p*(p-1).factorial := by
    conv_lhs => rw [← Nat.sub_add_cancel hp.pos, Nat.factorial_succ]
    rw [Nat.sub_add_cancel hp.pos]
  have hpow : p^j = p*p^(j-1) := by
    conv_lhs => rw [← Nat.sub_add_cancel hj, pow_succ']
  rw [hu, hf, mul_pow, hpow]
  ring

lemma numerator_identity (p j : ℕ) (hp : p.Prime) (hj : 0 < j) (hjp : j ≤ p) :
    numerator p j * p.factorial^j = p * (j*(p-1)).factorial :=
  Nat.div_mul_cancel (denominator_dvd p j hp hj hjp)

lemma factorial_split (p j : ℕ) (hp : 0 < p) (hj : 0 < j) :
    (j*(p-1)).factorial * (p*j-1).descFactorial (j-1) = (p*j-1).factorial := by
  have hbase : j ≤ p*j := Nat.le_mul_of_pos_left j hp
  have hle : j-1 ≤ p*j-1 := by omega
  have he : p*j-1-(j-1) = j*(p-1) := by
    have hh := Nat.sub_add_cancel hp
    have hh' := Nat.sub_add_cancel hj
    nlinarith [Nat.sub_add_cancel hle,
      Nat.sub_add_cancel (show 1 ≤ p*j by omega)]
  simpa only [he] using Nat.factorial_mul_descFactorial hle

lemma uniform_identity (p j : ℕ) (hp : p.Prime) (hj : 0 < j) (hjp : j ≤ p) :
    uniform p j = numerator p j * j * (p*j-1).descFactorial (j-1) := by
  have hp0 := hp.pos
  apply Nat.eq_of_mul_eq_mul_right (show 0 < p.factorial^j by positivity)
  have hd := Nat.div_mul_cancel (factorial_pow_dvd_factorial_mul p j)
  change ((p*j).factorial / p.factorial^j) * p.factorial^j = _
  rw [hd]
  calc
    (p*j).factorial = p*j*(p*j-1).factorial := by
      conv_lhs => rw [← Nat.sub_add_cancel (show 0 < p*j by positivity), Nat.factorial_succ]
      rw [Nat.sub_add_cancel (show 0 < p*j by positivity)]
    _ = p*j*((j*(p-1)).factorial * (p*j-1).descFactorial (j-1)) := by
      rw [factorial_split p j hp.pos hj]
    _ = (numerator p j * p.factorial^j)*j*(p*j-1).descFactorial (j-1) := by
      rw [numerator_identity p j hp hj hjp]
      ring
    _ = _ := by ring

lemma descending_cast (p j : ℕ) (hp : 0 < p) (hj : 0 < j) :
    ((p*j-1).descFactorial (j-1) : ZMod p) = (-1)^(j-1) * ((j-1).factorial : ZMod p) := by
  rw [Nat.descFactorial_eq_prod_range, Nat.factorial_eq_prod_range_add_one]
  simp only [Nat.cast_prod]
  nth_rw 2 [← Finset.card_range (j-1)]
  rw [Finset.pow_card_mul_prod]
  apply Finset.prod_congr rfl
  intro i hi
  have hi' := Finset.mem_range.mp hi
  have hbase : j ≤ p*j := Nat.le_mul_of_pos_left j hp
  have hle : i+1 ≤ p*j := by omega
  have he : p*j-1-i = p*j-(i+1) := by omega
  rw [he, Nat.cast_sub hle, Nat.cast_mul, ZMod.natCast_self]
  simp

lemma numerator_cast (p j : ℕ) (hp : p.Prime) (hj : 0 < j) (hjp : j < p) :
    (numerator p j : ZMod p) = (-1)^(j-1) := by
  letI : Fact p.Prime := ⟨hp⟩
  have hm : (uniform p j : ZMod p) = (j.factorial : ZMod p) := by
    apply (ZMod.natCast_eq_natCast_iff _ _ _).mpr
    simpa [uniform] using uniform_prime_scaling p hp 1 j
  have hf : (j.factorial : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff, hp.dvd_factorial]
    omega
  have hjf : (j : ZMod p) * ((j-1).factorial : ZMod p) = j.factorial := by
    have he : j*(j-1).factorial = j.factorial := by
      conv_rhs => rw [← Nat.sub_add_cancel hj, Nat.factorial_succ]
      rw [Nat.sub_add_cancel hj]
    simpa only [Nat.cast_mul] using congrArg (Nat.cast : ℕ → ZMod p) he
  rw [uniform_identity p j hp hj hjp.le, Nat.cast_mul, Nat.cast_mul,
    descending_cast p j hp.pos hj] at hm
  have hh : ((numerator p j : ZMod p) * (-1)^(j-1)) * j.factorial = 1*j.factorial := by
    calc
      _ = (numerator p j : ZMod p) * j * ((-1)^(j-1) * (j-1).factorial) := by
        rw [← hjf]
        ring
      _ = _ := by simpa using hm
  have hc := mul_right_cancel₀ hf hh
  have hs : ((-1 : ZMod p)^(j-1))^2 = 1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul]
    norm_num
  linear_combination hc * ((-1 : ZMod p)^(j-1)) - (numerator p j : ZMod p) * hs

lemma numerator_bound (p j : ℕ) (hp : p.Prime) (hj : 0 < j) (hjp : j ≤ p) :
    numerator p j ≤ (2^(j^2+1))^p := by
  have hd : (p-1).factorial^j ≤ p.factorial^j :=
    Nat.pow_le_pow_left (Nat.factorial_le (by omega)) _
  have hn : numerator p j ≤ p * blockCoefficient j (p-1) := by
    refine Nat.le_of_mul_le_mul_right (c := (p-1).factorial^j) ?_ (by positivity)
    calc
      numerator p j * (p-1).factorial^j ≤ numerator p j * p.factorial^j :=
        Nat.mul_le_mul_left _ hd
      _ = p*(j*(p-1)).factorial := numerator_identity p j hp hj hjp
      _ = (p*blockCoefficient j (p-1)) * (p-1).factorial^j := by
        rw [mul_assoc, blockCoefficient_identity]
  calc
    numerator p j ≤ p * blockCoefficient j (p-1) := hn
    _ ≤ 2^p * 2^(j^2*p) := Nat.mul_le_mul (Nat.lt_two_pow_self.le)
      ((blockCoefficient_bound j (p-1)).trans
        (Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_left _ (Nat.sub_le p 1))))
    _ = (2^(j^2+1))^p := by rw [← pow_add, ← pow_mul]; congr 1; ring

lemma eventually_numerator_small (j : ℕ) (hj : 0 < j) :
    ∀ᶠ p : ℕ in atTop, p.Prime → numerator p j < p.factorial-1 := by
  filter_upwards [Nat.eventually_mul_pow_lt_factorial_sub 2 (2^(j^2+1)) 0,
    eventually_ge_atTop j] with p hp hpj hprime
  simp only [Nat.sub_zero] at hp
  have hb := numerator_bound p j hprime hj hpj
  have hh : 0 < (2^(j^2+1))^p := by positivity
  omega

lemma geometric_decomposition (n p j : ℕ) (hp : 2 ≤ p) (hj : 0 < j)
    (hn : (j-1)*p ≤ n) :
    ∃ I : ℕ, (n.factorial : ℝ)/(p.factorial-1) = (I : ℝ) +
      (n.factorial : ℝ)/(p.factorial : ℝ)^j +
      (n.factorial : ℝ)/((p.factorial : ℝ)^j*(p.factorial-1)) := by
  have hf : (p.factorial : ℝ) ≠ 0 := by positivity
  have hf₂ : (2 : ℝ) ≤ p.factorial := by
    exact_mod_cast (show 2 ≤ p.factorial by simpa using Nat.factorial_le hp)
  have hd : (p.factorial : ℝ)-1 ≠ 0 := by linarith
  have hdiv : p.factorial^(j-1) ∣ n.factorial :=
    (factorial_pow_dvd_factorial_mul p (j-1)).trans
      (Nat.factorial_dvd_factorial (by simpa [Nat.mul_comm] using hn))
  let q := n.factorial / p.factorial^(j-1)
  let s := ∑ i ∈ Finset.range (j-1), p.factorial^i
  have hq : (q : ℝ) = (n.factorial : ℝ)/(p.factorial : ℝ)^(j-1) := by
    dsimp [q]
    rw [Nat.cast_div hdiv (by positivity), Nat.cast_pow]
  have hs : (s : ℝ)*(p.factorial-1) = (p.factorial : ℝ)^(j-1)-1 := by
    dsimp [s]
    push_cast
    exact geom_sum_mul _ _
  have he : (n.factorial : ℝ)/(p.factorial-1) = ((q*s : ℕ) : ℝ) +
      (n.factorial : ℝ)/((p.factorial : ℝ)^(j-1)*(p.factorial-1)) := by
    rw [Nat.cast_mul, hq]
    field_simp
    nlinarith [hs]
  have hpow : (p.factorial : ℝ)^j = (p.factorial : ℝ)^(j-1)*p.factorial := by
    conv_lhs => rw [← Nat.sub_add_cancel hj, pow_succ]
  refine ⟨q*s, ?_⟩
  rw [he, hpow]
  field_simp
  ring

/-- The exact prime-row formula. The final size hypothesis prevents the
small positive geometric correction from crossing the next integer. -/
theorem row_formula (p j : ℕ) (hp : p.Prime) (hj : 0 < j) (heven : Even j)
    (hjp : j < p) (hsmall : numerator p j < p.factorial-1) :
    rowRemainder (j*(p-1)) p = 1-1/(p : ℝ) +
      ((j*(p-1)).factorial : ℝ)/((p.factorial : ℝ)^j*(p.factorial-1)) := by
  have hp0 := hp.pos
  have hpR : (0 : ℝ) < p := by positivity
  have hfR : (0 : ℝ) < p.factorial := by positivity
  have hf₂ : (2 : ℝ) ≤ p.factorial := by
    exact_mod_cast (show 2 ≤ p.factorial by simpa using Nat.factorial_le hp.two_le)
  have hdR : (0 : ℝ) < p.factorial-1 := by linarith
  have hodd : Odd (j-1) := by
    obtain ⟨k, hk⟩ := heven
    exact ⟨k-1, by omega⟩
  have hcast : (numerator p j : ZMod p) = -1 := by
    rw [numerator_cast p j hp hj hjp, hodd.neg_one_pow]
  have hdiv : p ∣ numerator p j + 1 := by
    apply (ZMod.natCast_eq_zero_iff _ _).mp
    simp only [Nat.cast_add, Nat.cast_one, hcast, neg_add_cancel]
  obtain ⟨a, ha⟩ := hdiv
  have ha0 : a ≠ 0 := by intro hz; simp [hz] at ha
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero ha0
  have hc : (numerator p j : ℝ) = (p : ℝ)*(q+1)-1 := by
    have he : (numerator p j : ℝ)+1 = (p : ℝ)*(q+1) := by exact_mod_cast ha
    linarith
  have hratio : ((j*(p-1)).factorial : ℝ)/(p.factorial : ℝ)^j =
      (numerator p j : ℝ)/p := by
    have he : (numerator p j : ℝ)*(p.factorial : ℝ)^j =
        (p : ℝ)*(j*(p-1)).factorial := by
      exact_mod_cast numerator_identity p j hp hj hjp.le
    apply (div_eq_div_iff (by positivity) hpR.ne').mpr
    nlinarith
  let eps : ℝ := ((j*(p-1)).factorial : ℝ)/
    ((p.factorial : ℝ)^j*(p.factorial-1))
  have heps : eps = (numerator p j : ℝ)/((p : ℝ)*(p.factorial-1)) := by
    dsimp [eps]
    rw [← div_div, hratio, div_div]
  have heps0 : 0 < eps := by dsimp [eps]; positivity
  have heps1 : eps < 1/(p : ℝ) := by
    have hh : (numerator p j : ℝ) < (p.factorial : ℝ)-1 := by
      have he : numerator p j + 1 < p.factorial := by omega
      have heR : (numerator p j : ℝ)+1 < p.factorial := by exact_mod_cast he
      linarith
    rw [heps]
    apply (div_lt_div_iff₀ (mul_pos hpR hdR) hpR).mpr
    nlinarith
  have hfrac0 : 0 ≤ 1-1/(p : ℝ)+eps := by
    have hi : 1/(p : ℝ) ≤ 1 := (div_le_one hpR).mpr (by exact_mod_cast hp.pos)
    linarith
  have hfrac1 : 1-1/(p : ℝ)+eps < 1 := by linarith
  have hn : (j-1)*p ≤ j*(p-1) := by
    have he₁ := Nat.sub_add_cancel hj
    have he₂ := Nat.sub_add_cancel hp.pos
    nlinarith
  obtain ⟨I, hI⟩ := geometric_decomposition (j*(p-1)) p j hp.two_le hj hn
  have hsecond : ((j*(p-1)).factorial : ℝ)/(p.factorial : ℝ)^j =
      (q : ℝ)+1-1/(p : ℝ) := by
    rw [hratio, hc]
    field_simp
  have htotal : ((j*(p-1)).factorial : ℝ)/(p.factorial-1) =
      ((I+q : ℕ) : ℝ)+(1-1/(p : ℝ)+eps) := by
    rw [hI, hsecond, Nat.cast_add]
    dsimp [eps]
    ring
  unfold rowRemainder
  rw [htotal, Int.fract_natCast_add, Int.fract_eq_self.mpr ⟨hfrac0, hfrac1⟩]

theorem eventually_row_formula (j : ℕ) (hj : 0 < j) (heven : Even j) :
    ∀ᶠ p : ℕ in atTop, p.Prime →
      rowRemainder (j*(p-1)) p = 1-1/(p : ℝ) +
        ((j*(p-1)).factorial : ℝ)/((p.factorial : ℝ)^j*(p.factorial-1)) := by
  filter_upwards [eventually_numerator_small j hj, eventually_gt_atTop j]
    with p hp hpj hprime
  exact row_formula p j hprime hj heven hpj (hp hprime)

theorem row_gt_one_sub_inv (p j : ℕ) (hp : p.Prime) (hj : 0 < j) (heven : Even j)
    (hjp : j < p) (hsmall : numerator p j < p.factorial-1) :
    1-1/(p : ℝ) < rowRemainder (j*(p-1)) p := by
  rw [row_formula p j hp hj heven hjp hsmall]
  have hf₂ : (2 : ℝ) ≤ p.factorial := by
    exact_mod_cast (show 2 ≤ p.factorial by simpa using Nat.factorial_le hp.two_le)
  have hd : (0 : ℝ) < p.factorial-1 := by linarith
  have he : 0 < ((j*(p-1)).factorial : ℝ)/
      ((p.factorial : ℝ)^j*(p.factorial-1)) := by positivity
  linarith

theorem tail_gt_one_sub_inv (p j : ℕ) (hp : p.Prime) (hj : 0 < j) (heven : Even j)
    (hjp : j < p) (hsmall : numerator p j < p.factorial-1) :
    1-1/(p : ℝ) < rowTail (j*(p-1)) := by
  have hj₂ : 2 ≤ j := by obtain ⟨k, hk⟩ := heven; omega
  have hp₂ := hp.two_le
  have hnp : p ≤ j*(p-1) := by
    have he := Nat.sub_add_cancel hp.pos
    nlinarith
  exact (row_gt_one_sub_inv p j hp hj heven hjp hsmall).trans
    (PrimeRowRemainder.rowRemainder_lt_tail (j*(p-1)) p (by omega)
      (Finset.mem_Ico.mpr ⟨hp₂, by omega⟩))

/-- For any fixed positive even multiplier, arbitrarily late indices on
that multiple progression have row tails above each fixed number below one. -/
theorem frequently_tail_gt (j : ℕ) (hj : 0 < j) (heven : Even j)
    (c : ℝ) (hc : c < 1) (N : ℕ) :
    ∃ p : ℕ, p.Prime ∧ N ≤ j*(p-1) ∧ c < rowTail (j*(p-1)) := by
  obtain ⟨P, hP⟩ := eventually_atTop.mp (eventually_numerator_small j hj)
  obtain ⟨m, hm⟩ := exists_nat_gt (1/(1-c))
  obtain ⟨p, hpm, hp⟩ := Nat.exists_infinite_primes (max (max P N) (max m (j+1)))
  have hpj : j < p := by omega
  have hp0 := hp.pos
  have hpR : (0 : ℝ) < p := by positivity
  have hmp : (m : ℝ) ≤ p := by exact_mod_cast (show m ≤ p by omega)
  have hi : 1/(p : ℝ) < 1-c := by
    apply (div_lt_iff₀ hpR).mpr
    have hh := (div_lt_iff₀ (by linarith : (0 : ℝ) < 1-c)).mp (hm.trans_le hmp)
    nlinarith
  have hj₂ : 2 ≤ j := by obtain ⟨k, hk⟩ := heven; omega
  have hnp : p ≤ j*(p-1) := by
    have he := Nat.sub_add_cancel hp.pos
    have hp₂ := hp.two_le
    nlinarith
  refine ⟨p, hp, by omega, ?_⟩
  have ht := tail_gt_one_sub_inv p j hp hj heven hpj (hP p (by omega) hp)
  linarith

lemma subset_rows_lt_tail (n : ℕ) (hn : 2 ≤ n) (s : Finset ℕ)
    (hs : s ⊆ Finset.Ico 2 (n+1)) :
    (∑ k ∈ s, rowRemainder n k) < rowTail n := by
  have hle : (∑ k ∈ s, rowRemainder n k) ≤
      ∑ k ∈ Finset.Ico 2 (n+1), rowRemainder n k :=
    Finset.sum_le_sum_of_subset_of_nonneg hs (fun k _ _ => Int.fract_nonneg _)
  rw [rowRemainder_sum n hn] at hle
  have he := (partial_sum_error (n-1)).1
  have he' := mul_pos (show (0 : ℝ) < n.factorial by positivity) he
  unfold rowTail
  nlinarith

/-- Several applicable prime rows give an additive lower bound. This does
not assert that arbitrarily large prime configurations of this kind exist. -/
theorem finite_prime_rows_lower (n : ℕ) (hn : 2 ≤ n) (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime ∧ ∃ j : ℕ,
      0 < j ∧ Even j ∧ j < p ∧ n = j*(p-1) ∧ numerator p j < p.factorial-1) :
    (∑ p ∈ s, (1-1/(p : ℝ))) < rowTail n := by
  have hsubset : s ⊆ Finset.Ico 2 (n+1) := by
    intro p hp
    obtain ⟨hprime, j, hj, heven, _, rfl, _⟩ := hs p hp
    have hj₂ : 2 ≤ j := by obtain ⟨k, hk⟩ := heven; omega
    have hp₂ := hprime.two_le
    have he := Nat.sub_add_cancel hprime.pos
    apply Finset.mem_Ico.mpr
    constructor
    · exact hp₂
    · nlinarith
  apply lt_of_le_of_lt (b := ∑ p ∈ s, rowRemainder n p) ?_
    (subset_rows_lt_tail n hn s hsubset)
  apply Finset.sum_le_sum
  intro p hp
  obtain ⟨hprime, j, hj, heven, hjp, rfl, hsmall⟩ := hs p hp
  exact (row_gt_one_sub_inv p j hprime hj heven hjp hsmall).le

#print axioms numerator_cast
#print axioms row_formula
#print axioms eventually_row_formula
#print axioms frequently_tail_gt
#print axioms finite_prime_rows_lower

end PrimeMultiplierRowRemainder
