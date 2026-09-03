import Submission.CongruencePreservingCarry
import Submission.CongruentTailResets
import Submission.FactorialTailCriterion
import Submission.SubquadraticTailCriterion

/-!
Necessary prime-gap behavior if the original series were rational.
These are conditional identities, not an exclusion of rationality.
-/

namespace CarriedRationalPrimePattern

open Erdos68Development CongruencePreservingCarry

noncomputable def actualTail (n : ℕ) : ℝ :=
  FactorialTailCriterion.scaledTail coeff n

lemma actualTail_add_three (r : ℕ) : actualTail (r+3) = tail r := by
  simpa only [actualTail, FactorialTailCriterion.scaledTail, Nat.add_assoc] using
    scaled_tail_identity r

lemma actualTail_pos (n : ℕ) (hn : 3 ≤ n) : 0 < actualTail n := by
  obtain ⟨r, rfl⟩ : ∃ r, n = r+3 := ⟨n-3, by omega⟩
  rw [actualTail_add_three]
  exact tail_pos r

lemma actualTail_nonprime_lt (n : ℕ) (hn : 4 ≤ n) (hp : ¬n.Prime) :
    actualTail n < n := by
  obtain ⟨r, rfl⟩ : ∃ r, n = r+4 := ⟨n-4, by omega⟩
  have he : actualTail (r+4) = tail (r+1) := by
    simpa only [Nat.add_assoc] using actualTail_add_three (r+1)
  rw [he]
  exact_mod_cast tail_nonprime_lt r hp

def integerTail (q : ℚ) (n : ℕ) : ℤ :=
  q.num*(n.factorial/q.den : ℕ)-FactorialTailCriterion.factorialPrefix coeff n

lemma integerTail_cast (q : ℚ) (hq : (∑' k : ℕ, term k) = (q : ℝ))
    (n : ℕ) (hn : q.den ≤ n) : (integerTail q n : ℝ) = actualTail n := by
  have hd := Nat.dvd_factorial q.pos hn
  have hden : (q.den : ℝ) ≠ 0 := by exact_mod_cast q.den_ne_zero
  simp only [integerTail, actualTail, FactorialTailCriterion.scaledTail,
    Int.cast_sub, Int.cast_mul, Int.cast_natCast]
  rw [FactorialTailCriterion.cast_factorialPrefix, sum_coeff, hq,
    Nat.cast_div hd hden, Rat.cast_def]
  ring

lemma integerTail_succ (q : ℚ) (hq : (∑' k : ℕ, term k) = (q : ℝ))
    (n : ℕ) (hn : q.den ≤ n) :
    integerTail q (n+1) = (n+1 : ℤ)*integerTail q n-coeff (n+1) := by
  have he := FactorialTailCriterion.scaledTail_succ coeff n
  change actualTail (n+1) = (n+1 : ℝ)*actualTail n-(coeff (n+1) : ℝ) at he
  rw [← integerTail_cast q hq n hn, ← integerTail_cast q hq (n+1) (by omega)] at he
  exact_mod_cast he

lemma integerTail_congruence (q : ℚ) (hq : (∑' k : ℕ, term k) = (q : ℝ))
    (n : ℕ) (hn : q.den ≤ n) (hn3 : 3 ≤ n) :
    (n : ℤ) ∣ integerTail q (n+1)-integerTail q n+1 := by
  rw [integerTail_succ q hq n hn]
  have hd := predecessor_congruence (n+1) (by omega)
  have he : (n+1-1 : ℤ) = n := by ring
  push_cast at hd
  rw [he] at hd
  convert dvd_sub (dvd_mul_right (n : ℤ) (integerTail q n)) hd using 1
  ring

lemma integerTail_nonprime_bounds (q : ℚ) (hq : (∑' k : ℕ, term k) = (q : ℝ))
    (n : ℕ) (hn : q.den ≤ n) (hn4 : 4 ≤ n) (hp : ¬n.Prime) :
    1 ≤ integerTail q n ∧ integerTail q n ≤ (n : ℤ)-1 := by
  have hlo := actualTail_pos n (by omega)
  have hhi := actualTail_nonprime_lt n hn4 hp
  rw [← integerTail_cast q hq n hn] at hlo hhi
  have hlo' : (0 : ℤ) < integerTail q n := by exact_mod_cast hlo
  have hhi' : integerTail q n < (n : ℤ) := by exact_mod_cast hhi
  omega

/-- The positive linear successor bound and the prime-unit recurrence force
this reset. The value is `p-2`, not `p`. -/
lemma unit_successor (p : ℕ) (hp : 3 ≤ p) (u v w : ℤ)
    (hunit : v = (p : ℤ)*u-1)
    (hdiv : (p : ℤ) ∣ w-v+1)
    (hw : 1 ≤ w ∧ w ≤ p) : w = (p : ℤ)-2 := by
  have hd : (p : ℤ) ∣ w+2 := by
    convert dvd_add hdiv (dvd_mul_right (p : ℤ) u) using 1
    rw [hunit]
    ring
  obtain ⟨k, hk⟩ := hd
  have hk1 : k = 1 := by
    have hpos : (0 : ℤ) < p := by omega
    have hkl : 1 ≤ k := by
      by_contra h
      have hm := mul_nonpos_of_nonneg_of_nonpos hpos.le (show k ≤ 0 by omega)
      omega
    have hku : k ≤ 1 := by
      by_contra h
      have hm := mul_le_mul_of_nonneg_left (show (2 : ℤ) ≤ k by omega) hpos.le
      nlinarith
    omega
  rw [hk1, mul_one] at hk
  omega

lemma prime_successor_not_prime (p : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p) :
    ¬(p+1).Prime := by
  have ho := hp.eq_two_or_odd.resolve_left (by omega)
  intro hq
  have hqo := hq.eq_two_or_odd.resolve_left (by omega)
  omega

/-- Exact necessary behavior for every sufficiently late prime successor. -/
theorem rational_prime_successor (q : ℚ) (hq : (∑' k : ℕ, term k) = (q : ℝ))
    (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hden : q.den ≤ p-1) :
    integerTail q (p+1) = (p : ℤ)-2 := by
  have he : p-1+1 = p := by omega
  have hu := integerTail_succ q hq (p-1) hden
  rw [he, coeff_prime p hp] at hu
  have hu' : integerTail q p = (p : ℤ)*integerTail q (p-1)-1 := by
    simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_sub (show 1 ≤ p by omega),
      Nat.cast_one, sub_add_cancel] using hu
  have hb := integerTail_nonprime_bounds q hq (p+1) (by omega) (by omega)
    (prime_successor_not_prime p hp (by omega))
  apply unit_successor p (by omega) (integerTail q (p-1)) (integerTail q p)
    (integerTail q (p+1)) hu' (integerTail_congruence q hq p (by omega) (by omega))
  simpa only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right] using hb

/-- No further reset occurs before index `2*p-1`, unless another prime
intervenes. This describes an arbitrary integer sequence with these bounds. -/
lemma descending_block (t : ℕ → ℤ) (p L : ℕ) (hp : 5 ≤ p) (hL : L ≤ p-3)
    (hstart : t (p+1) = (p : ℤ)-2)
    (hb : ∀ i ≤ L, 1 ≤ t (p+1+i) ∧ t (p+1+i) ≤ (p+1+i : ℕ)-1)
    (hd : ∀ i < L, ((p+1+i : ℕ) : ℤ) ∣ t (p+1+i+1)-t (p+1+i)+1) :
    ∀ i ≤ L, t (p+1+i) = (p : ℤ)-2-i := by
  intro i hi
  induction i with
  | zero => simpa using hstart
  | succ i ih =>
    have ht := ih (by omega)
    have hbnext : 1 ≤ t (p+1+i+1) ∧ t (p+1+i+1) ≤ (p+1+i : ℕ) := by
      have hh := hb (i+1) hi
      rw [show p+1+(i+1) = p+1+i+1 by omega] at hh
      push_cast at hh ⊢
      exact ⟨hh.1, by linarith [hh.2]⟩
    have hs := CongruentTailResets.step t (p+1+i) (by omega)
      (hb i (by omega)) hbnext (hd i (by omega))
    rw [if_neg (by rw [ht]; omega), ht] at hs
    simpa only [Nat.add_assoc, Nat.cast_add, Nat.cast_one, sub_sub] using hs

/-- Conditional formula on an interval between two sufficiently late
consecutive primes less than a factor of two apart. -/
theorem rational_between_primes (q : ℚ) (hq : (∑' k : ℕ, term k) = (q : ℝ))
    (p s : ℕ) (hp : p.Prime) (hs : s.Prime) (hp5 : 5 ≤ p)
    (hden : q.den ≤ p-1) (hps : p < s) (hs2p : s < 2*p)
    (hgap : ∀ n, p < n → n < s → ¬n.Prime) :
    (∀ n, p < n → n < s → integerTail q n = 2*(p : ℤ)-1-n) ∧
      integerTail q s = (s : ℤ)*(2*(p : ℤ)-s)-1 := by
  have hpodd := hp.eq_two_or_odd.resolve_left (by omega)
  have hsodd := hs.eq_two_or_odd.resolve_left (by omega)
  have hgap2 : p+2 ≤ s := by omega
  have hstart := rational_prime_successor q hq p hp hp5 hden
  have hblock := descending_block (integerTail q) p (s-p-2) hp5 (by omega) hstart
    (fun i hi => integerTail_nonprime_bounds q hq (p+1+i) (by omega) (by omega)
      (hgap (p+1+i) (by omega) (by omega)))
    (fun i hi => integerTail_congruence q hq (p+1+i) (by omega) (by omega))
  have hmid : ∀ n, p < n → n < s → integerTail q n = 2*(p : ℤ)-1-n := by
    intro n hn hns
    have hh := hblock (n-p-1) (by omega)
    have he : p+1+(n-p-1) = n := by omega
    rw [he] at hh
    omega
  refine ⟨hmid, ?_⟩
  have he := integerTail_succ q hq (s-1) (by omega)
  rw [show s-1+1 = s by omega, coeff_prime s hs, hmid (s-1) (by omega) (by omega)] at he
  rw [he]
  rw [Nat.cast_sub (show 1 ≤ s by omega)]
  push_cast
  ring

/-- Under rationality, the quadratic tail bound is asymptotically sharp
along arbitrarily large prime indices. This remains a conditional result. -/
theorem rational_near_quadratic (q : ℚ) (hq : (∑' k : ℕ, term k) = (q : ℝ))
    (K M : ℕ) (hK : 1 ≤ K) :
    ∃ s ≥ M, s.Prime ∧ ((K : ℤ)-1)*(s : ℤ)^2 < (K : ℤ)*integerTail q s := by
  obtain ⟨a, ha, L, hL, hsize, hp, hqprime⟩ :=
    SubquadraticTailCriterion.prime_predecessor_pairs_square (4*K)
      (max (max M q.den) 5)
  have haM : M ≤ a := (le_max_left M q.den).trans ((le_max_left _ _).trans ha)
  have haD : q.den ≤ a := (le_max_right M q.den).trans ((le_max_left _ _).trans ha)
  have ha5 : 5 ≤ a := (le_max_right _ _).trans ha
  have hex : ∃ s : ℕ, a+1 < s ∧ s.Prime := ⟨a+L+1, by omega, hqprime⟩
  let s := Nat.find hex
  have hps : a+1 < s := (Nat.find_spec hex).1
  have hs : s.Prime := (Nat.find_spec hex).2
  have hsupper : s ≤ a+L+1 := Nat.find_min' hex ⟨by omega, hqprime⟩
  have hgap : ∀ n, a+1 < n → n < s → ¬n.Prime := by
    intro n hpn hns hn
    exact Nat.find_min hex hns ⟨hpn, hn⟩
  have hLa : L < a := by nlinarith [Nat.zero_le (K*L^2)]
  have hs2 : s < 2*(a+1) := by omega
  have he := (rational_between_primes q hq (a+1) s hp hs (by omega)
    (by omega) hps hs2 hgap).2
  have hbudget : 2*K*L+K+1 ≤ a+1 := by
    have hL1 : 1 ≤ L := hL
    nlinarith [Nat.zero_le (K*L^2), Nat.zero_le (L^2)]
  have hbudget' : (2 : ℤ)*K*L+K+1 ≤ a+1 := by exact_mod_cast hbudget
  have hps' : (a : ℤ)+1 < s := by exact_mod_cast hps
  have hsupper' : (s : ℤ) ≤ a+L+1 := by exact_mod_cast hsupper
  have hspos : (0 : ℤ) < s := by omega
  have hKpos : (0 : ℤ) < K := by omega
  have hmul := mul_le_mul_of_nonneg_left hbudget' hspos.le
  have hgapmul := mul_le_mul_of_nonneg_left hsupper' (mul_nonneg hKpos.le hspos.le)
  refine ⟨s, by omega, hs, ?_⟩
  rw [he]
  push_cast
  nlinarith [mul_nonneg hKpos.le (show (0 : ℤ) ≤ s-1 by omega)]

/-- A uniform fixed-factor improvement at prime indices WOULD settle the
target. No such estimate for the carried tails is established here. -/
theorem irrational_of_prime_fraction_bound (K N : ℕ) (hK : 1 ≤ K)
    (hb : ∀ p ≥ N, p.Prime →
      (K : ℝ)*actualTail p ≤ ((K : ℝ)-1)*(p : ℝ)^2) :
    Irrational (∑' k : ℕ, term k) := by
  rintro ⟨q, hq⟩
  obtain ⟨s, hsN, hs, htail⟩ := rational_near_quadratic q hq.symm K (max N q.den) hK
  have hu := hb s ((le_max_left _ _).trans hsN) hs
  rw [← integerTail_cast q hq.symm s ((le_max_right _ _).trans hsN)] at hu
  have hlu : ((K : ℝ)-1)*(s : ℝ)^2 < (K : ℝ)*(integerTail q s : ℝ) := by
    exact_mod_cast htail
  linarith

#print axioms rational_near_quadratic
#print axioms irrational_of_prime_fraction_bound
#print axioms rational_prime_successor
#print axioms rational_between_primes

end CarriedRationalPrimePattern
