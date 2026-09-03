import Submission.TwoSidedFactorPacking

/-! Products of losing integers with a common winning prime. The new winner
is only bounded below by the old winner; factorization multiplicities are
retained in the weighted identity. -/
namespace Erdos371
open Finset

/-- Equal input orientations force a fall at the product minus one;
opposite orientations force a rise at the product. -/
def losingProductIndex (n m : ℕ) : ℕ :=
  if (Nat.maxPrimeFac n < Nat.maxPrimeFac (n+1) ↔
      Nat.maxPrimeFac m < Nat.maxPrimeFac (m+1))
  then losingNumber n * losingNumber m - 1
  else losingNumber n * losingNumber m

lemma losingNumber_residue (n : ℕ) (hn : 1 < n) :
    (losingNumber n : ZMod (primeWinner n)) =
      if Nat.maxPrimeFac n < Nat.maxPrimeFac (n+1) then -1 else 1 := by
  have hw := (comparison_numbers_prime_factors n hn).2.2
  have hd : primeWinner n ∣ winningNumber n := by
    rw [← hw]
    exact Nat.maxPrimeFac_dvd
  have hz := (ZMod.natCast_eq_zero_iff (winningNumber n) (primeWinner n)).mpr hd
  by_cases h : Nat.maxPrimeFac n < Nat.maxPrimeFac (n+1)
  · simp only [winningNumber, if_pos h, Nat.cast_add, Nat.cast_one] at hz
    simpa only [losingNumber, if_pos h] using (eq_neg_iff_add_eq_zero.mpr hz)
  · simp only [losingNumber, if_neg h, Nat.cast_add, Nat.cast_one,
      show (n : ZMod (primeWinner n)) = 0 by simpa [winningNumber, h] using hz,
      zero_add]

lemma losingProductIndex_structure (n m : ℕ) (hn : 1 < n) (hm : 1 < m)
    (hp : primeWinner n = primeWinner m) :
    1 < losingProductIndex n m ∧
    losingNumber (losingProductIndex n m) = losingNumber n * losingNumber m ∧
    primeWinner n ≤ primeWinner (losingProductIndex n m) ∧
    factorSign (losingProductIndex n m) = -(factorSign n * factorSign m) := by
  let L := losingNumber n * losingNumber m
  have hnl := (comparison_numbers_bounds n hn).1
  have hml := (comparison_numbers_bounds m hm).1
  have hL : 3 < L := by dsimp [L]; nlinarith
  have hprod : Nat.maxPrimeFac L < primeWinner n := by
    dsimp [L]
    rw [Nat.maxPrimeFac_mul (by omega : losingNumber n ≠ 0)
      (by omega : losingNumber m ≠ 0)]
    exact max_lt (comparison_numbers_prime_factors n hn).2.1
      (hp ▸ (comparison_numbers_prime_factors m hm).2.1)
  have hprime := (comparison_numbers_prime_factors n hn).1
  have hnr := losingNumber_residue n hn
  have hmr := losingNumber_residue m hm
  rw [← hp] at hmr
  have hres : (L : ZMod (primeWinner n)) =
      (if Nat.maxPrimeFac n < Nat.maxPrimeFac (n+1) then -1 else 1) *
      (if Nat.maxPrimeFac m < Nat.maxPrimeFac (m+1) then -1 else 1) := by
    dsimp [L]
    rw [Nat.cast_mul, hnr, hmr]
  by_cases he : (Nat.maxPrimeFac n < Nat.maxPrimeFac (n+1) ↔
      Nat.maxPrimeFac m < Nat.maxPrimeFac (m+1))
  · have hi : losingProductIndex n m = L-1 := if_pos he
    have hres1 : (L : ZMod (primeWinner n)) = 1 := by
      by_cases h : Nat.maxPrimeFac n < Nat.maxPrimeFac (n+1)
      · simpa only [if_pos h, if_pos (he.mp h), neg_mul_neg, one_mul] using hres
      · simpa only [if_neg h, if_neg (fun hm => h (he.mpr hm)), one_mul] using hres
    have hd : primeWinner n ∣ L-1 := by
      apply (ZMod.natCast_eq_zero_iff _ _).mp
      rw [Nat.cast_sub (by omega : 1 ≤ L), Nat.cast_one, hres1, sub_self]
    have hw : primeWinner n ≤ Nat.maxPrimeFac (L-1) :=
      Nat.le_maxPrimeFac (by omega) hprime hd
    have hf : Nat.maxPrimeFac L < Nat.maxPrimeFac (L-1) := hprod.trans_le hw
    have hsucc : L-1+1 = L := by omega
    have hnot : ¬Nat.maxPrimeFac (L-1) < Nat.maxPrimeFac (L-1+1) := by
      rw [hsucc]
      exact hf.not_gt
    refine ⟨by omega, ?_, ?_, ?_⟩
    · rw [hi]
      change (if Nat.maxPrimeFac (L-1) < Nat.maxPrimeFac (L-1+1)
        then L-1 else L-1+1) = L
      rw [if_neg hnot, hsucc]
    · simpa only [hi, primeWinner, hsucc, max_eq_left hf.le] using hw
    · rw [hi]
      simp only [factorSign, predicateSign, if_neg hnot]
      by_cases h : Nat.maxPrimeFac n < Nat.maxPrimeFac (n+1)
      · simp [h, he.mp h]
      · have hm' : ¬Nat.maxPrimeFac m < Nat.maxPrimeFac (m+1) := fun hm' => h (he.mpr hm')
        simp [h, hm']
  · have hi : losingProductIndex n m = L := if_neg he
    have hres1 : (L : ZMod (primeWinner n)) = -1 := by
      by_cases h : Nat.maxPrimeFac n < Nat.maxPrimeFac (n+1)
      · have hm' : ¬Nat.maxPrimeFac m < Nat.maxPrimeFac (m+1) :=
          fun hm' => he ⟨fun _ => hm', fun _ => h⟩
        simpa only [if_pos h, if_neg hm', mul_one] using hres
      · have hm' : Nat.maxPrimeFac m < Nat.maxPrimeFac (m+1) := by tauto
        simpa only [if_neg h, if_pos hm', one_mul] using hres
    have hd : primeWinner n ∣ L+1 := by
      apply (ZMod.natCast_eq_zero_iff _ _).mp
      rw [Nat.cast_add, Nat.cast_one, hres1, neg_add_cancel]
    have hw : primeWinner n ≤ Nat.maxPrimeFac (L+1) :=
      Nat.le_maxPrimeFac (by omega) hprime hd
    have hr : Nat.maxPrimeFac L < Nat.maxPrimeFac (L+1) := hprod.trans_le hw
    refine ⟨by omega, ?_, ?_, ?_⟩
    · rw [hi]
      change (if Nat.maxPrimeFac L < Nat.maxPrimeFac (L+1) then L else L+1) = L
      rw [if_pos hr]
    · simpa only [hi, primeWinner, max_eq_right hr.le] using hw
    · rw [hi]
      simp only [factorSign, predicateSign, if_pos hr]
      by_cases h : Nat.maxPrimeFac n < Nat.maxPrimeFac (n+1)
      · have hm' : ¬Nat.maxPrimeFac m < Nat.maxPrimeFac (m+1) := by tauto
        simp [h, hm']
      · have hm' : Nat.maxPrimeFac m < Nat.maxPrimeFac (m+1) := by tauto
        simp [h, hm']

/-- The exact loser label is the maximum of the two original loser labels. -/
lemma losingProductIndex_loser (n m : ℕ) (hn : 1 < n) (hm : 1 < m)
    (hp : primeWinner n = primeWinner m) :
    Nat.maxPrimeFac (losingNumber (losingProductIndex n m)) =
      max (Nat.maxPrimeFac (losingNumber n)) (Nat.maxPrimeFac (losingNumber m)) := by
  rw [(losingProductIndex_structure n m hn hm hp).2.1]
  exact Nat.maxPrimeFac_mul
    (by have := (comparison_numbers_bounds n hn).1; omega)
    (by have := (comparison_numbers_bounds m hm).1; omega)

/-- Away from the prime two, a losing integer has at most one comparison
with a prescribed winner. Otherwise that prime would divide both neighbors. -/
lemma losingNumber_injective_at_winner (n m p : ℕ) (hn : 1 < n) (hm : 1 < m)
    (hp : 2 < p) (hnp : primeWinner n = p) (hmp : primeWinner m = p)
    (he : losingNumber n = losingNumber m) : n = m := by
  have hdn : p ∣ winningNumber n := by
    rw [← hnp, ← (comparison_numbers_prime_factors n hn).2.2]
    exact Nat.maxPrimeFac_dvd
  have hdm : p ∣ winningNumber m := by
    rw [← hmp, ← (comparison_numbers_prime_factors m hm).2.2]
    exact Nat.maxPrimeFac_dvd
  by_cases hrn : Nat.maxPrimeFac n < Nat.maxPrimeFac (n+1)
  · by_cases hrm : Nat.maxPrimeFac m < Nat.maxPrimeFac (m+1)
    · simpa only [losingNumber, if_pos hrn, if_pos hrm] using he
    · simp only [losingNumber, if_pos hrn, if_neg hrm] at he
      simp only [winningNumber, if_pos hrn] at hdn
      simp only [winningNumber, if_neg hrm] at hdm
      have hd : p ∣ 2 := by
        have ht := Nat.dvd_sub hdn hdm
        simpa only [he, show m+1+1-m=2 by omega] using ht
      have := Nat.le_of_dvd (by decide : 0 < 2) hd
      omega
  · by_cases hrm : Nat.maxPrimeFac m < Nat.maxPrimeFac (m+1)
    · simp only [losingNumber, if_neg hrn, if_pos hrm] at he
      simp only [winningNumber, if_neg hrn] at hdn
      simp only [winningNumber, if_pos hrm] at hdm
      have hd : p ∣ 2 := by
        have ht := Nat.dvd_sub hdm hdn
        simpa only [← he, show n+1+1-n=2 by omega] using ht
      have := Nat.le_of_dvd (by decide : 0 < 2) hd
      omega
    · simp only [losingNumber, if_neg hrn, if_neg hrm] at he
      omega

/-- All representation multiplicities are retained: each ordered pair in a
fixed-product fibre gives a different divisor of that product. -/
theorem losing_product_fibre_card_le (S : Finset ℕ) (p L : ℕ) (hp : 2 < p)
    (hS : ∀ n ∈ S, 1 < n ∧ primeWinner n = p) :
    ((S ×ˢ S).filter (fun nm => losingNumber nm.1 * losingNumber nm.2 = L)).card ≤
      L.divisors.card := by
  apply Finset.card_le_card_of_injOn (fun nm : ℕ × ℕ => losingNumber nm.1)
  · intro nm hnm
    obtain ⟨hnmS, hnmL⟩ := mem_filter.mp hnm
    obtain ⟨hn, hm⟩ := mem_product.mp hnmS
    have ha := (comparison_numbers_bounds nm.1 (hS nm.1 hn).1).1
    have hb := (comparison_numbers_bounds nm.2 (hS nm.2 hm).1).1
    apply Nat.mem_divisors.mpr
    refine ⟨⟨losingNumber nm.2, hnmL.symm⟩, ?_⟩
    rw [← hnmL]
    exact mul_ne_zero (by omega) (by omega)
  · intro nm hnm kl hkl he
    obtain ⟨hnmS, hnmL⟩ := mem_filter.mp hnm
    obtain ⟨hklS, hklL⟩ := mem_filter.mp hkl
    obtain ⟨hn, hm⟩ := mem_product.mp hnmS
    obtain ⟨hk, hl⟩ := mem_product.mp hklS
    have hfirst : nm.1 = kl.1 := losingNumber_injective_at_winner _ _ p
      (hS _ hn).1 (hS _ hk).1 hp (hS _ hn).2 (hS _ hk).2 he
    have ha : losingNumber nm.1 ≠ 0 := by
      have := (comparison_numbers_bounds nm.1 (hS nm.1 hn).1).1
      omega
    have hsecond : nm.2 = kl.2 := by
      apply losingNumber_injective_at_winner _ _ p
        (hS _ hm).1 (hS _ hl).1 hp (hS _ hm).2 (hS _ hl).2
      apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero ha)
      rw [hnmL, hfirst, hklL]
    exact Prod.ext hfirst hsecond

/-- The output fixes the product exactly, not merely up to a shift by one. -/
theorem losingProductIndex_fibre_card_le (S : Finset ℕ) (p r : ℕ) (hp : 2 < p)
    (hS : ∀ n ∈ S, 1 < n ∧ primeWinner n = p) :
    ((S ×ˢ S).filter (fun nm => losingProductIndex nm.1 nm.2 = r)).card ≤
      (losingNumber r).divisors.card := by
  have hsub : (S ×ˢ S).filter (fun nm => losingProductIndex nm.1 nm.2 = r) ⊆
      (S ×ˢ S).filter (fun nm => losingNumber nm.1 * losingNumber nm.2 = losingNumber r) := by
    intro nm hnm
    obtain ⟨hnmS, hnmR⟩ := mem_filter.mp hnm
    obtain ⟨hn, hm⟩ := mem_product.mp hnmS
    refine mem_filter.mpr ⟨hnmS, ?_⟩
    have hs := (losingProductIndex_structure nm.1 nm.2
      (hS _ hn).1 (hS _ hm).1 ((hS _ hn).2.trans (hS _ hm).2.symm)).2.1
    rw [hnmR] at hs
    exact hs.symm
  exact (Finset.card_le_card hsub).trans
    (losing_product_fibre_card_le S p (losingNumber r) hp hS)

/-- This identity keeps every ordered pair, including diagonal pairs.
It does not replace the product pushforward by uniform sampling. -/
theorem weighted_losingProduct_square (S : Finset ℕ) (p : ℕ) (w : ℕ → ℝ)
    (hS : ∀ n ∈ S, 1 < n ∧ primeWinner n = p) :
    (∑ n ∈ S, w n * factorSign n)^2 =
      -(∑ n ∈ S, ∑ m ∈ S, w n * w m * factorSign (losingProductIndex n m)) := by
  rw [sq, sum_mul_sum, ← sum_neg_distrib]
  apply sum_congr rfl
  intro n hn
  rw [← sum_neg_distrib]
  apply sum_congr rfl
  intro m hm
  rw [(losingProductIndex_structure n m (hS n hn).1 (hS m hm).1
    ((hS n hn).2.trans (hS m hm).2.symm)).2.2.2]
  ring

/-- The winner need not be preserved: squaring the losing integer of the
comparison at 3 produces the comparison at 15, with winning prime 5. -/
lemma losingProduct_winner_increases :
    primeWinner 3 = 3 ∧ losingProductIndex 3 3 = 15 ∧ primeWinner 15 = 5 := by
  decide +kernel

#print axioms losingNumber_residue
#print axioms losingProductIndex_structure
#print axioms losingNumber_injective_at_winner
#print axioms losing_product_fibre_card_le
#print axioms losingProductIndex_fibre_card_le
#print axioms weighted_losingProduct_square
#print axioms losingProduct_winner_increases
end Erdos371
