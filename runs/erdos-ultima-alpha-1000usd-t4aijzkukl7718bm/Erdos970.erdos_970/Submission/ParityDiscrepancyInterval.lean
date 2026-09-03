import Submission.ParityDiscrepancyEnergy

/-! The alternating profile is an actual parity discrepancy of surviving
positions in an interval of odd prime-product length. -/
namespace Erdos970.ParityDiscrepancy
open Finset

def survivorIndicator (P : Finset ℕ) (a : ℕ) : ℚ := if ∀ p ∈ P, ¬p ∣ a then 1 else 0

def alternatingCount (P : Finset ℕ) (a m : ℕ) : ℚ :=
  ∑ j ∈ range m, (-1) ^ j * survivorIndicator P (a + j)

lemma primeProduct_dvd_iff (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (a : ℕ) :
    primeProduct P ∣ a ↔ ∀ p ∈ P, p ∣ a := by
  induction P using Finset.induction_on with
  | empty => simp [primeProduct]
  | @insert p P hp ih =>
    have hpp := hP p (mem_insert_self _ _)
    have hP' : ∀ q ∈ P, q.Prime := fun q hq => hP q (mem_insert_of_mem hq)
    have hco : p.Coprime (primeProduct P) := by
      apply Nat.coprime_prod_right_iff.mpr
      intro q hq
      exact (Nat.coprime_primes hpp (hP' q hq)).mpr (fun heq => hp (heq ▸ hq))
    simp only [primeProduct, prod_insert hp, forall_mem_insert]
    constructor
    · intro h
      exact ⟨dvd_trans (dvd_mul_right _ _) h,
        (ih hP').mp (dvd_trans (dvd_mul_left _ _) h)⟩
    · rintro ⟨hpa, hPa⟩
      exact hco.mul_dvd_of_dvd_of_dvd hpa ((ih hP').mpr hPa)

lemma survivorIndicator_inclusion (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (a : ℕ) :
    survivorIndicator P a =
      ∑ Q ∈ P.powerset, (-1 : ℚ) ^ Q.card * (if primeProduct Q ∣ a then 1 else 0) := by
  have hprod : (∏ p ∈ P, ((1 : ℚ) - if p ∣ a then 1 else 0)) = survivorIndicator P a := by
    have hterm (p : ℕ) : ((1 : ℚ) - if p ∣ a then 1 else 0) = if ¬p ∣ a then 1 else 0 := by
      split_ifs <;> norm_num at *
    simp_rw [hterm]
    simp only [prod_ite_zero, prod_const_one, survivorIndicator]
  rw [← hprod, prod_sub]
  apply sum_congr rfl
  intro Q hQ
  simp only [primeProduct_dvd_iff Q (fun p hp => hP p (mem_powerset.mp hQ hp)),
    prod_const_one, mul_one, prod_ite_zero]

lemma profile_succ (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime ∧ Odd p) (a : ℕ) :
    profile P a + profile P (a + 1) = 2 * survivorIndicator P (a + 1) := by
  rw [survivorIndicator_inclusion P (fun p hp => (hP p hp).1)]
  simp only [profile, ← sum_add_distrib, mul_sum]
  apply sum_congr rfl
  intro Q hQ
  rw [← mul_add, residueSign_succ _ _ (primeProduct_odd Q
    (fun p hp => (hP p (mem_powerset.mp hQ hp)).2))]
  split_ifs <;> ring

lemma profile_period (P : Finset ℕ) (a t : ℕ) :
    profile P (a + primeProduct P * t) = profile P a := by
  apply sum_congr rfl
  intro Q hQ
  have hd : primeProduct Q ∣ primeProduct P := prod_dvd_prod_of_subset Q P (fun p : ℕ => p) (mem_powerset.mp hQ)
  obtain ⟨v, hv⟩ := hd
  rw [hv, mul_assoc, residueSign_period]

/-- Telescoping identifies the profile with a signed count of actual survivors.
Any odd multiple of the complete period gives the same discrepancy. -/
theorem alternatingCount_odd_period (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime ∧ Odd p)
    (a t : ℕ) (ht : Odd t) :
    alternatingCount P (a + 1) (primeProduct P * t) = profile P a := by
  let N := primeProduct P * t
  let F := fun j => (-1 : ℚ) ^ j * profile P (a + j)
  have hN : Odd N := (primeProduct_odd P (fun p hp => (hP p hp).2)).mul ht
  have hterm (j : ℕ) : F j - F (j + 1) =
      2 * ((-1 : ℚ) ^ j * survivorIndicator P (a + 1 + j)) := by
    have hs := profile_succ P hP (a + j)
    dsimp only [F]
    rw [pow_succ]
    have heq : a + (j + 1) = a + j + 1 := by omega
    have heq' : a + 1 + j = a + j + 1 := by omega
    rw [heq, heq']
    linear_combination ((-1 : ℚ) ^ j) * hs
  have hh := sum_congr (s₁ := range N) rfl (fun j _ => hterm j)
  rw [sum_range_sub', ← mul_sum] at hh
  change F 0 - F N = 2 * alternatingCount P (a + 1) N at hh
  dsimp only [F] at hh
  rw [pow_zero, one_mul, Nat.add_zero, hN.neg_one_pow,
    show profile P (a + N) = profile P a from profile_period P a t] at hh
  dsimp only [N] at hh
  linarith

/-- This energy identity is about genuine interval parity counts, not a synthetic
moment population. -/
theorem alternatingCount_energy (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime ∧ Odd p)
    (t : ℕ) (ht : Odd t) :
    (∑ a ∈ range (primeProduct P), alternatingCount P (a + 1) (primeProduct P * t) ^ 2) =
      (primeProduct P : ℚ) * ∏ p ∈ P, (2 - 2 / (p : ℚ)) := by
  simp_rw [alternatingCount_odd_period P hP _ t ht]
  exact profile_energy P hP

lemma alternatingCount_eq_card_difference (P : Finset ℕ) (a m : ℕ) :
    alternatingCount P a m =
      (((range m).filter (fun j => Even j ∧ ∀ p ∈ P, ¬p ∣ a + j)).card : ℚ) -
        (((range m).filter (fun j => Odd j ∧ ∀ p ∈ P, ¬p ∣ a + j)).card : ℚ) := by
  rw [← sum_boole, ← sum_boole, ← sum_sub_distrib]
  apply sum_congr rfl
  intro j hj
  simp only [neg_one_pow_eq_ite, survivorIndicator]
  rcases Nat.even_or_odd j with he | ho
  · have hn : ¬Odd j := by
      obtain ⟨x, hx⟩ := he
      rintro ⟨y, hy⟩
      omega
    simp [he, hn]
  · have hn : ¬Even j := by
      obtain ⟨x, hx⟩ := ho
      rintro ⟨y, hy⟩
      omega
    simp only [ho, hn, if_false, true_and, false_and, zero_sub]
    split_ifs <;> norm_num

#print axioms alternatingCount_energy
#print axioms alternatingCount_eq_card_difference
end Erdos970.ParityDiscrepancy
