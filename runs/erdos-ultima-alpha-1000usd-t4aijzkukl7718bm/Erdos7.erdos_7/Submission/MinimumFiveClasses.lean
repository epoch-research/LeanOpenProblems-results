import Submission.ArithmeticReduction
import Submission.ExchangePrivateTransfer

/-!
# Minimum cardinality for an ordinary distinct covering system

The digit Tarsi bound reduces a putative cover with at most four classes to
period at most eight. An exhaustive finite divisor table excludes these
periods. Thus the five-class even exchange control really is minimum-cardinal,
not just irredundant or minimal for its fixed set of modulus labels.

This concerns ordinary covers, including even moduli; it does not settle the
odd covering conjecture.
-/

namespace Erdos7MinimumFive
open scoped BigOperators
open Erdos7Reduction Erdos7Digits

/-- A simple period bound valid without an oddness assumption. -/
lemma period_le_two_pow_weight (N : ℕ) (hN : N ≠ 0) :
    N ≤ 2 ^ (∑ p ∈ N.primeFactors, N.factorization p * (p-1)) := by
  have heq : N = ∏ p ∈ N.primeFactors, p ^ N.factorization p := by
    simpa only [Finsupp.prod, Nat.support_factorization] using
      (Nat.factorization_prod_pow_eq_self hN).symm
  calc
    N = ∏ p ∈ N.primeFactors, p ^ N.factorization p := heq
    _ ≤ ∏ p ∈ N.primeFactors, (2 ^ (p-1)) ^ N.factorization p := by
      apply Finset.prod_le_prod'
      intro p hp
      apply Nat.pow_le_pow_left
      have hpos := (Nat.mem_primeFactors.mp hp).1.pos
      have h := Nat.lt_two_pow_self (n := p-1)
      omega
    _ = 2 ^ (∑ p ∈ N.primeFactors, N.factorization p * (p-1)) := by
      simp only [← pow_mul, Nat.mul_comm, Finset.prod_pow_eq_pow_sum]

/-- All nontrivial divisor labels at a small period, represented by a genuinely
finite type. -/
abbrev Labels (N : Fin 9) := {d : Fin 9 // 1 < d.val ∧ d.val ∣ N.val}

/-- Every assignment to ALL available nontrivial divisors leaves a hole. The
residues are allowed all values below nine, more than the period requires. -/
lemma small_period_table : ∀ N : Fin 9, 0 < N.val →
    ∀ a : Labels N → Fin 9, ∃ x : Fin 9, x.val < N.val ∧
      ∀ d : Labels N, ¬ (d.val.val : ℤ) ∣ (x.val : ℤ)-(a d).val := by
  decide +kernel

/-- Arithmetic lifting of the finite table. Missing divisor labels can be
assigned arbitrary phases; distinctness makes phases of present labels
unambiguous. -/
theorem no_small_period_cover {I : Type*} (m : I → ℕ) (a : I → ℤ)
    (hinj : Function.Injective m) (hm : ∀ i, 1 < m i)
    (N : ℕ) (hN : 0 < N) (hN8 : N ≤ 8) (hmN : ∀ i, m i ∣ N) :
    ¬ (∀ x : ℤ, ∃ i, (m i : ℤ) ∣ x-a i) := by
  classical
  intro hc
  let n : Fin 9 := ⟨N, by omega⟩
  have hnZ : 0 < (N : ℤ) := by exact_mod_cast hN
  let label (i : I) : Labels n :=
    ⟨⟨m i, by have := Nat.le_of_dvd hN (hmN i); omega⟩, hm i, hmN i⟩
  let b (d : Labels n) : Fin 9 :=
    if h : ∃ i, m i = d.val.val then
      ⟨(a (Classical.choose h) % (N : ℤ)).toNat, by
        have hlo := Int.emod_nonneg (a (Classical.choose h)) (ne_of_gt hnZ)
        have hhi := Int.emod_lt_of_pos (a (Classical.choose h)) hnZ
        omega⟩
    else 0
  have hb (i : I) : ((b (label i)).val : ℤ) = a i % (N : ℤ) := by
    dsimp only [b]
    split_ifs with h
    · have he : Classical.choose h = i := hinj (Classical.choose_spec h)
      simp only [he]
      exact Int.toNat_of_nonneg (Int.emod_nonneg _ (ne_of_gt hnZ))
    · exact False.elim (h ⟨i, rfl⟩)
  obtain ⟨x, _, hx⟩ := small_period_table n hN b
  obtain ⟨i, hi⟩ := hc x.val
  apply hx (label i)
  change (m i : ℤ) ∣ (x.val : ℤ)-(b (label i)).val
  rw [hb i]
  have hd : (m i : ℤ) ∣ (N : ℤ) := by exact_mod_cast hmN i
  have ha : (N : ℤ) ∣ a i-a i % (N : ℤ) := Int.dvd_self_sub_emod
  simpa only [sub_add_sub_cancel] using dvd_add hi (hd.trans ha)

/-- Every finite covering system of distinct nontrivial integer moduli has
at least five classes, whether or not its moduli are odd. -/
theorem five_le_card {I : Type*} [Fintype I] (m : I → ℕ) (a : I → ℤ)
    (hinj : Function.Injective m) (hm : ∀ i, 1 < m i)
    (hc : ∀ x : ℤ, ∃ i, (m i : ℤ) ∣ x-a i) : 5 ≤ Fintype.card I := by
  classical
  by_contra h
  have hcard : Fintype.card I ≤ 4 := by omega
  obtain ⟨s, hs, hpriv⟩ := arithmetic_irredundant_subcover m a hc
  let m' (i : s) := m i.val
  let a' (i : s) := a i.val
  have hm' (i : s) : m' i ≠ 0 := by have := hm i.val; dsimp [m']; omega
  have hc' : ∀ x : ℤ, ∃ i : s, (m' i : ℤ) ∣ x-a' i := by
    intro x
    obtain ⟨i, hi, hix⟩ := hs x
    exact ⟨⟨i, hi⟩, hix⟩
  have hp' : ∀ i : s, ∃ x : ℤ, ∀ j : s, j ≠ i → ¬ (m' j : ℤ) ∣ x-a' j := by
    intro i
    obtain ⟨x, hx⟩ := hpriv i.val i.property
    refine ⟨x, fun j hji => hx j.val j.property ?_⟩
    exact fun he => hji (Subtype.ext he)
  have hs4 : Fintype.card s ≤ 4 := by
    simpa only [Fintype.card_coe] using s.card_le_univ.trans hcard
  let N := Finset.univ.lcm m'
  have hN0 : N ≠ 0 := Finset.lcm_ne_zero_iff.mpr (fun i _ => hm' i)
  have hweight := arithmetic_irredundant_factorization_sum_bound m' a' hm' hc' hp'
  rw [← primeFactors_finset_lcm Finset.univ m' (fun i _ => hm' i)] at hweight
  change (∑ p ∈ N.primeFactors, N.factorization p * (p-1)) < Fintype.card s at hweight
  have hweight3 : (∑ p ∈ N.primeFactors, N.factorization p * (p-1)) ≤ 3 := by omega
  have hN8 : N ≤ 8 := (period_le_two_pow_weight N hN0).trans
    (by simpa using Nat.pow_le_pow_right (by decide : 0 < 2) hweight3)
  exact no_small_period_cover m' a'
    (fun i j hij => Subtype.ext (hinj hij)) (fun i => hm i.val)
    N (Nat.pos_of_ne_zero hN0) hN8 (fun i => Finset.dvd_lcm (Finset.mem_univ i)) hc'

/-- Ideal-valued version, with no oddness hypothesis. -/
theorem strict_cover_five (C : StrictCoveringSystem ℤ) :
    letI := C.fintypeIndex
    5 ≤ Fintype.card C.ι := by
  letI := C.fintypeIndex
  exact five_le_card (fun i => (C.moduli i).absNorm) C.residue
    (moduli_absNorm_injective C) (moduli_absNorm_gt_one C) (arithmetic_cover C)

/-- The old and new five-class controls therefore have minimum possible
cardinality among ALL ordinary strict covering systems, not just among their
fixed-label subfamilies. -/
theorem exchange_controls_minimum :
    (∀ x : ℤ, ∃ i, (Erdos7CompanionExchange.moduli i : ℤ) ∣
      x-Erdos7CompanionExchange.residues i) ∧
    (∀ x : ℤ, ∃ i, (Erdos7CompanionExchange.moduli i : ℤ) ∣
      x-Erdos7ExchangePrivateTransfer.newA i) ∧
    (∀ (C : StrictCoveringSystem ℤ),
      letI := C.fintypeIndex
      Fintype.card (Fin 5) ≤ Fintype.card C.ι) := by
  exact ⟨Erdos7CompanionExchange.control_cover,
    Erdos7ExchangePrivateTransfer.new_cover, fun C => by simpa using strict_cover_five C⟩

#print axioms period_le_two_pow_weight
#print axioms small_period_table
#print axioms no_small_period_cover
#print axioms five_le_card
#print axioms strict_cover_five
#print axioms exchange_controls_minimum

end Erdos7MinimumFive
