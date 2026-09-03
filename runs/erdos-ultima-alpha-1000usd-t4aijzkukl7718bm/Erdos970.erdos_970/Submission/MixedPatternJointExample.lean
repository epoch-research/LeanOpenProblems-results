import Submission.MixedPatternRescaling
import Submission.WheelFiniteCheck

/-! A joint-pattern inequality improves a finite interval bound beyond the tested
single-prime deletion recurrences. All finite wheel inputs are kernel checked.
No uniform quadratic estimate is asserted. -/
namespace Erdos970.MixedPattern.JointExample
open OptimalCoverCore BrunCriterion BlockSieve.SievePolynomial

/-- A computable count in a translated zero-residue wheel. -/
def wheelCount (P : Finset ℕ) (a m : ℕ) : ℕ :=
  Nat.count (fun i => ∀ p ∈ P, ¬a + i ≡ 0 [MOD p]) m

lemma fastWheel_eq (ps : List ℕ) (a m : ℕ) :
    fastWheel ps a m = wheelCount ps.toFinset a m := by
  have hb (i : ℕ) : ps.all (fun p => (a + i) % p != 0) = true ↔
      ∀ p ∈ ps.toFinset, ¬a + i ≡ 0 [MOD p] := by
    simp [List.all_eq_true, Nat.ModEq]
  induction m with
  | zero => simp [fastWheel, wheelCount]
  | succ m ih =>
    rw [show fastWheel ps a (m + 1) = fastWheel ps a m +
        (if ps.all (fun p => (a + m) % p != 0) then 1 else 0) by
      simp only [fastWheel, List.range_succ, List.filter_append, List.length_append,
        List.filter_singleton]
      cases ps.all (fun p => (a + m) % p != 0) <;> rfl]
    rw [ih]
    simp only [wheelCount, Nat.count_succ, hb m]

/-- Every residue configuration for a fixed prime set is a translate of its
zero-residue wheel. The translating parameter lies in one period. -/
theorem survivors_eq_wheelCount (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (m : ℕ) (r : ℕ → ℕ) :
    ∃ a < ∏ p ∈ P, p, (survivors m P r).card = wheelCount P a m := by
  classical
  let N := ∏ p ∈ P, p
  have hN : 0 < N := Finset.prod_pos (fun p hp => (hP p hp).pos)
  obtain ⟨b, hb⟩ := intersection_residue P hP r
  have hbr : ∀ p ∈ P, b ≡ r p [MOD p] := (hb b).mpr (Nat.ModEq.refl b)
  let a := ((N - 1) * b) % N
  have hab : a + b ≡ 0 [MOD N] := by
    have ha : a ≡ (N - 1) * b [MOD N] := by simp [a, Nat.ModEq]
    have he : (N - 1) * b + b = N * b := by nlinarith [Nat.sub_add_cancel hN]
    exact (ha.add_right b).trans (by rw [he]; simp [Nat.ModEq])
  have hbase (p : ℕ) (hp : p ∈ P) : a + r p ≡ 0 [MOD p] :=
    ((hbr p hp).symm.add_left a).trans
      (hab.of_dvd (Finset.dvd_prod_of_mem (fun p => p) hp))
  have hiff (i p : ℕ) (hp : p ∈ P) :
      i ≡ r p [MOD p] ↔ a + i ≡ 0 [MOD p] := by
    constructor
    · intro hi
      exact (hi.add_left a).trans (hbase p hp)
    · intro hi
      exact Nat.ModEq.add_left_cancel' a (hi.trans (hbase p hp).symm)
  refine ⟨a, Nat.mod_lt _ hN, ?_⟩
  unfold survivors wheelCount
  rw [Nat.count_eq_card_filter_range]
  congr 1
  ext i
  simp only [Finset.mem_filter]
  apply and_congr_right
  intro hi
  constructor <;> intro h p hp hbad
  · exact h p hp ((hiff i p hp).mpr hbad)
  · exact h p hp ((hiff i p hp).mp hbad)

/-- A finite check of the wheel proves a bound for every residue vector. -/
theorem bounds_of_wheel_check (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (m l u : ℕ)
    (hcheck : ∀ a : Fin (∏ p ∈ P, p), l ≤ wheelCount P a m ∧ wheelCount P a m ≤ u)
    (r : ℕ → ℕ) : l ≤ (survivors m P r).card ∧ (survivors m P r).card ≤ u := by
  obtain ⟨a, ha, he⟩ := survivors_eq_wheelCount P hP m r
  rw [he]
  exact hcheck ⟨a, ha⟩

lemma survivor_count_sum (m : ℕ) (P : Finset ℕ) (r : ℕ → ℕ) :
    (survivors m P r).card =
      ∑ i ∈ Finset.range m, if ∀ p ∈ P, ¬i ≡ r p [MOD p] then 1 else 0 := by
  classical
  simp only [survivors, Finset.card_eq_sum_ones, Finset.sum_filter]

/-- A three-way avoidance inequality combining three pairwise counts. -/
theorem three_pair_avoidance_le (m : ℕ) (S : Finset ℕ) (p q t : ℕ) (r : ℕ → ℕ) :
    (survivors m (S ∪ {p, q}) r).card + (survivors m (S ∪ {p, t}) r).card +
      (survivors m (S ∪ {q, t}) r).card ≤
        (survivors m S r).card + 2 * (survivors m (S ∪ {p, q, t}) r).card := by
  classical
  simp only [survivor_count_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  by_cases hS : ∀ v ∈ S, ¬i ≡ r v [MOD v] <;>
    by_cases hp : i ≡ r p [MOD p] <;>
    by_cases hq : i ≡ r q [MOD q] <;>
    by_cases ht : i ≡ r t [MOD t] <;>
    simp [hS, hp, hq, ht] <;> split_ifs <;> omega

lemma wheel_checks :
    (∀ a : Fin (3 * 11 * 17), 38 ≤ wheelCount {3, 11, 17} a 69) ∧
    (∀ a : Fin (3 * 5 * 17), 33 ≤ wheelCount {3, 5, 17} a 69) ∧
    (∀ a : Fin (3 * 5 * 11), 32 ≤ wheelCount {3, 5, 11} a 69) ∧
    (∀ a : Fin 3, wheelCount {3} a 69 ≤ 46) := by
  have h := fast_check_verified
  simp only [fastCheck, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a
    have hh := h.1.1.1 a.val (List.mem_range.mpr a.isLt)
    simpa only [fastWheel_eq, List.toFinset_cons, List.toFinset_nil] using hh
  · intro a
    have hh := h.1.1.2 a.val (List.mem_range.mpr a.isLt)
    simpa only [fastWheel_eq, List.toFinset_cons, List.toFinset_nil] using hh
  · intro a
    have hh := h.1.2 a.val (List.mem_range.mpr a.isLt)
    simpa only [fastWheel_eq, List.toFinset_cons, List.toFinset_nil] using hh
  · intro a
    have hh := h.2 a.val (List.mem_range.mpr a.isLt)
    simpa only [fastWheel_eq, List.toFinset_cons, List.toFinset_nil] using hh


lemma triple_lower_31117 (r : ℕ → ℕ) : 38 ≤ (survivors 69 {3, 11, 17} r).card := by
  have hP : ∀ p ∈ ({3, 11, 17} : Finset ℕ), p.Prime := by decide
  apply (bounds_of_wheel_check {3, 11, 17} hP 69 38 69 ?_ r).1
  intro a
  constructor
  · convert wheel_checks.1 ⟨a.val, by simpa using a.isLt⟩ using 1
  · unfold wheelCount
    exact Nat.count_le _

lemma triple_lower_3517 (r : ℕ → ℕ) : 33 ≤ (survivors 69 {3, 5, 17} r).card := by
  have hP : ∀ p ∈ ({3, 5, 17} : Finset ℕ), p.Prime := by decide
  apply (bounds_of_wheel_check {3, 5, 17} hP 69 33 69 ?_ r).1
  intro a
  constructor
  · convert wheel_checks.2.1 ⟨a.val, by simpa using a.isLt⟩ using 1
  · unfold wheelCount
    exact Nat.count_le _

lemma triple_lower_3511 (r : ℕ → ℕ) : 32 ≤ (survivors 69 {3, 5, 11} r).card := by
  have hP : ∀ p ∈ ({3, 5, 11} : Finset ℕ), p.Prime := by decide
  apply (bounds_of_wheel_check {3, 5, 11} hP 69 32 69 ?_ r).1
  intro a
  constructor
  · convert wheel_checks.2.2.1 ⟨a.val, by simpa using a.isLt⟩ using 1
  · unfold wheelCount
    exact Nat.count_le _

lemma singleton_upper (r : ℕ → ℕ) : (survivors 69 {3} r).card ≤ 46 := by
  have hP : ∀ p ∈ ({3} : Finset ℕ), p.Prime := by decide
  apply (bounds_of_wheel_check {3} hP 69 0 46 ?_ r).2
  intro a
  refine ⟨Nat.zero_le _, ?_⟩
  convert wheel_checks.2.2.2 ⟨a.val, by simpa using a.isLt⟩ using 1

/-- Three pairwise bounds yield 2*S >=57, hence S>=29 by integrality. -/
theorem four_prime_survivors_ge_twenty_nine (r : ℕ → ℕ) :
    29 ≤ (survivors 69 {3, 5, 11, 17} r).card := by
  have hh := three_pair_avoidance_le 69 {3} 5 11 17 r
  have he₁ : ({3} ∪ {5, 11} : Finset ℕ) = {3, 5, 11} := by decide
  have he₂ : ({3} ∪ {5, 17} : Finset ℕ) = {3, 5, 17} := by decide
  have he₃ : ({3} ∪ {11, 17} : Finset ℕ) = {3, 11, 17} := by decide
  have he₄ : ({3} ∪ {5, 11, 17} : Finset ℕ) = {3, 5, 11, 17} := by decide
  rw [he₁, he₂, he₃, he₄] at hh
  have h₁ := triple_lower_3511 r
  have h₂ := triple_lower_3517 r
  have h₃ := triple_lower_31117 r
  have h₄ := singleton_upper r
  omega

lemma survivors_antitone_primes {m : ℕ} {P Q : Finset ℕ} (h : Q ⊆ P) (r : ℕ → ℕ) :
    survivors m P r ⊆ survivors m Q r := by
  intro x hx
  obtain ⟨hxm, hxP⟩ := (mem_survivors _ _ _ _).mp hx
  exact (mem_survivors _ _ _ _).mpr ⟨hxm, fun q hq => hxP q (h hq)⟩

lemma mixed_insert_partition (m : ℕ) (P : Finset ℕ) (p : ℕ) (r : ℕ → ℕ) :
    mixedCount m {p} P r + (survivors m (insert p P) r).card =
      (survivors m P r).card := by
  classical
  have hh := Finset.card_filter_add_card_filter_not (s := survivors m P r)
    (fun x => x ≡ r p [MOD p])
  simpa [mixedCount, positions, survivors, Finset.filter_filter, and_comm] using hh

lemma insert_lower (m : ℕ) (P : Finset ℕ) (p l u : ℕ)
    (hP : ∀ q ∈ P, q.Prime) (hp : p.Prime) (hpP : p ∉ P)
    (hl : ∀ r, l ≤ (survivors m P r).card)
    (hu : ∀ s, (survivors (ceilQuotient m p) P s).card ≤ u) (r : ℕ → ℕ) :
    l - u ≤ (survivors m (insert p P) r).card := by
  have hprime : ∀ q ∈ ({p} : Finset ℕ), q.Prime := by simpa using hp
  have hdis : Disjoint ({p} : Finset ℕ) P := by simpa using hpP
  obtain ⟨c, t, hc, hcu, he⟩ := mixedCount_rescale m {p} P r hprime hP hdis
  simp only [Finset.prod_singleton] at hcu
  have hupper : mixedCount m {p} P r ≤ u := by
    rw [he]
    exact (Finset.card_le_card (survivors_mono_length P t hcu)).trans (hu t)
  have hh := mixed_insert_partition m P p r
  have hh' := hl r
  omega

lemma small_wheel_checks :
    (∀ a : Fin 15, wheelCount {3, 5} a 10 ≤ 6) ∧
    (∀ a : Fin 3, wheelCount {3} a 6 ≤ 4) := by
  decide +kernel

lemma two_prime_upper_ten (s : ℕ → ℕ) : (survivors 10 {3, 5} s).card ≤ 6 := by
  apply (bounds_of_wheel_check {3, 5} (by decide) 10 0 6 ?_ s).2
  intro a
  refine ⟨Nat.zero_le _, ?_⟩
  convert small_wheel_checks.1 ⟨a.val, by simpa using a.isLt⟩ using 1

lemma one_prime_upper_six (s : ℕ → ℕ) : (survivors 6 {3} s).card ≤ 4 := by
  apply (bounds_of_wheel_check {3} (by decide) 6 0 4 ?_ s).2
  intro a
  refine ⟨Nat.zero_le _, ?_⟩
  convert small_wheel_checks.2 ⟨a.val, by simpa using a.isLt⟩ using 1

lemma five_prime_survivors_ge_twenty_three (r : ℕ → ℕ) :
    23 ≤ (survivors 69 {3, 5, 7, 11, 17} r).card := by
  have hh := insert_lower 69 {3, 5, 11, 17} 7 29 6 (by decide) (by decide)
    (by decide) four_prime_survivors_ge_twenty_nine (fun s => ?_) r
  · have he : (insert 7 {3, 5, 11, 17} : Finset ℕ) = {3, 5, 7, 11, 17} := by decide
    simpa only [he] using hh
  · change (survivors 10 {3, 5, 11, 17} s).card ≤ 6
    exact (Finset.card_le_card (survivors_antitone_primes (by decide :
      ({3, 5} : Finset ℕ) ⊆ {3, 5, 11, 17}) s)).trans (two_prime_upper_ten s)

/-- The improved joint bound survives two further prime deletions. -/
theorem six_prime_survivors_ge_nineteen (r : ℕ → ℕ) :
    19 ≤ (survivors 69 {3, 5, 7, 11, 13, 17} r).card := by
  have hh := insert_lower 69 {3, 5, 7, 11, 17} 13 23 4 (by decide) (by decide)
    (by decide) five_prime_survivors_ge_twenty_three (fun s => ?_) r
  · have he : (insert 13 {3, 5, 7, 11, 17} : Finset ℕ) = {3, 5, 7, 11, 13, 17} := by decide
    simpa only [he] using hh
  · change (survivors 6 {3, 5, 7, 11, 17} s).card ≤ 4
    exact (Finset.card_le_card (survivors_antitone_primes (by decide :
      ({3} : Finset ℕ) ⊆ {3, 5, 7, 11, 17}) s)).trans (one_prime_upper_six s)

#print axioms wheel_checks
#print axioms three_pair_avoidance_le
#print axioms four_prime_survivors_ge_twenty_nine
#print axioms six_prime_survivors_ge_nineteen
end Erdos970.MixedPattern.JointExample
