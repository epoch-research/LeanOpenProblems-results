import Mathlib
import Submission.OccupancyLimit

/-!
# The direct first-occurrence defect for factorial residues

`U n` is the natural-number product of `n! / j! - 1` for `1 ≤ j < n`.
The quotients are exact, and their positivity ensures that subtraction of one
has no truncation issue. For a prime `p` and `n < p`, divisibility of `U n` by
`p` detects precisely whether `n! mod p` has occurred at an earlier positive
index.

A general ordered finite-map identity counts every non-first occurrence once,
not once per pair of equal values. It gives the exact factorial support defect.
The final section proves only an equivalence between the proposed support
limit and a normalized repetition-count limit, on the existing nontrivial
prime filter. Neither limit is asserted. This file does not import the
problem specification.
-/

set_option autoImplicit false
set_option warningAsError true

open scoped BigOperators

namespace FactorialDefect

section OrderedFiniteMap

variable {α β : Type*} [LinearOrder α] [DecidableEq β]

open scoped Classical in
/-- Image size plus the number of non-first occurrences is the source size.
Each repeated index is counted only once, even if it has several predecessors
with the same value. -/
theorem card_image_add_card_repeats (s : Finset α) (f : α → β) :
    (s.image f).card +
      (s.filter (fun x => ∃ y ∈ s, y < x ∧ f x = f y)).card = s.card := by
  classical
  let repeated : α → Prop := fun x => ∃ y ∈ s, y < x ∧ f x = f y
  let firsts := s.filter (fun x => ¬ repeated x)
  have himage : firsts.image f = s.image f := by
    apply Finset.Subset.antisymm
    · exact Finset.image_subset_image (Finset.filter_subset _ _)
    · intro b hb
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hb
      let fiber := s.filter (fun y => f y = f x)
      have hne : fiber.Nonempty := ⟨x, Finset.mem_filter.mpr ⟨hx, rfl⟩⟩
      let m := fiber.min' hne
      have hm : m ∈ fiber := fiber.min'_mem hne
      obtain ⟨hms, hmf⟩ := Finset.mem_filter.mp hm
      refine Finset.mem_image.mpr ⟨m, Finset.mem_filter.mpr ⟨hms, ?_⟩, hmf⟩
      rintro ⟨y, hys, hym, hf⟩
      have hy : y ∈ fiber := Finset.mem_filter.mpr ⟨hys, hf.symm.trans hmf⟩
      exact (not_lt_of_ge (fiber.min'_le y hy)) hym
  have hinj : Set.InjOn f firsts := by
    intro a ha b hb hab
    have hna := (Finset.mem_filter.mp ha).2
    have hnb := (Finset.mem_filter.mp hb).2
    rcases lt_trichotomy a b with hlt | heq | hgt
    · exact False.elim (hnb ⟨a, (Finset.mem_filter.mp ha).1, hlt, hab.symm⟩)
    · exact heq
    · exact False.elim (hna ⟨b, (Finset.mem_filter.mp hb).1, hgt, hab⟩)
  change (s.image f).card + (s.filter repeated).card = s.card
  calc
    (s.image f).card + (s.filter repeated).card =
        firsts.card + (s.filter repeated).card := by
      rw [← himage, Finset.card_image_of_injOn hinj]
    _ = s.card := by
      dsimp only [firsts]
      rw [Nat.add_comm]
      exact Finset.card_filter_add_card_filter_not repeated

open scoped Classical in
/-- For indices `1 ≤ n < N`, non-first occurrences automatically have `n ≥ 2`.
No assumptions on `N` or on the values of `f` are needed. -/
theorem card_image_Ico_add_card_repeats (f : ℕ → β) (N : ℕ) :
    ((Finset.Ico 1 N).image f).card +
      ((Finset.Ico 2 N).filter
        (fun n => ∃ j ∈ Finset.Ico 1 n, f n = f j)).card = N - 1 := by
  classical
  convert card_image_add_card_repeats (Finset.Ico 1 N) f using 2
  · congr 1
    ext n
    simp only [Finset.mem_filter, Finset.mem_Ico]
    constructor
    · rintro ⟨⟨hn2, hnN⟩, j, ⟨hj1, hjn⟩, heq⟩
      exact ⟨⟨by omega, hnN⟩, j, ⟨hj1, lt_trans hjn hnN⟩, hjn, heq⟩
    · rintro ⟨⟨hn1, hnN⟩, j, ⟨hj1, hjN⟩, hjn, heq⟩
      exact ⟨⟨by omega, hnN⟩, j, ⟨hj1, hjn⟩, heq⟩
  · exact (Nat.card_Ico 1 N).symm

end OrderedFiniteMap

/-- The requested product. It is defined for all natural numbers; for `n = 0,1`
the index set is empty and the product is one. -/
def U (n : ℕ) : ℕ :=
  ∏ j ∈ Finset.Ico 1 n, (n.factorial / j.factorial - 1)

@[simp] theorem U_zero : U 0 = 1 := by simp [U]

@[simp] theorem U_one : U 1 = 1 := by simp [U]

/-- Exactness of the natural division used in `U`. -/
theorem factorial_div_mul {j n : ℕ} (hjn : j ≤ n) :
    (n.factorial / j.factorial) * j.factorial = n.factorial :=
  Nat.div_mul_cancel (Nat.factorial_dvd_factorial hjn)

/-- There is no underflow when subtracting one from a quotient in `U`. -/
theorem factorial_div_pos {j n : ℕ} (hjn : j ≤ n) :
    0 < n.factorial / j.factorial :=
  Nat.div_pos (Nat.factorial_le hjn) (Nat.factorial_pos j)

/-- An optional division-free expression of exactly the same product, using
ascending factorials `(j+1)(j+2)⋯n`. -/
theorem U_eq_prod_ascFactorial (n : ℕ) :
    U n = ∏ j ∈ Finset.Ico 1 n, ((j + 1).ascFactorial (n - j) - 1) := by
  apply Finset.prod_congr rfl
  intro j hj
  have hjn := (Finset.mem_Ico.mp hj).2.le
  rw [Nat.ascFactorial_eq_div, Nat.add_sub_of_le hjn]

/-- Cancellation is valid because the smaller factorial is coprime to `p`.
This lemma includes the harmless case `j = n`. -/
theorem prime_dvd_factorial_div_sub_one_iff {p n j : ℕ}
    (hp : p.Prime) (hn : n < p) (hjn : j ≤ n) :
    p ∣ (n.factorial / j.factorial - 1) ↔
      n.factorial % p = j.factorial % p := by
  have hpos : 1 ≤ n.factorial / j.factorial := factorial_div_pos hjn
  have hmul := factorial_div_mul hjn
  have hcop := hp.coprime_factorial_of_lt (lt_of_le_of_lt hjn hn)
  rw [← Nat.modEq_iff_dvd' hpos]
  change Nat.ModEq p 1 (n.factorial / j.factorial) ↔
    Nat.ModEq p n.factorial j.factorial
  constructor
  · intro h
    simpa only [one_mul, hmul] using (h.mul_right j.factorial).symm
  · intro h
    apply Nat.ModEq.cancel_right_of_coprime hcop
    simpa only [one_mul, hmul] using h.symm

/-- Direct divisibility test for an earlier occurrence of the residue `n! mod p`.
In particular it applies on the requested range `2 ≤ n < p`. -/
theorem prime_dvd_U_iff {p n : ℕ} (hp : p.Prime) (hn : n < p) :
    p ∣ U n ↔ ∃ j ∈ Finset.Ico 1 n, n.factorial % p = j.factorial % p := by
  rw [U, hp.prime.dvd_finset_prod_iff]
  apply exists_congr
  intro j
  apply and_congr_right
  intro hj
  exact prime_dvd_factorial_div_sub_one_iff hp hn (Finset.mem_Ico.mp hj).2.le

/-- The exact support-defect identity. Each `n` with `p ∣ U n` contributes one
missing first occurrence, irrespective of how many earlier factorials agree. -/
theorem card_factorial_image_add_card_dvd_U {p : ℕ} (hp : p.Prime) :
    ((Finset.Ico 1 p).image (fun k => k.factorial % p)).card +
      ((Finset.Ico 2 p).filter (fun n => p ∣ U n)).card = p - 1 := by
  classical
  have hset :
      (Finset.Ico 2 p).filter
          (fun n => ∃ j ∈ Finset.Ico 1 n, n.factorial % p = j.factorial % p) =
        (Finset.Ico 2 p).filter (fun n => p ∣ U n) := by
    ext n
    simp only [Finset.mem_filter]
    apply and_congr_right
    intro hn
    exact (prime_dvd_U_iff hp (Finset.mem_Ico.mp hn).2).symm
  simpa only [hset] using
    card_image_Ico_add_card_repeats (fun k => k.factorial % p) p

/-- The number of indices `2 ≤ n < p` whose quotient product is divisible by `p`.
For prime `p`, these are precisely the non-first factorial residues. -/
def repetitionCount (p : ℕ) : ℕ :=
  ((Finset.Ico 2 p).filter (fun n => p ∣ U n)).card

/-- The repetition count is exactly the defect from `p - 1` distinct values. -/
theorem repetitionCount_eq_defect {p : ℕ} (hp : p.Prime) :
    repetitionCount p = p - 1 -
      ((Finset.Ico 1 p).image (fun k => k.factorial % p)).card := by
  have h := card_factorial_image_add_card_dvd_U hp
  change ((Finset.Ico 1 p).image (fun k => k.factorial % p)).card +
    repetitionCount p = p - 1 at h
  omega

section LimitEquivalence

open Filter OccupancyBounds.FactorialResidues
open scoped Topology

/-- The finite identity, using the support notation from `OccupancyLimit`. -/
theorem card_targets_add_repetitionCount {p : ℕ} (hp : p.Prime) :
    (targets p).card + repetitionCount p = p - 1 :=
  card_factorial_image_add_card_dvd_U hp

/-- The exact normalized identity. The numerator on the right uses natural
subtraction, as in the already-proved first-moment formula. -/
theorem normalized_card_targets_add_repetitionCount {p : ℕ} (hp : p.Prime) :
    ((targets p).card : ℝ) / p + (repetitionCount p : ℝ) / p =
      ((p - 1 : ℕ) : ℝ) / p := by
  rw [← add_div, ← Nat.cast_add, card_targets_add_repetitionCount hp]

/-- On the nontrivial prime filter, convergence of the normalized support to
`c` is equivalent to convergence of the normalized repetition count to `1-c`.
This is a complement identity for limits, not an estimate for either count. -/
theorem tendsto_card_targets_iff_repetitionCount (c : ℝ) :
    Tendsto (fun p : ℕ => ((targets p).card : ℝ) / p)
      primeFilter (𝓝 c) ↔
    Tendsto (fun p : ℕ => (repetitionCount p : ℝ) / p)
      primeFilter (𝓝 (1 - c)) := by
  have htotal : Tendsto (fun p : ℕ => ((p - 1 : ℕ) : ℝ) / p)
      primeFilter (𝓝 1) := by
    simpa only [moment_one] using tendsto_moment_one
  have hprime : ∀ᶠ p in primeFilter, p.Prime := by
    exact Filter.mem_inf_of_right (by simp)
  constructor
  · intro hs
    apply (htotal.sub hs).congr'
    filter_upwards [hprime] with p hp
    have h := normalized_card_targets_add_repetitionCount hp
    linarith
  · intro hr
    have h := htotal.sub hr
    have hc : (1 : ℝ) - (1 - c) = c := by ring
    rw [hc] at h
    apply h.congr'
    filter_upwards [hprime] with p hp
    have hsum := normalized_card_targets_add_repetitionCount hp
    linarith

/-- The exact support-limit proposition from the problem is equivalent to
`repetitionCount p / p → 1 / exp 1` along primes. Neither side is claimed here. -/
theorem support_limit_iff_repetitionCount_limit :
    Tendsto
      (fun p : ℕ =>
        (((Finset.Ico 1 p).image (fun k => k.factorial % p)).card : ℝ) / p)
      (atTop ⊓ Filter.principal {p : ℕ | p.Prime})
      (𝓝 (1 - 1 / Real.exp 1)) ↔
    Tendsto (fun p : ℕ => (repetitionCount p : ℝ) / p)
      (atTop ⊓ Filter.principal {p : ℕ | p.Prime})
      (𝓝 (1 / Real.exp 1)) := by
  have h := tendsto_card_targets_iff_repetitionCount (1 - 1 / Real.exp 1)
  have hc : (1 : ℝ) - (1 - 1 / Real.exp 1) = 1 / Real.exp 1 := by ring
  simpa only [targets, source, residue, primeFilter, hc] using h

end LimitEquivalence

end FactorialDefect

-- Kernel-axiom audits for the main finite and conditional results.
#print axioms FactorialDefect.card_image_add_card_repeats
#print axioms FactorialDefect.factorial_div_mul
#print axioms FactorialDefect.factorial_div_pos
#print axioms FactorialDefect.U_eq_prod_ascFactorial
#print axioms FactorialDefect.prime_dvd_U_iff
#print axioms FactorialDefect.card_factorial_image_add_card_dvd_U
#print axioms FactorialDefect.tendsto_card_targets_iff_repetitionCount
#print axioms FactorialDefect.support_limit_iff_repetitionCount_limit
#print axioms OccupancyBounds.FactorialResidues.primeFilter_neBot