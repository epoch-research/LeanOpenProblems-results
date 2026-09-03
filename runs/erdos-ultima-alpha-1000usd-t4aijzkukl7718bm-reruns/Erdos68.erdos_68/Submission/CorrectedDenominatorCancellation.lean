import Submission.CorrectedApprox

/-!
# A reduced-denominator cancellation at N = 137

This is not a disproof of Erdős 68. It refutes the auxiliary claim that the
last included denominator must divide the reduced denominator of either the
partial sum or its strict upper correction.

The prime 139 divides 137! - 1. Its contributions at the factorial indices
69, 122, and 137 cancel in the reduced partial sum through 137.
-/

namespace Erdos68Development

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-- All factorial denominators through 137 containing the prime 139. -/
lemma factors_139_through_137 :
    ∀ n ∈ Finset.range 136,
      (139 ∣ denom n ↔ n ∈ ({67, 120, 135} : Finset ℕ)) := by
  decide

lemma quotient_residues_139 :
    (denom 67 / 139) % 139 = 6 ∧
      (denom 120 / 139) % 139 = 49 ∧
      (denom 135 / 139) % 139 = 73 := by
  decide


private def qTerm (n : ℕ) : ℚ := 1 / ((n + 2).factorial - 1 : ℚ)

private lemma qTerm_den (n : ℕ) : (qTerm n).den = denom n := by
  have hf : 2 ≤ (n + 2).factorial := by exact_mod_cast factorial_ge_two n
  have hd : 0 < denom n := by unfold denom; omega
  have he : qTerm n = 1 / (denom n : ℚ) := by
    unfold qTerm denom
    rw [Nat.cast_sub (Nat.factorial_pos _), Nat.cast_one]
  rw [he, one_div, Rat.inv_natCast_den_of_pos hd]

private lemma coprime_den_add {p : ℕ} {x y : ℚ}
    (hx : p.Coprime x.den) (hy : p.Coprime y.den) :
    p.Coprime (x + y).den :=
  (hx.mul_right hy).of_dvd_right (Rat.add_den_dvd x y)

private lemma coprime_den_sum {p : ℕ} {s : Finset ℕ} {f : ℕ → ℚ}
    (h : ∀ n ∈ s, p.Coprime (f n).den) :
    p.Coprime (∑ n ∈ s, f n).den := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    apply coprime_den_add (h a (by simp))
    exact ih (fun n hn => h n (by simp [hn]))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private lemma coprime_den_bad_group :
    Nat.Coprime 139 (∑ n ∈ ({67, 120, 135} : Finset ℕ), qTerm n).den := by
  norm_num [qTerm, Nat.factorial]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private lemma coprime_den_other_terms :
    ∀ n ∈ Finset.range 136 \ ({67, 120, 135} : Finset ℕ),
      Nat.Coprime 139 (qTerm n).den := by
  simp only [qTerm_den]
  decide

lemma partial_sum_137_den_coprime_139 :
    Nat.Coprime 139
      (∑ n ∈ Finset.range 136, 1 / ((n + 2).factorial - 1 : ℚ)).den := by
  change Nat.Coprime 139 (∑ n ∈ Finset.range 136, qTerm n).den
  have hs : ({67, 120, 135} : Finset ℕ) ⊆ Finset.range 136 := by decide
  have hd : Disjoint (Finset.range 136 \ ({67, 120, 135} : Finset ℕ))
      ({67, 120, 135} : Finset ℕ) := by decide
  rw [← Finset.sdiff_union_of_subset hs, Finset.sum_union hd]
  exact coprime_den_add (coprime_den_sum coprime_den_other_terms) coprime_den_bad_group

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
lemma correctedApprox_134_den_coprime_139 :
    Nat.Coprime 139 (correctedApprox 134).den := by
  unfold correctedApprox
  apply coprime_den_add partial_sum_137_den_coprime_139
  norm_num [Nat.factorial]

set_option maxRecDepth 20000 in
lemma canceled_prime_in_correctedApprox :
    139 ∣ denom 135 ∧ ¬139 ∣ (correctedApprox 134).den := by
  constructor
  · decide
  · intro h
    exact Nat.not_coprime_of_dvd_of_dvd (by norm_num : 1 < 139)
      (dvd_refl 139) h correctedApprox_134_den_coprime_139

/-- The strict upper correction does not preserve every factor of the last
included denominator. This refutes only a proposed denominator lemma, not the
original irrationality conjecture. -/
theorem last_denominator_need_not_survive_correction :
    ¬denom 135 ∣ (correctedApprox 134).den := by
  intro h
  exact canceled_prime_in_correctedApprox.2 (canceled_prime_in_correctedApprox.1.trans h)

#print axioms last_denominator_need_not_survive_correction

end Erdos68Development
