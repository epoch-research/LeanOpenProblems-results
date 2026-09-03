import Submission.RoundedSieve

/-!
A finite obstruction to completeness of residue-independent rounded sieve certificates.
This is a diagnostic theorem, not a disproof of the quadratic Jacobsthal conjecture.
-/
namespace Erdos970.BlockSieve.SievePolynomial

/-- Evaluate a sieve polynomial on a prescribed set of hit primes. -/
noncomputable def patternValue (S : SievePolynomial) (B : Finset ℕ) : ℝ :=
  ∑ a : S.Term, S.coefficient a * if S.primes a ⊆ B then 1 else 0

/-- Any hit pattern is realized at zero by choosing zero or one as forbidden residue. -/
theorem patternValue_eq_value_zero (S : SievePolynomial)
    (hS : ∀ a, ∀ p ∈ S.primes a, p.Prime) (B : Finset ℕ) :
    S.patternValue B = S.value (fun p => if p ∈ B then 0 else 1) 0 := by
  classical
  unfold patternValue value
  apply Finset.sum_congr rfl
  intro a ha
  have heq : (∀ p ∈ S.primes a, (0 : ℕ) ≡ (if p ∈ B then 0 else 1) [MOD p]) ↔
      S.primes a ⊆ B := by
    constructor
    · intro h p hp
      by_contra hpB
      have hh := h p hp
      have hp1 := (hS a p hp).one_lt
      simp [hpB, Nat.ModEq, Nat.mod_eq_of_lt hp1] at hh
    · intro h p hp
      simp [h hp, Nat.ModEq]
  simp only [heq]

/-- A synthetic population has two points hitting only 2 and two hitting only 3. -/
def syntheticCount (Q : Finset ℕ) : ℕ :=
  (if Q ⊆ {2} then 2 else 0) + (if Q ⊆ {3} then 2 else 0)

/-- This synthetic population obeys every separate CRT floor/ceiling count bound at length four. -/
theorem syntheticCount_bounds (Q : Finset ℕ) (hQ : Q ⊆ {2, 3}) :
    4 / (∏ p ∈ Q, p) ≤ syntheticCount Q ∧
    syntheticCount Q ≤ ceilQuotient 4 (∏ p ∈ Q, p) := by
  have hh : ∀ A ∈ ({2, 3} : Finset ℕ).powerset,
      4 / (∏ p ∈ A, p) ≤ syntheticCount A ∧
      syntheticCount A ≤ ceilQuotient 4 (∏ p ∈ A, p) := by decide
  exact hh Q (Finset.mem_powerset.mpr hQ)

/-- Consequently, no universally valid lower polynomial can have positive rounded main term. -/
theorem roundedMain_nonpos_two_three (S : SievePolynomial)
    (hS : S.SupportedOn {2, 3})
    (hpoint : ∀ B : Finset ℕ, B ⊆ {2, 3} → B.Nonempty → S.patternValue B ≤ 0) :
    S.roundedMain 4 ≤ 0 := by
  classical
  have hle : S.roundedMain 4 ≤
      ∑ a : S.Term, S.coefficient a * syntheticCount (S.primes a) := by
    apply Finset.sum_le_sum
    intro a ha
    obtain ⟨hlo, hhi⟩ := syntheticCount_bounds (S.primes a) (hS a)
    by_cases hc : 0 ≤ S.coefficient a
    · rw [if_pos hc]
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast hlo) hc
    · rw [if_neg hc]
      exact mul_le_mul_of_nonpos_left (by exact_mod_cast hhi) (le_of_not_ge hc)
  have heq : (∑ a : S.Term, S.coefficient a * syntheticCount (S.primes a)) =
      2 * S.patternValue {2} + 2 * S.patternValue {3} := by
    rw [patternValue, patternValue, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a ha
    dsimp only [syntheticCount]
    split_ifs <;> push_cast <;> ring
  have htwo := hpoint {2} (by decide) (by decide)
  have hthree := hpoint {3} (by decide) (by decide)
  rw [heq] at hle
  linarith

/-- The universal pointwise condition used in a residue-independent certificate suffices. -/
theorem no_uniform_rounded_certificate_two_three :
    ¬∃ S : SievePolynomial, S.SupportedOn {2, 3} ∧
      (∀ r : ℕ → ℕ, ∀ i < 4, (∃ p ∈ ({2, 3} : Finset ℕ), i ≡ r p [MOD p]) →
        S.value r i ≤ 0) ∧ 0 < S.roundedMain 4 := by
  classical
  rintro ⟨S, hS, hpoint, hpos⟩
  apply hpos.not_ge
  apply roundedMain_nonpos_two_three S hS
  intro B hB hne
  have hSp : ∀ a, ∀ p ∈ S.primes a, p.Prime := by
    intro a p hp
    have hh := hS a hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hh
    rcases hh with rfl | rfl <;> norm_num
  rw [patternValue_eq_value_zero S hSp B]
  apply hpoint _ 0 (by decide)
  obtain ⟨p, hp⟩ := hne
  exact ⟨p, hB hp, by simp [hp, Nat.ModEq]⟩

/-- Nevertheless, every actual choice of the two residue classes leaves a survivor. -/
theorem actual_survivor_two_three (r : ℕ → ℕ) :
    ∃ i < 4, ∀ p ∈ ({2, 3} : Finset ℕ), ¬i ≡ r p [MOD p] := by
  have hfinite : ∀ a : Fin 2, ∀ b : Fin 3, ∃ i : Fin 4,
      i.val % 2 ≠ a.val ∧ i.val % 3 ≠ b.val := by decide
  obtain ⟨i, hi2, hi3⟩ := hfinite ⟨r 2 % 2, Nat.mod_lt _ (by decide)⟩
    ⟨r 3 % 3, Nat.mod_lt _ (by decide)⟩
  refine ⟨i.val, i.isLt, ?_⟩
  intro p hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl
  · exact hi2
  · exact hi3

/-- A proven interval bound need not admit a positive universal rounded certificate. -/
theorem rounded_certificate_not_complete :
    (∀ r : ℕ → ℕ, ∃ i < 4, ∀ p ∈ ({2, 3} : Finset ℕ), ¬i ≡ r p [MOD p]) ∧
    ¬∃ S : SievePolynomial, S.SupportedOn {2, 3} ∧
      (∀ r : ℕ → ℕ, ∀ i < 4, (∃ p ∈ ({2, 3} : Finset ℕ), i ≡ r p [MOD p]) →
        S.value r i ≤ 0) ∧ 0 < S.roundedMain 4 :=
  ⟨actual_survivor_two_three, no_uniform_rounded_certificate_two_three⟩

/-- Evaluation only depends on the hit pattern on the supporting primes. -/
theorem patternValue_eq_given_hits (S : SievePolynomial) (P B : Finset ℕ)
    (hS : S.SupportedOn P) (r : ℕ → ℕ) (i : ℕ)
    (hmatch : ∀ p ∈ P, p ∈ B ↔ i ≡ r p [MOD p]) :
    S.patternValue B = S.value r i := by
  classical
  unfold patternValue value
  apply Finset.sum_congr rfl
  intro a ha
  have heq : (∀ p ∈ S.primes a, i ≡ r p [MOD p]) ↔ S.primes a ⊆ B := by
    constructor
    · intro h p hp
      exact (hmatch p (hS a hp)).mpr (h p hp)
    · intro h p hp
      exact (hmatch p (hS a hp)).mp (h hp)
  simp only [heq]

/-- Even for the single fixed choice of zero residues, the rounded certificate can fail. -/
theorem no_rounded_certificate_fixed_zero :
    ¬∃ S : SievePolynomial, S.SupportedOn {2, 3} ∧
      (∀ i < 4, (∃ p ∈ ({2, 3} : Finset ℕ), i ≡ 0 [MOD p]) →
        S.value (fun _ => 0) i ≤ 0) ∧ 0 < S.roundedMain 4 := by
  rintro ⟨S, hS, hpoint, hpos⟩
  apply hpos.not_ge
  apply roundedMain_nonpos_two_three S hS
  intro B hB hne
  have hpatterns : ∀ A ∈ ({2, 3} : Finset ℕ).powerset, A.Nonempty →
      ∃ i : Fin 4, ∀ p ∈ ({2, 3} : Finset ℕ), p ∈ A ↔ i.val ≡ 0 [MOD p] := by decide
  obtain ⟨i, hi⟩ := hpatterns B (Finset.mem_powerset.mpr hB) hne
  rw [patternValue_eq_given_hits S {2, 3} B hS (fun _ => 0) i.val hi]
  apply hpoint i.val i.isLt
  obtain ⟨p, hp⟩ := hne
  exact ⟨p, hB hp, (hi p (hB hp)).mp hp⟩

#print axioms no_rounded_certificate_fixed_zero

#print axioms rounded_certificate_not_complete
end Erdos970.BlockSieve.SievePolynomial
