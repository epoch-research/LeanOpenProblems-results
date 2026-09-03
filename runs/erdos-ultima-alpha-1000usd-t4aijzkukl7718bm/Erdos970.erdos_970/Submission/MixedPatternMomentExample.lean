import Submission.MixedPatternRescaling

/-! Integer rounded intersection moments alone miss an exact conditional
progression constraint. The synthetic population here is NOT a residue cover. -/
namespace Erdos970.MixedPattern.MomentExample
open OptimalCoverCore BlockSieve.SievePolynomial

def primes : Finset ℕ := {2, 3, 5}

def pattern : Fin 6 → Finset ℕ := ![{2}, {2}, {3}, {2, 3}, {5}, {5}]

def moment (A : Finset ℕ) : ℕ :=
  (Finset.univ.filter (fun j : Fin 6 => A ⊆ pattern j)).card

def syntheticMixed (A B : Finset ℕ) : ℕ :=
  (Finset.univ.filter (fun j : Fin 6 => A ⊆ pattern j ∧ Disjoint B (pattern j))).card

/-- Every rounded CRT intersection bound, including the total mass, holds. -/
theorem synthetic_moments :
    (∀ A ∈ primes.powerset,
      6 / (∏ p ∈ A, p) ≤ moment A ∧ moment A ≤ ceilQuotient 6 (∏ p ∈ A, p)) ∧
    (∀ j : Fin 6, (pattern j).Nonempty ∧ pattern j ⊆ primes) ∧
    syntheticMixed {5} {2} = 2 := by
  decide +kernel

lemma singleton_survivors_upper (n p : ℕ) (hp : 0 < p) (s : ℕ → ℕ) :
    (survivors n {p} s).card ≤ n - n / p := by
  classical
  have hpart := Finset.card_filter_add_card_filter_not (s := Finset.range n)
    (fun x => x ≡ s p [MOD p])
  have hlo := (residue_count_bounds n p (s p) hp).1
  simp only [Finset.card_range] at hpart
  have he : survivors n {p} s = (Finset.range n).filter (fun x => ¬x ≡ s p [MOD p]) := by
    ext x
    simp [survivors]
  rw [he]
  omega

/-- In an actual interval of length six, at most one point can hit the class
modulo five while avoiding the class modulo two. -/
theorem actual_mixed_le_one (r : ℕ → ℕ) : mixedCount 6 {5} {2} r ≤ 1 := by
  have hA : ∀ p ∈ ({5} : Finset ℕ), p.Prime := by
    intro p hp
    simpa only [Finset.mem_singleton.mp hp] using (show Nat.Prime 5 by decide)
  have hB : ∀ p ∈ ({2} : Finset ℕ), p.Prime := by
    intro p hp
    simpa only [Finset.mem_singleton.mp hp] using Nat.prime_two
  have hh := (mixedCount_bounds 6 {5} {2} r hA hB (by decide)
    (fun _ => 0) (fun n => n - n / 2) (fun _ _ => Nat.zero_le _)
    (fun n s => singleton_survivors_upper n 2 (by decide) s)).2
  norm_num [ceilQuotient] at hh
  exact hh

/-- The synthetic population satisfies all rounded moments and has no empty
pattern, but cannot reproduce the mixed counts of any residue configuration. -/
theorem synthetic_not_realizable :
    ¬∃ r : ℕ → ℕ, ∀ A B : Finset ℕ,
      A ⊆ primes → B ⊆ primes → Disjoint A B →
      mixedCount 6 A B r = syntheticMixed A B := by
  rintro ⟨r, hr⟩
  have hh := actual_mixed_le_one r
  rw [hr {5} {2} (by decide) (by decide) (by decide), synthetic_moments.2.2] at hh
  omega

#print axioms synthetic_moments
#print axioms actual_mixed_le_one
#print axioms synthetic_not_realizable
end Erdos970.MixedPattern.MomentExample
