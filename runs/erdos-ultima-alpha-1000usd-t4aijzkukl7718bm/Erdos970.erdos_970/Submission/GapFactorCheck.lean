import FormalConjecturesUtil

/-!
A counterexample to an auxiliary claim about prime factors of unit gaps.
This is NOT a disproof of Erdős 970.
-/
namespace Erdos970.GapFactorCheck

def primes : Finset ℕ := {3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97}

def residues : ℕ → ℕ
  | 3 => 1
  | 5 => 3
  | 7 => 1
  | 11 => 10
  | 13 => 4
  | 17 => 9
  | 19 => 5
  | 23 => 20
  | 29 => 6
  | 31 => 28
  | 37 => 12
  | 41 => 14
  | 43 => 2
  | 47 => 27
  | 53 => 44
  | 59 => 39
  | 61 => 11
  | 67 => 13
  | 71 => 41
  | 73 => 2
  | 79 => 51
  | 83 => 1
  | 89 => 47
  | 97 => 42
  | _ => 0

/-- A prime gap of length `101`, formed using only primes less than `101`. -/
theorem prime_gap_counterexample :
    (∀ p ∈ primes, p.Prime ∧ p < 101) ∧
    (∀ p ∈ primes, ¬(0 : ℕ) ≡ residues p [MOD p]) ∧
    (∀ p ∈ primes, ¬(101 : ℕ) ≡ residues p [MOD p]) ∧
    (∀ i : Fin 101, 0 < i.val → ∃ p ∈ primes, i.val ≡ residues p [MOD p]) := by
  decide

/-- The tempting assertion that a gap's prime factors cannot exceed all the sieving primes. -/
def GapFactorsSmall : Prop :=
  ∀ (P : Finset ℕ) (r : ℕ → ℕ) (d : ℕ), (∀ p ∈ P, p.Prime) → 0 < d →
    (∀ p ∈ P, ¬(0 : ℕ) ≡ r p [MOD p]) →
    (∀ p ∈ P, ¬d ≡ r p [MOD p]) →
    (∀ i : ℕ, 0 < i → i < d → ∃ p ∈ P, i ≡ r p [MOD p]) →
    ∀ q : ℕ, q.Prime → q ∣ d → ∃ p ∈ P, q ≤ p

theorem not_gapFactorsSmall : ¬GapFactorsSmall := by
  intro h
  obtain ⟨hp, h0, h101, hcover⟩ := prime_gap_counterexample
  obtain ⟨p, hpP, hple⟩ := h primes residues 101 (fun p hpP => (hp p hpP).1)
    (by decide) h0 h101 (fun i hi hid => hcover ⟨i, hid⟩ hi)
    101 (by decide) (dvd_refl _)
  exact (not_le_of_gt (hp p hpP).2) hple

#print axioms prime_gap_counterexample
#print axioms not_gapFactorsSmall
end Erdos970.GapFactorCheck
