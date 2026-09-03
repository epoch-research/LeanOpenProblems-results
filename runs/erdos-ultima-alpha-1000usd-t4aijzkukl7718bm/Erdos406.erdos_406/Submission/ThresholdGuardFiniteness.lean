import Submission.DyadicGuardFiniteness

/-! Finiteness criteria with multiplication closure required only above an
explicit numerical threshold. No witness for the criteria is supplied. -/
namespace Erdos406ThresholdGuard
open Erdos406DyadicGuard

lemma guard_of_large_exponent (k e : ℕ) (hke : k ≤ e) : Guard k (4 ^ e) := by
  have hh := guard_four_pow k (e - k)
  simpa only [Nat.add_sub_of_le hke] using hh

lemma orbit_in_threshold_invariant (k E : ℕ) (hkE : k ≤ E) (P : ℕ → Prop)
    (hseed : P (4 ^ E))
    (hstep : ∀ n, 4 ^ E ≤ n → Guard k n → P n → P (4 * n)) :
    ∀ j : ℕ, P (4 ^ (E + j)) := by
  intro j
  induction j with
  | zero => simpa using hseed
  | succ j ih =>
    have hlarge : 4 ^ E ≤ 4 ^ (E + j) := Nat.pow_le_pow_right (by decide) (by omega)
    have hg := guard_of_large_exponent k (E + j) (by omega)
    have hh := hstep _ hlarge hg ih
    simpa only [Nat.add_succ, pow_succ'] using hh

/-- An accepted seed at the threshold, closure above it, and a finite
accepted-good intersection suffice. Closure below the threshold is irrelevant. -/
theorem finite_of_threshold_guard (k E : ℕ) (hkE : k ≤ E) (P : ℕ → Prop)
    (hseed : P (4 ^ E))
    (hstep : ∀ n, 4 ^ E ≤ n → Guard k n → P n → P (4 * n))
    (hgood : {n : ℕ | P n ∧ Nat.digits 3 n ⊆ [0, 1]}.Finite) :
    {n : ℕ | n.isPowerOfTwo ∧ Nat.digits 3 n ⊆ [0, 1]}.Finite := by
  obtain ⟨B, hB⟩ := hgood.bddAbove
  apply Set.finite_iff_bddAbove.mpr
  refine ⟨max B (4 ^ E), ?_⟩
  rintro n ⟨⟨e, rfl⟩, hg⟩
  obtain ⟨m, hm⟩ := Erdos406Work.even_exponent hg
  have he : 2 ^ e = 4 ^ m := by
    rw [hm, ← two_mul, pow_mul]
    rfl
  rw [he] at hg ⊢
  by_cases hEm : E ≤ m
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hEm
    exact (hB ⟨orbit_in_threshold_invariant k E hkE P hseed hstep j, hg⟩).trans
      (le_max_left _ _)
  · exact (Nat.pow_le_pow_right (by decide : 1 ≤ 4) (by omega : m ≤ E)).trans
      (le_max_right _ _)

/-- The bound on failure inputs must lie strictly below an actual accepted
seed. Merely having finitely many closure failures does not supply that seed. -/
theorem finite_of_bounded_failures (k E : ℕ) (hkE : k ≤ E) (P : ℕ → Prop)
    (hseed : P (4 ^ E))
    (hfail : ∀ n, Guard k n → P n → ¬ P (4 * n) → n < 4 ^ E)
    (hgood : {n : ℕ | P n ∧ Nat.digits 3 n ⊆ [0, 1]}.Finite) :
    {n : ℕ | n.isPowerOfTwo ∧ Nat.digits 3 n ⊆ [0, 1]}.Finite := by
  apply finite_of_threshold_guard k E hkE P hseed ?_ hgood
  intro n hn hg hp
  by_contra hh
  have hl := hfail n hg hp hh
  omega

/-- Intersecting with the threshold and the guard converts eventual closure
into ordinary all-input closure, as needed by the finite automaton exporter. -/
lemma truncated_closed (B : ℕ) (P G : ℕ → Prop)
    (hG : ∀ n, G n → G (4 * n))
    (hstep : ∀ n, B ≤ n → G n → P n → P (4 * n)) :
    ∀ n, (B ≤ n ∧ G n ∧ P n) → (B ≤ 4 * n ∧ G (4 * n) ∧ P (4 * n)) := by
  rintro n ⟨hn, hg, hp⟩
  exact ⟨by omega, hG n hg, hstep n hn hg hp⟩

#print axioms finite_of_threshold_guard
#print axioms finite_of_bounded_failures
#print axioms truncated_closed
end Erdos406ThresholdGuard
