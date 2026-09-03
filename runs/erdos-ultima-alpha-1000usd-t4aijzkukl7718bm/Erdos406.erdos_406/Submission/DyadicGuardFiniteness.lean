import Submission.Work

/-! A guarded invariant criterion for Erdős 406. No invariant witness is
provided; all of the required hypotheses remain explicit. -/
namespace Erdos406DyadicGuard

/-- The eventual residue class of the powers of four, modulo `3 * 4^k`. -/
def Guard (k n : ℕ) : Prop := n % (3 * 4 ^ k) = 4 ^ k

lemma guard_four_pow (k j : ℕ) : Guard k (4 ^ (k + j)) := by
  unfold Guard
  rw [pow_add, Nat.mul_comm 3 (4 ^ k), Nat.mul_mod_mul_left]
  simp [Nat.pow_mod]

lemma guard_mul_four (k n : ℕ) (h : Guard k n) : Guard k (4 * n) := by
  unfold Guard at *
  have hpos : 0 < 4 ^ k := by positivity
  have hlt : 4 ^ k < 3 * 4 ^ k := by omega
  have hc : Nat.ModEq (3 * 4 ^ k) n (4 ^ k) := by
    change n % (3 * 4 ^ k) = (4 ^ k) % (3 * 4 ^ k)
    rw [h, Nat.mod_eq_of_lt hlt]
  have hh := hc.mul_left 4
  change (4 * n) % (3 * 4 ^ k) = (4 * 4 ^ k) % (3 * 4 ^ k) at hh
  simpa only [Nat.mul_mod_mul_right, Nat.reduceMod, Nat.one_mul] using hh

/-- Closure is needed only in the eventual dyadic residue class, rather than
on every integer. The seed is the first power lying in this class. -/
lemma orbit_in_invariant (k : ℕ) (P : ℕ → Prop)
    (hseed : P (4 ^ k))
    (hstep : ∀ n, Guard k n → P n → P (4 * n)) :
    ∀ j : ℕ, P (4 ^ (k + j)) := by
  intro j
  induction j with
  | zero => simpa using hseed
  | succ j ih =>
    have hh := hstep (4 ^ (k + j)) (guard_four_pow k j) ih
    simpa only [Nat.add_succ, pow_succ, Nat.mul_comm] using hh

/-- Sufficient finiteness criterion used by the guarded-language search.
This is conditional, not a proof of Erdős 406. -/
theorem finite_of_guarded_invariant (k : ℕ) (P : ℕ → Prop)
    (hseed : P (4 ^ k))
    (hstep : ∀ n, Guard k n → P n → P (4 * n))
    (hgood : {n : ℕ | P n ∧ Nat.digits 3 n ⊆ [0, 1]}.Finite) :
    {n : ℕ | n.isPowerOfTwo ∧ Nat.digits 3 n ⊆ [0, 1]}.Finite := by
  obtain ⟨B, hB⟩ := hgood.bddAbove
  apply Set.finite_iff_bddAbove.mpr
  refine ⟨max B (4 ^ k), ?_⟩
  rintro n ⟨⟨e, rfl⟩, hg⟩
  obtain ⟨m, hm⟩ := Erdos406Work.even_exponent hg
  have he : 2 ^ e = 4 ^ m := by
    rw [hm, ← two_mul, pow_mul]
    rfl
  rw [he] at hg ⊢
  by_cases hmk : k ≤ m
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hmk
    exact (hB ⟨orbit_in_invariant k P hseed hstep j, hg⟩).trans (le_max_left _ _)
  · exact (Nat.pow_le_pow_right (by decide : 1 ≤ 4) (by omega : m ≤ k)).trans
      (le_max_right _ _)

#print axioms guard_four_pow
#print axioms guard_mul_four
#print axioms orbit_in_invariant
#print axioms finite_of_guarded_invariant
end Erdos406DyadicGuard
