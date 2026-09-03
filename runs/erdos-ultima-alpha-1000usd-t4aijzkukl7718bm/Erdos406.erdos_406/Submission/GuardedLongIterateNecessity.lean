import Submission.DyadicGuardFiniteness

/-! Necessary rejection constraints for the guarded finite-language search.
No invariant satisfying the hypotheses is supplied. This is not a settlement
of Erdős 406. -/
namespace Erdos406GuardedLongIterate
open Erdos406DyadicGuard

/-- The eventual residue class together with the omitted small seeds. -/
def FullGuard (k n : ℕ) : Prop := Guard k n ∨ ∃ i < k, n = 4^i

lemma four_pow_full_guard (k i : ℕ) : FullGuard k (4^i) := by
  by_cases h : k ≤ i
  · obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le h
    exact Or.inl (guard_four_pow k j)
  · exact Or.inr ⟨i,by omega,rfl⟩

lemma full_guard_mul (k n : ℕ) (h : FullGuard k n) : FullGuard k (4*n) := by
  rcases h with h | ⟨i,hi,rfl⟩
  · exact Or.inl (guard_mul_four k n h)
  · simpa only [pow_succ, Nat.mul_comm] using four_pow_full_guard k (i+1)

lemma closure_on_full_guard (k : ℕ) (P : ℕ → Prop)
    (hseed : ∀ i ≤ k, P (4^i))
    (hstep : ∀ n, Guard k n → P n → P (4*n)) :
    ∀ n, FullGuard k n → P n → P (4*n) := by
  intro n hn hp
  rcases hn with hn | ⟨i,hi,rfl⟩
  · exact hstep n hn hp
  · simpa only [pow_succ, Nat.mul_comm] using hseed (i+1) (by omega)

lemma accepted_iterates (k : ℕ) (P : ℕ → Prop)
    (hstep : ∀ n, FullGuard k n → P n → P (4*n))
    (n : ℕ) (hn : FullGuard k n) (hp : P n) :
    ∀ j : ℕ, FullGuard k (4^j*n) ∧ P (4^j*n) := by
  intro j
  induction j with
  | zero => simpa using And.intro hn hp
  | succ j ih =>
    have hg := full_guard_mul k (4^j*n) ih.1
    have ha := hstep (4^j*n) ih.1 ih.2
    simpa only [pow_succ', Nat.mul_assoc] using And.intro hg ha

/-- A concrete long good iterate forces rejection of its guarded predecessor.
The zero-iterate case needs no guard at all. -/
theorem long_good_iterate_rejected (k N : ℕ) (P : ℕ → Prop)
    (hseed : ∀ i ≤ k, P (4^i))
    (hstep : ∀ n, Guard k n → P n → P (4*n))
    (hbound : ∀ n, P n → Nat.digits 3 n ⊆ [0,1] → (Nat.digits 3 n).length < N)
    (n j : ℕ) (hguard : j = 0 ∨ FullGuard k n)
    (hgood : Nat.digits 3 (4^j*n) ⊆ [0,1])
    (hlength : N ≤ (Nat.digits 3 (4^j*n)).length) : ¬ P n := by
  intro hp
  have hout : P (4^j*n) := by
    rcases hguard with rfl | hg
    · simpa using hp
    · exact (accepted_iterates k P (closure_on_full_guard k P hseed hstep) n hg hp j).2
  have hh := hbound (4^j*n) hout hgood
  omega

/-- The exact arithmetic witnesses obtained from the old failed NFA model.
They are not powers-of-two counterexamples; they are necessary negatives
for the stated finite-language template. -/
lemma concrete_long_iterates :
    ∀ p ∈ ([(3736672,1),(897232,2),(897376,2),(224320,3),(227008,3)] : List (ℕ×ℕ)),
      Guard 2 p.1 ∧ Nat.digits 3 (4^p.2*p.1) ⊆ [0,1] ∧
        16 ≤ (Nat.digits 3 (4^p.2*p.1)).length := by
  unfold Guard
  decide +kernel

#print axioms four_pow_full_guard
#print axioms closure_on_full_guard
#print axioms long_good_iterate_rejected
#print axioms concrete_long_iterates
end Erdos406GuardedLongIterate
