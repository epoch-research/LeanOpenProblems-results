import Submission.BackwardNFAStrided

/-! Guarded, threshold-only backward covers. These criteria are conditional;
no covering automata for the missing exponent classes are supplied. -/
namespace Erdos406BackwardGuardedStrided
open Erdos406BackwardStrided

def enlarge (B : ℕ) (G Q : ℕ → Prop) (n : ℕ) : Prop :=
  Q n ∨ (0 < n ∧ (n < B ∨ ¬ G n))

theorem enlarge_backward (K B : ℕ) (hK : 0 < K) (G Q : ℕ → Prop)
    (hG : ∀ n, G n → G (K * n))
    (hback : ∀ n, B ≤ n → G n → Q (K * n) → Q n) :
    ∀ n, enlarge B G Q (K * n) → enlarge B G Q n := by
  intro n hn
  by_cases hz : n = 0
  · subst n
    simpa only [mul_zero] using hn
  have hnpos : 0 < n := Nat.pos_of_ne_zero hz
  by_cases hsmall : n < B
  · exact Or.inr ⟨hnpos, Or.inl hsmall⟩
  by_cases hg : G n
  · apply Or.inl
    rcases hn with hn | ⟨_, hbad⟩
    · exact hback n (by omega) hg hn
    · rcases hbad with hbad | hbad
      · have hmul : n ≤ K * n := by nlinarith
        omega
      · exact False.elim (hbad (hG n hg))
  · exact Or.inr ⟨hnpos, Or.inr hg⟩

theorem enlarge_seed (B : ℕ) (G Q : ℕ → Prop) (hg : G B) (hq : ¬ Q B) :
    ¬ enlarge B G Q B := by
  rintro (h | ⟨_, h | h⟩)
  · exact hq h
  · omega
  · exact h hg

theorem finite_of_guarded_family (s E : ℕ) (hs : 0 < s)
    (G Q : ℕ → ℕ → Prop)
    (hGseed : ∀ r, r < s → G r (4 ^ (E + r)))
    (hGstep : ∀ r, r < s → ∀ n, G r n → G r (4 ^ s * n))
    (hseed : ∀ r, r < s → ¬ Q r (4 ^ (E + r)))
    (hback : ∀ r, r < s → ∀ n, 4 ^ (E + r) ≤ n → G r n →
      Q r (4 ^ s * n) → Q r n)
    (hcover : ∀ r, r < s → ∀ n, 0 < n → Nat.digits 3 n ⊆ [0, 1] → Q r n) :
    {n : ℕ | n.isPowerOfTwo ∧ Nat.digits 3 n ⊆ [0, 1]}.Finite := by
  apply finite_of_backward_family s E hs (fun r => enlarge (4 ^ (E + r)) (G r) (Q r))
  · intro r hr
    exact enlarge_seed _ _ _ (hGseed r hr) (hseed r hr)
  · intro r hr
    exact enlarge_backward _ _ (by positivity) _ _ (hGstep r hr) (hback r hr)
  · intro r hr n hn hg
    exact Or.inl (hcover r hr n hn hg)

#print axioms enlarge_backward
#print axioms finite_of_guarded_family
end Erdos406BackwardGuardedStrided
