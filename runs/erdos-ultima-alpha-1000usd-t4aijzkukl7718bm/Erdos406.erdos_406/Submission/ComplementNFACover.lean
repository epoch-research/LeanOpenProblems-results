import Submission.BackwardComplementFiniteness
import Submission.MSDCertificates

/-! A reserved accepting state with two self-loops covers every positive good
integer. The backward-closure and rejected-seed hypotheses remain unproved. -/
namespace Erdos406ComplementNFA
open Erdos406MSDCertificate

def acceptsNat {σ : Type*} (M : NFA ℕ σ) (n : ℕ) : Prop :=
  ∃ q ∈ evalNat M.toDFA n, q ∈ M.accept

lemma good_state_reachable {σ : Type*} (M : NFA ℕ σ) (g : σ)
    (hfirst : g ∈ M.stepSet M.start 1)
    (hloop : ∀ d, d < 2 → g ∈ M.step g d)
    (n : ℕ) (hn : 0 < n) (hgood : Nat.digits 3 n ⊆ [0, 1]) :
    g ∈ evalNat M.toDFA n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hd : n % 3 ≤ 1 := by
      simpa using Erdos406Work.ternary_digit_bound hgood 0
    by_cases hsmall : n < 3
    · rw [Nat.mod_eq_of_lt hsmall] at hd
      have he : n = 1 := by omega
      subst n
      rw [evalNat_pos M.toDFA (by decide : 0 < (1 : ℕ))]
      change g ∈ M.stepSet (evalNat M.toDFA 0) 1
      rw [evalNat_zero]
      exact hfirst
    · have hnq : 0 < n / 3 := by omega
      have hlt : n / 3 < n := Nat.div_lt_self hn (by decide)
      have hgq : Nat.digits 3 (n / 3) ⊆ [0, 1] := by
        intro d hmem
        apply hgood
        rw [Nat.digits_of_two_le_of_pos (by decide : 2 ≤ 3) hn]
        exact List.mem_cons_of_mem _ hmem
      rw [evalNat_pos M.toDFA hn]
      exact NFA.mem_stepSet.mpr ⟨g, ih (n / 3) hlt hnq hgq, hloop _ (by omega)⟩

lemma covers_positive_good {σ : Type*} (M : NFA ℕ σ) (g : σ)
    (hfirst : g ∈ M.stepSet M.start 1)
    (hloop : ∀ d, d < 2 → g ∈ M.step g d)
    (haccept : g ∈ M.accept) (n : ℕ) (hn : 0 < n)
    (hgood : Nat.digits 3 n ⊆ [0, 1]) : acceptsNat M n :=
  ⟨g, good_state_reachable M g hfirst hloop n hn hgood, haccept⟩

/-- This supplies the cover premise for the backward criterion, but not its
closure or seed premises. It is not a certificate for the conjecture. -/
theorem finite_of_complement_nfa {σ : Type*} (M : NFA ℕ σ) (g : σ)
    (hfirst : g ∈ M.stepSet M.start 1)
    (hloop : ∀ d, d < 2 → g ∈ M.step g d)
    (haccept : g ∈ M.accept) (E : ℕ) (G : ℕ → Prop)
    (hGseed : G (4 ^ E)) (hGstep : ∀ n, G n → G (4 * n))
    (hseed : ¬ acceptsNat M (4 ^ E))
    (hback : ∀ n, 4 ^ E ≤ n → G n → acceptsNat M (4 * n) → acceptsNat M n) :
    {n : ℕ | n.isPowerOfTwo ∧ Nat.digits 3 n ⊆ [0, 1]}.Finite := by
  exact Erdos406BackwardComplement.finite_of_backward_cover E (acceptsNat M) G
    hGseed hGstep hseed hback (covers_positive_good M g hfirst hloop haccept)

#print axioms good_state_reachable
#print axioms covers_positive_good
#print axioms finite_of_complement_nfa
end Erdos406ComplementNFA
