import Submission.Certificates

/-! Conditional finite-state criterion for Boolean-register searches.
No register automaton satisfying these hypotheses is asserted to exist. -/
namespace Erdos406BooleanRegister

structure Data (σ : Type*) where
  step : σ → ℕ → σ
  start : σ
  test : σ → Bool

def Data.dfa {σ : Type*} (D : Data σ) : DFA ℕ σ where
  step := D.step
  start := D.start
  accept := {s | D.test s = false}

/-- A concrete register table with these checked conditions would settle the
conjecture. The table, seed, and all closure hypotheses remain explicit. -/
theorem finite_of_checks {σ : Type*} (D : Data σ) (E : ℕ)
    (R : σ → σ → ℕ → Prop)
    (hstart : R D.start D.start 0)
    (hstep : ∀ s t c d, c < 4 → d < 3 → R s t c →
      R (D.step s d) (D.step t ((4 * d + c) % 3)) ((4 * d + c) / 3))
    (hend : ∀ s t c d, c < 4 → 0 < d → d < 3 → R s t c →
      D.test (D.dfa.evalFrom (D.step t ((4 * d + c) % 3))
        (Nat.digits 3 ((4 * d + c) / 3))) = true → D.test (D.step s d) = true)
    (hseed : D.test (D.dfa.eval (Nat.digits 3 (4 ^ E))) = false)
    (G : σ → Prop) (hgoodStart : G D.start)
    (hgoodStep : ∀ s d, d < 2 → G s → G (D.step s d))
    (hgoodEnd : ∀ s, G s → D.test (D.step s 1) = true) :
    {n : ℕ | n.isPowerOfTwo ∧ Nat.digits 3 n ⊆ [0, 1]}.Finite := by
  refine Erdos406Certificate.dfa_eventual_certificate_finiteness
    D.dfa R hstart hstep ?_ E hseed G hgoodStart hgoodStep ?_
  · intro s t c d hc hd hd3 hr hs
    change D.test (D.dfa.evalFrom (D.step t ((4 * d + c) % 3))
      (Nat.digits 3 ((4 * d + c) / 3))) = false
    cases he : D.test (D.dfa.evalFrom (D.step t ((4 * d + c) % 3))
      (Nat.digits 3 ((4 * d + c) / 3))) with
    | false => rfl
    | true =>
      have hh := hend s t c d hc hd hd3 hr he
      change D.test (D.step s d) = false at hs
      simp [hs] at hh
  · intro s hs hbad
    have hh := hgoodEnd s hs
    change D.test (D.step s 1) = false at hbad
    simp [hbad] at hh

#print axioms finite_of_checks
end Erdos406BooleanRegister
