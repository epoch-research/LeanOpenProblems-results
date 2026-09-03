import Submission.EntropyDecrement
import Submission.StationaryEntropyRecurrence

/-! A uniform finite entropy-decrement theorem for stationary labels and
permuted auxiliary variables. The horizon is chosen before the finite system. -/

namespace Erdos371.FiniteInformation
open EntropyScales EntropyDecrement
universe u v w

/-- Uniform finite entropy decrement. Each auxiliary space may be different,
and only the finitely many scales below the selected horizon are constrained.
This is suitable for residue variables on a sufficiently long cyclic sample. -/
theorem stationary_entropy_decrement {A : Type u} [Fintype A]
    (H₀ : ℕ) (hH₀ : 1 < H₀) (C ε : ℝ) (hC : 0 ≤ C) (hε : 0 < ε) :
    ∃ K > 0, ∀ (Ω : Type v) [Fintype Ω] (p : Law Ω)
      (S : Ω → Ω), mapLaw p S = p → ∀ (L : Ω → A)
      (B : ℕ → Type w) [∀ H, Fintype (B H)]
      (Y : ∀ H, Ω → B H) (R : ∀ H, Equiv.Perm (B H)),
      (∀ n < K, Function.Semiconj (Y (factorialScale H₀ n)) S (R (factorialScale H₀ n))) →
      (∀ n < K, Real.log (Fintype.card (B (factorialScale H₀ n))) ≤ C * factorialScale H₀ n) →
        ∃ n < K, mutualInformation
          (blockJointLaw p S L (Y (factorialScale H₀ n)) (factorialScale H₀ n)) <
            ε * factorialScale H₀ n / Real.log (factorialScale H₀ n : ℝ) := by
  obtain ⟨K,hK,hdec⟩ := exists_factorial_decrement_horizon H₀ hH₀
    (Real.log (Fintype.card A)) C ε hC hε
  refine ⟨K,hK,?_⟩
  intro Ω _ p S hS L B _ Y R hY hB
  let E : ℕ → ℝ := fun H => entropy (blockLaw p S L H)
  let I : ℕ → ℝ := fun H => mutualInformation (blockJointLaw p S L (Y H) H)
  apply hdec E I (fun H => entropy_nonneg _)
  · exact (entropy_blockLaw_le p S L H₀).trans_eq (mul_comm _ _)
  · intro n hn
    have hrec := stationary_block_entropy_recurrence p S hS L
      (Y (factorialScale H₀ n)) (R (factorialScale H₀ n)) (hY n hn)
      (factorialScale H₀ n) ((n+2)^2)
    rw [← factorialScale_succ] at hrec
    have hres : entropy (mapLaw p (Y (factorialScale H₀ n))) ≤ C * factorialScale H₀ n :=
      (entropy_le_log_card _).trans (hB n hn)
    simp only [Nat.cast_pow, Nat.cast_add, Nat.cast_ofNat] at hrec
    exact hrec.trans (add_le_add hres le_rfl)

#print axioms stationary_entropy_decrement
end Erdos371.FiniteInformation
