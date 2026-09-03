import Submission.ParameterPeakTransfer

/-! A sufficient variable-arity amplification criterion. No representation
formula satisfying its hypotheses is asserted here. -/

noncomputable section
namespace Erdos322Research.VariableArityPeakTransfer
open Finset

/-- Exponential output counts with height exponential in arity give fixed
power peaks. A fixed additive height overhead does not affect the exponent. -/
theorem peaks_of_exponential_witnesses (r : ℕ → ℕ) (A C D : ℕ) (hA : 0 < A)
    (h : ∀ M : ℕ, ∃ s n : ℕ, M ≤ s ∧ n ≤ A^(C*s+D) ∧ 2^s ≤ r n) :
    {n : ℕ | (n : ℝ)^((1 : ℝ)/(2*(A*(C+1)))) < (r n : ℝ)}.Infinite := by
  convert ParameterPeakTransfer.peaks_of_height_witnesses r (A*(C+1)) 1
    (by positivity) (by decide) ?_ using 1 <;>
    try { simp only [Nat.cast_one, Nat.cast_mul, Nat.cast_add] }
  intro M
  obtain ⟨s,n,hs,hn,hr⟩ := h (M+D+1)
  have hspos : 0 < s := by omega
  have hds : D ≤ s := by omega
  have hA2 : A ≤ 2^A := (Nat.lt_two_pow_self (n := A)).le
  have hn' : n ≤ (2^s)^(A*(C+1)) := by
    calc
      n ≤ A^(C*s+D) := hn
      _ ≤ (2^A)^(C*s+D) := Nat.pow_le_pow_left hA2 _
      _ = 2^(A*(C*s+D)) := (pow_mul _ _ _).symm
      _ ≤ 2^(s*(A*(C+1))) := by
        apply Nat.pow_le_pow_right (by decide : 0 < 2)
        calc
          A*(C*s+D) ≤ A*(C*s+s) := Nat.mul_le_mul_left A (by omega)
          _ = s*(A*(C+1)) := by ring
      _ = (2^s)^(A*(C+1)) := pow_mul _ _ _
  refine ⟨2^s,n,?_,hn',?_⟩
  · have he := Nat.lt_two_pow_self (n := s)
    omega
  · simpa only [pow_one] using hr

/-- A seed set larger than twice the per-input multiplicity budget produces
at least `2^s` distinct outputs from `s` inputs. -/
theorem many_input_card_lower {α β : Type*} [Fintype α] [DecidableEq β]
    (s L : ℕ) (hL : 0 < L) (hseed : 2*L ≤ Fintype.card α)
    (T : Finset β) (F : (Fin s → α) → β)
    (hmap : ∀ a, F a ∈ T)
    (hmult : ∀ b ∈ T, ((univ : Finset (Fin s → α)).filter (fun a ↦ F a=b)).card ≤ L^s) :
    2^s ≤ T.card := by
  classical
  have hcount : ((univ : Finset (Fin s → α))).card ≤ L^s*T.card := by
    apply card_le_mul_card_image_of_maps_to (f := F) (t := T)
      (fun a _ ↦ hmap a) (L^s)
    exact hmult
  simp only [card_univ, Fintype.card_fun, Fintype.card_fin] at hcount
  have hlow : 2^s*L^s ≤ (Fintype.card α)^s := by
    rw [← mul_pow]
    exact Nat.pow_le_pow_left hseed s
  have he : 2^s*L^s ≤ T.card*L^s := by
    simpa only [mul_comm (L^s) T.card] using hlow.trans hcount
  exact (mul_le_mul_iff_left₀ (pow_pos hL s)).mp he

/-- Abstract many-input transfer. The output multiplicities and the height
bound are explicit hypotheses; varying the arity does not establish them. -/
theorem peaks_of_many_input_formulas {α : Type*} [Fintype α]
    {β : Type*} [DecidableEq β]
    (r : ℕ → ℕ) (A C D L : ℕ) (hA : 0 < A) (hL : 0 < L)
    (hseed : 2*L ≤ Fintype.card α)
    (N : ℕ → ℕ) (T : ℕ → Finset β) (F : (s : ℕ) → (Fin s → α) → β)
    (hheight : ∀ s, N s ≤ A^(C*s+D))
    (hmap : ∀ s a, F s a ∈ T s)
    (hmult : ∀ s b, b ∈ T s →
      ((univ : Finset (Fin s → α)).filter (fun a ↦ F s a=b)).card ≤ L^s)
    (hcard : ∀ s, (T s).card ≤ r (N s)) :
    {n : ℕ | (n : ℝ)^((1 : ℝ)/(2*(A*(C+1)))) < (r n : ℝ)}.Infinite := by
  apply peaks_of_exponential_witnesses r A C D hA
  intro M
  refine ⟨M,N M,le_rfl,hheight M,?_⟩
  exact (many_input_card_lower M L hL hseed (T M) (F M) (hmap M) (hmult M)).trans (hcard M)

end Erdos322Research.VariableArityPeakTransfer
