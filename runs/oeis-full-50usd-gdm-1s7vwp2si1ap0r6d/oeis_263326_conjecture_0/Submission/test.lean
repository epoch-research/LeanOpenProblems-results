import FormalConjectures.Util.ProblemImports

open Nat Rat Finset

set_option linter.unusedVariables false


noncomputable def S (n k s : ℕ) : ℚ :=
  Finset.sum (Nat.divisors n) fun d : ℕ => (d.cast + k.cast)⁻¹ ^ s.cast






set_option maxRecDepth 2000000

theorem S_five_val : S 5 31 1 = 17 / 288 := by
  unfold S
  have hdiv : Nat.divisors 5 = {1, 5} := by rfl
  rw [hdiv]
  have hnot : 1 ∉ ({5} : Finset ℕ) := by decide
  rw [Finset.sum_insert hnot]
  rw [Finset.sum_singleton]
  norm_num

theorem S_1829_val : S 1829 31 1 = 17 / 288 := by
  unfold S
  have hdiv : Nat.divisors 1829 = {1, 31, 59, 1829} := by rfl
  rw [hdiv]
  have hnot1 : 1 ∉ ({31, 59, 1829} : Finset ℕ) := by decide
  rw [Finset.sum_insert hnot1]
  have hnot2 : 31 ∉ ({59, 1829} : Finset ℕ) := by decide
  rw [Finset.sum_insert hnot2]
  have hnot3 : 59 ∉ ({1829} : Finset ℕ) := by decide
  rw [Finset.sum_insert hnot3]
  rw [Finset.sum_singleton]
  norm_num

theorem oeis_263326_conjecture_0.disproof :
  ¬ (∀ (k s : ℕ) (hk : k > 0) (hs : s > 0),
    (∀ n : ℕ, n > 0 → Int.fract (S n k s) ≠ 0) ∧
    (∀ n₁ n₂ : ℕ, n₁ > 0 → n₂ > 0 → n₁ ≠ n₂ →
      Int.fract (S n₁ k s) ≠ Int.fract (S n₂ k s))) := by
  intro h
  have h_inst := h 31 1 (by decide) (by decide)
  have h_distinct := h_inst.2
  have h_not_eq := h_distinct 1829 5 (by decide) (by decide) (by decide)
  have heq : Int.fract (S 1829 31 1) = Int.fract (S 5 31 1) := by
    rw [S_1829_val, S_five_val]
  exact h_not_eq heq








theorem S_one (k s : ℕ) : S 1 k s = (1 + k.cast : ℚ)⁻¹ ^ s := by
  unfold S
  have hdiv : Nat.divisors 1 = {1} := by rfl
  rw [hdiv]
  rw [Finset.sum_singleton]
  simp

lemma S_one_pos (k s : ℕ) (hk : k > 0) (_hs : s > 0) : S 1 k s > 0 := by
  rw [S_one]
  have h1 : (1 + (k : ℚ)) > 0 := by positivity
  have h2 : (1 + (k : ℚ))⁻¹ > 0 := by positivity
  positivity

lemma S_one_lt_one (k s : ℕ) (hk : k > 0) (hs : s > 0) : S 1 k s < 1 := by
  rw [S_one]
  have h1 : (1 + (k : ℚ)) > 1 := by
    have : (k : ℚ) > 0 := by positivity
    linarith
  have h2 : (1 + (k : ℚ))⁻¹ < 1 := inv_lt_one_of_one_lt₀ h1
  have h3 : 0 ≤ (1 + (k : ℚ))⁻¹ := by positivity
  exact pow_lt_one₀ h3 h2 hs.ne'

lemma S_one_fract_ne_zero (k s : ℕ) (hk : k > 0) (hs : s > 0) : Int.fract (S 1 k s) ≠ 0 := by
  have hpos := S_one_pos k s hk hs
  have hlt := S_one_lt_one k s hk hs
  rw [Int.fract_ne_zero_iff]
  intro ⟨z, hz⟩
  rw [← hz] at hpos hlt
  norm_cast at hpos hlt
  omega







#check padicValRat
#check padicValNat
#check Padic


#print axioms oeis_263326_conjecture_0.disproof
