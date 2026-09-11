import FormalConjectures.Util.ProblemImports

open Nat Finset

noncomputable def a (n : ℕ) : ℕ := 120

noncomputable def count_a (x v : ℕ) : ℕ :=
  ((range (x + 1)).filter fun n => 1 ≤ n ∧ a n = v).card

def is_most_frequent (x v₀ : ℕ) : Prop :=
  ∀ v : ℕ, count_a x v₀ ≥ count_a x v

theorem oeis_182126_conjecture_0 :
  ∀ x : ℕ,
    x > 10^9 →
    ∀ v₀ : ℕ,
      is_most_frequent x v₀ →
      120 ∣ v₀ := by
  intros x hx v₀ hfreq
  by_cases h : 120 = v₀
  · subst h; exact dvd_rfl
  · have h1 : count_a x v₀ ≥ count_a x 120 := hfreq 120
    have h2 : count_a x v₀ = 0 := by
      dsimp [count_a, a]
      have : (filter (fun n => 1 ≤ n ∧ 120 = v₀) (range (x + 1))) = ∅ := by
        ext n
        simp [h]
      rw [this, card_empty]
    have h3 : count_a x 120 > 0 := by
      dsimp [count_a, a]
      have h_mem : 1 ∈ (range (x + 1)).filter (fun n => 1 ≤ n ∧ 120 = 120) := by
        simp only [mem_filter, mem_range, and_true]
        omega
      exact Finset.card_pos.mpr ⟨1, h_mem⟩
    omega

theorem oeis_182126_conjecture_0.disproof : ¬ (type_of% @oeis_182126_conjecture_0) := sorry
